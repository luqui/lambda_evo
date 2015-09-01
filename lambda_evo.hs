{-# LANGUAGE DeriveFunctor,
             DeriveFoldable,
             DeriveTraversable,
             GeneralizedNewtypeDeriving,
             LambdaCase,
             ScopedTypeVariables,
             TupleSections #-}

import Prelude hiding (concat, mapM_)

import Bound
import Control.Applicative
import Control.Arrow (first, (>>>))
import Control.Monad (ap, guard, join)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.Foldable
import Data.Functor.Identity
import Data.List (sortBy)
import Data.Maybe (catMaybes, fromJust)
import Data.Ord (comparing)
import Data.Traversable
import Data.Void
import Prelude.Extras

import qualified Control.Monad.Random as Rand
import qualified Control.Monad.Trans.State as State
import qualified Control.Monad.Trans.RWS as RWS
import qualified Data.Map as Map
import qualified Text.Printf as Printf

class (Functor m, Monad m) => MonadStep m where
  step :: m ()

-- TODO convert this to CPS for speed
newtype AbortT m a = AbortT (MaybeT (RWS.RWST Int () Int m) a)
  deriving (Functor, Applicative, Monad)

runAbortT :: (Functor m, Monad m) => Int -> AbortT m a -> m (Maybe a)
runAbortT limit (AbortT m) = fst <$> RWS.evalRWST (runMaybeT m) limit 0

runAbort :: Int -> AbortT Identity a -> Maybe a
runAbort limit m = runIdentity (runAbortT limit m)

instance (Functor m, Monad m) => MonadStep (AbortT m) where
  step = AbortT $ do
    limit <- lift RWS.ask
    cur <- lift RWS.get
    if cur < limit
      then lift . RWS.put $! cur+1
      else empty

newtype DoesntAbortT m a = DoesntAbortT { runDoesntAbortT :: m a }
  deriving (Functor, Applicative, Monad)

instance (Functor m, Monad m) => MonadStep (DoesntAbortT m) where
  step = return ()

---------------

data Term a = Var a | Term a :@ Term a | Lam (Scope () Term a)
  deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

instance Monad Term where
  return = Var
  Var x >>= f = f x
  (x :@ y) >>= f = (x >>= f) :@ (y >>= f)
  Lam e >>= f = Lam (e >>>= f)

instance Eq1 Term
instance Ord1 Term
instance Show1 Term
instance Read1 Term
instance Applicative Term where
  pure = Var
  (<*>) = ap

lam :: Eq a => a -> Term a -> Term a
lam v b = Lam (abstract1 v b)

dBInstantiate :: Scope () Term a -> Term (Maybe a)
dBInstantiate = instantiate (const (Var Nothing)) . fmap Just

dBAbstract :: Term (Maybe a) -> Scope () Term a
dBAbstract = fromJust . sequenceA . abstract (\case Nothing -> Just (); Just _ -> Nothing)

normalize :: (MonadStep m) => Term a -> m (Term a)
normalize (Var v) = return (Var v)
normalize (a :@ b) = do
  a' <- normalize a
  case a' of
    Lam body -> do
      step
      normalize (instantiate1 b body)
    other -> (other :@) <$> normalize b
normalize (Lam body) = do
  let body' = dBInstantiate body
  Lam . dBAbstract <$> normalize body'

subterms :: Term a -> [Term a]
subterms (Var x) = []
subterms (t :@ u) = [t,u] ++ subterms t ++ subterms u
subterms (Lam body) = catMaybes (map sequenceA (subterms (dBInstantiate body)))

type Cloud = Rand.Rand Rand.StdGen

genTerm :: [(Cloud a, Rational)] -> Int -> Cloud (Term a)
genTerm genVar size = join . Rand.fromList . concat $ [
    [ (genLam, χ (null genVar || size > 0)) ],
    [ (genApp, χ (size > 0)) ],
    (map.first.fmap) Var genVar
  ]
  where
  genLam = Lam . dBAbstract <$> genTerm ((return Nothing, 1) : subVar) (size-1)
    where
    subVar = (map.first.fmap) Just genVar
  genApp = do
    (l,r) <- splitSize (size-1)
    liftA2 (:@) (genTerm genVar l) (genTerm genVar r)

  splitSize size = do
    leftR <- Rand.getRandomR (0,size)
    return (leftR, size-leftR)
  χ True = 1
  χ False = 0

data NameDB a = Name String | Up a
instance (Show a) => Show (NameDB a) where
  show (Name s) = s
  show (Up a) = show a

showTerm :: (Show a) => Term a -> String
showTerm = \t -> State.evalState (go False False t) (tail varNames)
  where
  go :: (Show a) => Bool -> Bool -> Term a -> State.State [String] String
  go ap lp (Var x) = return $ show x
  go ap lp (t :@ u) = do
    t' <- go False True t
    u' <- go True True u
    return $ parens ap (t' ++ " " ++ u')
  go ap lp (Lam body) = do
    (name:names) <- State.get
    State.put names
    let body' = instantiate (const (Var (Name name))) . fmap Up $ body
    bodyShow <- go False False body'
    return $ parens lp ("\\" ++ name ++ ". " ++ bodyShow)

  varNames = [] : liftA2 (\x y -> x ++ [y]) varNames ['a'..'z']

  parens True = ("(" ++) . (++ ")")
  parens False = id

---------------

-- Let value :: Term -> R be the value judgment function for _closed_ terms.
-- Then we shall define
--
-- value t = sum { ?? value(normalize u) | t is a subterm of u }
--
-- subject to some condition ?? which allows the sum to converge.
--
-- Imagine that we have some term `t`.  The term `I t` has the same normal
-- form as `t`, but has `I` as a subterm, so `I` would gain some value from it.
-- But `I` is adding nothing.  Can we make it so that `I` does not gain?

_LIMIT_ = 500
_STEPSIZE_ = 0.01
_TERMSIZE_ = 50

normalize' :: Term a -> Maybe (Term a)
normalize' = runAbort _LIMIT_ . normalize

deltas :: Term Void -> Maybe (Term Void, [(Double, Term Void)])
deltas t = do
  normT <- normalize' t
  let subs = catMaybes (normalize' <$> subterms normT)
  let scale = 1 / fromIntegral (length subs)
  guard $ not (null subs)
  return (normT, (-1, normT) : map (scale,) subs)

genFlow :: forall a. (Ord a) => Cloud a -> (a -> Maybe (a, [(Double, a)]))
                             -> Cloud [Map.Map a Double]
genFlow genA f = iterateM (step _STEPSIZE_) Map.empty
  where
  step :: Double -> Map.Map a Double -> Cloud (Map.Map a Double)
  step dt m0 = do
    a <- genA
    return $ case f a of
      Nothing -> m0
      Just (a', dels) ->
        --let weight = Map.findWithDefault 1 a' m0 in
        let weight = 1 in
        foldl' (\m (δ,x) -> Map.insertWith (+) x (dt*weight*δ) m) m0 dels

iterateM :: (Functor m, Monad m) => (a -> m a) -> a -> m [a]
iterateM f x0 = (x0:) <$> (iterateM f =<< f x0)

------------

displayFlowState :: (Show a) => Map.Map (Term a) Double -> String
displayFlowState = id
  >>> Map.assocs
  >>> sortBy (comparing (negate.snd))
  >>> map (\(t,r) -> Printf.printf "%+.3f" r ++ "\t" ++ showTerm t)
  >>> unlines

showPrompt :: String -> IO ()
showPrompt s = putStrLn s >> return ()

main :: IO ()
main = do
  gen <- Rand.newStdGen
  let flow = genFlow (genTerm [] _TERMSIZE_) deltas
  let flowValues = Rand.evalRand flow gen
  mapM_ (showPrompt.displayFlowState) flowValues
