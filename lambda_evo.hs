{-# LANGUAGE DeriveFunctor,
             DeriveFoldable,
             DeriveTraversable,
             GeneralizedNewtypeDeriving,
             LambdaCase,
             ScopedTypeVariables,
             TupleSections #-}

import Prelude hiding (concat, mapM_, sum)

import Bound
import Control.Applicative
import Control.Arrow (first, second, (>>>))
import Control.Monad (ap, guard, join, replicateM)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.Foldable
import Data.Functor.Identity
import Data.List (sortBy)
import Data.Maybe (catMaybes, fromJust)
import Data.Monoid
import Data.Ord (comparing)
import Data.Traversable
import Data.Void
import GHC.Conc (numCapabilities)
import Prelude.Extras

import qualified Control.Monad.Random as Rand
import qualified Control.Monad.Trans.State as State
import qualified Control.Monad.Trans.RWS as RWS
import qualified Control.Parallel.Strategies as Parallel
import qualified Data.Map.Strict as Map
import qualified Data.MemoCombinators as Memo
import qualified Text.Printf as Printf

newtype LimitT m a = LimitT (RWS.RWST Int Any Int m a)
  deriving (Functor, Applicative, Monad)

runLimitT :: (Functor m, Monad m) => Int -> LimitT m a -> m (a, Bool)
runLimitT limit (LimitT m) = second getAny <$> RWS.evalRWST m limit 0

runLimit :: Int -> LimitT Identity a -> (a, Bool)
runLimit limit m = runIdentity (runLimitT limit m)

step :: (Monad m) => a -> LimitT m a -> LimitT m a
step def (LimitT comp) = LimitT $ do
  steps <- RWS.get
  limit <- RWS.ask
  if steps < limit
    then do
      RWS.put $! steps+1
      comp
    else do
      RWS.tell $ Any True
      return def

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

normalize :: (Functor m, Monad m) => Term a -> LimitT m (Term a)
normalize (Var v) = return (Var v)
normalize (a :@ b) = do
  a' <- normalize a
  case a' of
    Lam body -> step (a' :@ b) (normalize (instantiate1 b body))
    other -> (other :@) <$> normalize b
normalize (Lam body) = do
  let body' = dBInstantiate body
  Lam . dBAbstract <$> normalize body'

closedSubterms :: Term a -> [Term a]
closedSubterms (Var x) = []
closedSubterms (t :@ u) = checkClosed t ++ checkClosed u
closedSubterms (Lam body) = catMaybes (map sequenceA (closedSubterms (dBInstantiate body)))

checkClosed :: Term a -> [Term a]
checkClosed t = maybe (closedSubterms t) (:[]) (traverse (const Nothing) t)

termSize :: (Num b) => Term a -> b
termSize (Var x) = 1
termSize (t :@ u) = 1 + termSize t + termSize u
termSize (Lam body) = 1 + termSize (dBInstantiate body)

type Cloud = Rand.Rand Rand.StdGen

genTerm :: [(Cloud a, Rational)] -> Int -> Cloud (Term a)
genTerm genVar size = join . Rand.fromList . concat $ [
    [ (genLam, χ (null genVar || size > 1)) ],
    [ (genApp, χ (size > 1)) ],
    if size <= 1 then (map.first.fmap) Var genVar else []
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

termsOfSize :: Integer -> Integer -> Integer
termsOfSize = Memo.memo2 Memo.integral Memo.integral go
  where
  go _ 0 = 0
  go vars 1 = vars
  go vars size =
    sum [ termsOfSize vars n * termsOfSize vars ((size-1)-n) | n <- [1..(size-1)-1] ] + -- apply
    termsOfSize (vars+1) (size-1)

normalTermsOfSize :: Integer -> Integer
normalTermsOfSize = withLambdas 0
  where
  withLambdas = Memo.memo2 Memo.integral Memo.integral go
    where
    go _ 0 = 0
    go vars 1 = vars
    go vars size = applies vars size + withLambdas (vars+1) (size-1)

  nonLambdas = Memo.memo2 Memo.integral Memo.integral go
    where
    go _ 0 = 0
    go vars 1 = vars
    go vars size = applies vars size

  applies vars size = sum [ nonLambdas vars n * withLambdas vars ((size-1)-n) | n <- [1..(size-1)-1] ]

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

_SIZE_LIMIT_ = 1000 :: Int
_REDUCTIONS_PER_SET_ = 10 :: Int
_SET_LIMIT_ = 100 :: Int
_STEP_SIZE_ = 0.01 :: Double 
_INITIAL_TERM_SIZE_ = 50 :: Int

normalize' :: Term a -> Maybe (Term a)
normalize' = go _SET_LIMIT_
  where
  go 0 _ = Nothing
  go sets t = case runSet t of
                (t', True) | termSize t' < _SIZE_LIMIT_ -> go (sets-1) t'
                           | otherwise -> Nothing
                (t', False) -> Just t'
  runSet = runLimit _REDUCTIONS_PER_SET_ . normalize

deltas :: Term Void -> Maybe (Term Void, [(Double, Term Void)])
deltas t = do
  normT <- normalize' t
  let tSize = termSize t
  let subs = [ (s,s') | s <- closedSubterms t, Just s' <- [normalize' s] ]
  let scale = 1 / fromIntegral (length subs)
  guard $ not (null subs)
  let dels = [ (termSize s/.tSize, s') | (s,s') <- subs ]
  return (normT, dels)
  where
  x /. y = fromIntegral x / fromIntegral y

genFlow :: forall a. 
  (Ord a) => Int -> Cloud a -> (a -> Maybe (a, [(Double, a)]))
          -> Cloud [Map.Map a Double]
genFlow threads genA f = iterateM (step _STEP_SIZE_) Map.empty
  where
  step :: Double -> Map.Map a Double -> Cloud (Map.Map a Double)
  step dt m0 = do
    ts <- replicateM threads genA
    let fts = Parallel.runEval (Parallel.parList Parallel.rseq (map f ts))
    return $! foldl' addDeltas m0 fts
    where
    addDeltas m0 ft = case ft of
      Nothing -> m0
      Just (t', dels) ->
        let weight = Map.findWithDefault 1 t' m0 in
        foldl' (\m (δ,x) -> accumDefault 1 (+ dt*weight*δ) x m) m0 dels

accumDefault :: (Ord k) => a -> (a -> a) -> k -> Map.Map k a -> Map.Map k a
accumDefault def mod = Map.alter $ \case
    Nothing -> Just (mod def)
    Just x  -> Just (mod x)

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

snipe :: Int -> [a] -> [a]
snipe n [] = []
snipe n (x:xs) = x `seq` (x : snipe n (drop (n-1) xs))

main :: IO ()
main = do
  let processors = max (numCapabilities-1) 1
  putStrLn $ "Using " ++ show processors ++ " processors"
  gen <- Rand.newStdGen
  let flow = genFlow processors (genTerm [] _INITIAL_TERM_SIZE_) deltas
  let flowValues = Rand.evalRand flow gen
  mapM_ (showPrompt.displayFlowState) . snipe (1260 `div` processors) $ flowValues

-- vim: sw=2 :
