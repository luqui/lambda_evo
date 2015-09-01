{-# LANGUAGE DeriveFunctor,
             DeriveFoldable,
             DeriveTraversable,
             GeneralizedNewtypeDeriving,
             LambdaCase #-}

import Prelude hiding (concat)

import Bound
import Control.Applicative
import Control.Arrow (first)
import Control.Monad (ap, join)
import Control.Monad.Trans
import Control.Monad.Trans.RWS
import Control.Monad.Trans.Maybe
import Data.Foldable
import Data.Maybe (fromJust)
import Data.Traversable
import Data.Void
import Prelude.Extras

import qualified Data.Map as Map
import qualified Control.Monad.Random as Rand

class (Functor m, Monad m) => MonadStep m where
  step :: m ()

-- TODO convert this to CPS for speed
newtype AbortT m a = AbortT { runAbortT :: MaybeT (RWST Int () Int m) a }
  deriving (Functor, Applicative, Monad)

instance (Functor m, Monad m) => MonadStep (AbortT m) where
  step = AbortT $ do
    limit <- lift ask
    cur <- lift get
    if cur < limit
      then lift . put $! cur+1
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
  let body' = instantiate (const (Var Nothing)) (Just <$> body)
  Lam . dBAbstract <$> normalize body'

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


---------------

type ScoreMap = Map.Map (Term Void) Double


