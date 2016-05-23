{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module SimpleHelperMonads where
import Control.Monad.Fail as Fail
import Control.Applicative
import Control.Monad
import Relations

newtype FreshnessGenerator a = FreshnessGenerator {runFg::(Int -> (Int,a))} 

instance Show y => (Show (FreshnessGenerator y)) where
  show f = show (snd (runFg f 0))
instance Monad FreshnessGenerator where
  return x = FreshnessGenerator (\i -> (i,x))
  (FreshnessGenerator a) >>= f
    = FreshnessGenerator (\i -> let (i',a') = a i
                                    (FreshnessGenerator f') = f a'
                                in seq i' $ f' i')
instance Applicative FreshnessGenerator where
  pure = return
  (<*>) = ap
instance Functor FreshnessGenerator where
  fmap f x = pure f <*> x

data FailingMonad a = Failure {runFailure::String} | Result {runFailingMonad::a} deriving (Functor,Foldable,Traversable)
instance Applicative FailingMonad where
  (<*>) = ap
  pure = Result
instance Monad FailingMonad where
  (>>=) (Failure x) _ = Failure x
  (>>=) (Result a) f = f a
instance MonadFail FailingMonad where
  fail = Failure
instance Alternative FailingMonad where
  empty = Failure "Empty failure"
  (<|>) (Failure _) b = b
  (<|>) (Result a) _ = Result a

forOne :: (RelLookup r, MonadFail f)
       => r -> RelType r -> f (AtomType r) -> f (AtomType r)
forOne r a b = (isOne . forEachOf r a) =<< b
forNone :: (RelLookup r, MonadFail f)
        => r -> RelType r -> AtomType r -> f ()
forNone r a b = isNone $ forEachOf r a b
forOneOrNone :: (RelLookup r, MonadFail f, Show(RelType r))
        => r -> RelType r -> f (AtomType r) -> (f (AtomType r) -> f b) -> f b -> f b
forOneOrNone r a b' fOne bNone
 = do b <- b'
      case forEachOf r a b of
         [one] -> fOne (pure one)
         [] -> bNone
         lst -> Fail.fail ("Expecting one or none items in "++show a++", got "++show (Prelude.length lst))

isOne :: MonadFail f => [a] -> f a
isOne [a] = pure a
isOne lst = Fail.fail ("Expecting one, got "++show (Prelude.length lst))
isNone :: MonadFail f => [a] -> f ()
isNone [] = pure ()
isNone lst = Fail.fail ("Expecting none, got "++show (Prelude.length lst))
isOneOrNone :: MonadFail f => String -> a -> [a] -> f a
isOneOrNone _ _ [a] = pure a
isOneOrNone _ deflt [] = pure deflt
isOneOrNone s _ lst = Fail.fail ("Expecting at most one "++s++", got "++show (Prelude.length lst))
