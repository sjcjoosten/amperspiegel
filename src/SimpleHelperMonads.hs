{-# OPTIONS_GHC -Wall #-} {-# LANGUAGE BangPatterns, LambdaCase, ApplicativeDo, OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveTraversable, FlexibleInstances, FlexibleContexts #-}
module SimpleHelperMonads where
import Control.Monad.Fail as Fail
import Control.Applicative
import Control.Monad
import Relations

data FailingMonad a = Failure {runFailure::String} | Result {runFailingMonad::a}
  deriving (Functor,Foldable,Traversable,Show)
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
       => String -> r -> RelType r -> f (AtomType r) -> f (AtomType r)
forOne s r a b = (isOne s . forEachOf r a) =<< b
forNone :: (RelLookup r, MonadFail f)
        => String -> r -> RelType r -> AtomType r -> f ()
forNone s r a b = isNone s $ forEachOf r a b
forOneOrNone :: (RelLookup r, MonadFail f, Show(RelType r))
        => r -> RelType r -> f (AtomType r) -> (f (AtomType r) -> f b) -> f b -> f b
forOneOrNone r a b' fOne bNone
 = do b <- b'
      case forEachOf r a b of
         [one] -> fOne (pure one)
         [] -> bNone
         lst -> Fail.fail ("Expecting one or none items in "++show a++", got "++show (Prelude.length lst))

isOne :: MonadFail f => String -> [a] -> f a
isOne _ [a] = pure a
isOne s lst = Fail.fail ("Expecting one "++s++", got "++show (Prelude.length lst))
isNone :: MonadFail f => String -> [a] -> f ()
isNone _ [] = pure ()
isNone s lst = Fail.fail ("Expecting no "++s++", got "++show (Prelude.length lst))
isOneOrNone :: MonadFail f => String -> a -> [a] -> f a
isOneOrNone _ _ [a] = pure a
isOneOrNone _ deflt [] = pure deflt
isOneOrNone s _ lst = Fail.fail ("Expecting at most one "++s++", got "++show (Prelude.length lst))
