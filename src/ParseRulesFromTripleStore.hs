{-# OPTIONS_GHC -Wall #-} {-# LANGUAGE TypeFamilies, BangPatterns, LambdaCase, ApplicativeDo, OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveTraversable, FlexibleInstances, FlexibleContexts #-}
module ParseRulesFromTripleStore (ParseRule(..),ParseAtom(..),tripleStoreRelations,tripleStoreToParseRules,traverseStrings,fmap23) where
import Helpers

-- A grammar
data ParseRule a b refId = ParseRule refId [ParseAtom a b refId] deriving (Functor,Foldable,Traversable,Show)-- concatenation of strings
data ParseAtom a b refId = ParseString b | ParseRef a refId deriving (Functor,Foldable,Traversable)

{-
fmap12 :: Applicative m => (t1 -> m a) -> (t -> m b) -> ParseRule t1 t refId -> m (ParseRule a b refId)
fmap12 f1 f2 (ParseRule r lst) = ParseRule r <$> (traverse (fmap12' f1 f2) lst)
fmap12' :: Applicative m => (t1 -> m a) -> (t -> m b) -> ParseAtom t1 t refId -> m (ParseAtom a b refId)
fmap12' _ f2 (ParseString b) = ParseString <$> f2 b
fmap12' f1 _ (ParseRef a rid) = flip ParseRef rid <$> (f1 a)
fmap13 :: Applicative m => (t1 -> m a) -> (refId -> m b) -> ParseRule t1 t refId -> m (ParseRule a t b)
fmap13 f1 f3 (ParseRule r lst) = ParseRule <$> f3 r <*> traverse (fmap13' f1 f3) lst
fmap13' :: Applicative f => (t -> f a) -> (t1 -> f refId) -> ParseAtom t b t1 -> f (ParseAtom a b refId)
fmap13' _ _ (ParseString b) = pure (ParseString b)
fmap13' f1 f3 (ParseRef a rid) = ParseRef <$> f1 a <*> f3 rid -}
fmap23 :: Applicative m => (t -> m a) -> (refId -> m b) -> ParseRule t1 t refId -> m (ParseRule t1 a b)
fmap23 f2 f3 (ParseRule r lst) = ParseRule <$> f3 r <*> traverse (fmap23' f2 f3) lst
fmap23' :: Functor f => (t -> f b) -> (t1 -> f refId) -> ParseAtom a t t1 -> f (ParseAtom a b refId)
fmap23' f2 _ (ParseString b) = ParseString <$> f2 b
fmap23' _ f3 (ParseRef a rid) = ParseRef a <$> f3 rid

instance (Show a,Show b,Show refId) => Show (ParseAtom a b refId) where
  show (ParseString b) = show b
  show (ParseRef a refId) = show a ++ " " ++ show refId

instance IsString b => IsString (ParseAtom a b c) where
  fromString = ParseString . fromString
instance ( string ~ String -- delay the conversion to a and force it to be a String here still, to avoid having to write a type: Ambiguous type variable ‘t0’ arising from the literal ‘"firstString"’ prevents the constraint ‘(IsString (t0 -> ParseAtom Text Text Text))’ from being solved
         , IsString a, IsString c)
      => IsString (string -> ParseAtom a b c) where
  fromString s = ParseRef (fromString s) . fromString
  
traverseStrings :: Applicative f => (a -> f b) -> ParseRule x a z -> f (ParseRule x b z)
traverseStrings f (ParseRule r lst)
 = ParseRule r <$> traverse (traverseString f) lst

traverseString :: Applicative f => (a -> f b) -> ParseAtom x a z -> f (ParseAtom x b z)
traverseString f (ParseString a) = ParseString <$> f a
traverseString _ (ParseRef x i) = pure (ParseRef x i)

tripleStoreRelations :: IsString x => [x]
tripleStoreRelations
 = [ "choice" -- :: ParseRule*Expansion
   , "continuation" -- :: Expansion*Expansion [UNI]
   , "recogniser" -- :: Expension*Element [UNI]
   , "nonTerminal" -- :: Reference*ParseRule [UNI,TOT]
   ]
   
-- tripleStoreToParseRules takes a triple store that describes a parser, and turns it into the set of parserules that can be turned into a parser by parseListOf or readListGrammar
-- Requires the following relations:
  -- choice :: ParseRule*Expansion
  -- continuation :: Expansion*Expansion [UNI]
  -- recogniser :: Expension*Element [UNI]
  -- nonTerminal :: Reference*ParseRule [UNI,TOT]
  -- Reference ISA Element, String ISA Element
-- Requirements are cardinality constraints plus:
  -- I[Element] = I[Reference] (+) I[String]
  -- where (+) denotes the disjoint sum
-- The atom 'Statement' is returned as the thing to be parsed.
-- For [ParseRule x y z], we have: x ~ Reference, y ~ String, z ~ ParseRule
-- It makes sense for a list to satisfy the following (not-required):
--  recogniser;V = continuation;V[Expansion*ONE]
-- Totality of nonTerminal is used as a test between x and y.
  -- Consequently, anything other than x which may be an ELEMENT will be treated as an y.
  -- Additionally, anything used to describe the final relation (i.e. anything in x) will not be usable as an y.
  -- In other words: it is your own responsibility that the intersection of x and y is empty. This is why we require I[Element] = I[Reference] (+) I[String]
-- TODO: write this function in an &-INTERFACE-like syntax
tripleStoreToParseRules :: forall z v m y r.
                       ( MonadFail m, Alternative m -- TODO: get rid of these and make functions like isOne, isNone and orElse such that they can be translated into preconditions on the TripleStore... Demanding 'Applicative' is enough if we do this
                       , IsString y -- TODO: ask for IsString (m y), to allow for relation lookups/disambiguation
                       , RelLookup r
                       , RelType r ~ y
                       , AtomType r ~ v)
                    => (v -> z) -> r -> m [ParseRule z z z]
tripleStoreToParseRules transAtom ts
 = do r<-fA "choice" makeParseRule
      return r
 where
   fA :: y -> ((v,v) -> m (ParseRule z z z)) -> m [ParseRule z z z]
   fA c f = traversePair f (getRel ts c)
   traversePair :: ((v, v)    -> m (ParseRule z z z))
                -> [(v, [v])] -> m [ParseRule z z z]
   traversePair _ [] = pure []
   traversePair f ((src',tgts):as) = (++) <$> sequenceA [f (src', tgt') | tgt'<-tgts] <*> traversePair f as
   fE :: y -> v -> (v -> m a) -> m [a]
   fE r a f = traverse f (forEachOf ts r a)
   showInternal :: v -> m z
   showInternal = pure . transAtom
   makeParseRule :: (v, v) -> m (ParseRule z z z)
   makeParseRule (s,t) = ParseRule <$> (showInternal s)
                                   <*> (makeListOf makeAtom t)
   makeListOf :: (v -> m a) -> v -> m [a]
   makeListOf head_fn cl
        = ($) <$> (isOneOrNone "recogniser" id =<< fE "recogniser" cl (fmap (:) . head_fn))
              <*> (isOneOrNone "continuation" [] =<< fE "continuation" cl (makeListOf head_fn))
   makeAtom :: v -> m (ParseAtom z z z)
   makeAtom atm
        = (const <$> (ParseString <$> showInternal atm)
                 <*> (isNone "non-terminal" =<< fE "nonTerminal" atm showInternal)) <|>
          (ParseRef <$> showInternal atm
                    <*> (isOne "non-terminal, relations names should be unique" =<< fE "nonTerminal" atm showInternal))
