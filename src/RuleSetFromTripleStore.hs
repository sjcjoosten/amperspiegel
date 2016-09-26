{-# OPTIONS_GHC -Wall #-} {-# LANGUAGE TypeFamilies, BangPatterns, LambdaCase, ApplicativeDo, OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveTraversable, FlexibleInstances, FlexibleContexts #-}
module RuleSetFromTripleStore (tripleStoreToRuleSet,ruleSetRelations) where
import Relations
import Data.String
import Control.Monad.Fail
import SimpleHelperMonads

ruleSetRelations :: IsString x => [x]
ruleSetRelations
 = ["rule","eFst","eSnd","atom","conjunct","compose","converse"]

tripleStoreToRuleSet :: forall z v m y r.
                       ( MonadFail m
                       , IsString y -- TODO: ask for IsString (m y), to allow for relation lookups/disambiguation
                       , Show y
                       , FullRelLookup r
                       , RelType r ~ y
                       , AtomType r ~ v)
                    => (v -> m z) -> r -> m [Rule z v]
tripleStoreToRuleSet transAtom ts
 = traverse makeRule [pure t | (_,t_list) <- getRel ts "rule", t<-t_list]
 where
   makeRule :: m v -> m (Rule z v)
   makeRule v = uncurry Subset <$> makeTuple v
   makeTuple :: m v -> m (Expression v z,Expression v z)
   makeTuple v
    = (,) <$> (makeExpression (forOne "eFst" ts "eFst" v))
          <*> (makeExpression (forOne "eSnd" ts "eSnd" v))
   makeExpression :: m v -> m (Expression v z)
   makeExpression v
    = forOneOrNone ts "atom"     v ((\x -> ExprAtom <$> (transAtom =<< x))) $
      forOneOrNone ts "conjunct" v (fmap (uncurry Conjunction) . makeTuple) $
      forOneOrNone ts "compose"  v (fmap (uncurry Compose    ) . makeTuple) $
      forOneOrNone ts "converse" v (fmap Flp . makeExpression) $
      pure I
