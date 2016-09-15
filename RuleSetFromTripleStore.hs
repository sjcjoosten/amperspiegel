{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module RuleSetFromTripleStore (tripleStoreToRuleSet) where
import Relations
import Data.String
import Control.Monad.Fail
import SimpleHelperMonads

tripleStoreToRuleSet :: forall z v m y r.
                       ( MonadFail m
                       , IsString y -- TODO: ask for IsString (m y), to allow for relation lookups/disambiguation
                       , Show y
                       , FullRelLookup r
                       , RelType r ~ y
                       , AtomType r ~ v)
                    => (v -> z) -> r -> m [Rule z v]
tripleStoreToRuleSet transAtom ts
 = traverse makeRule [(pure s,pure t) | (s,t_list) <- getRel ts "subset", t<-t_list]
 where
   makeRule :: (m v,m v) -> m (Rule z v)
   makeRule (s,t) = Subset <$> makeExpression s
                           <*> makeExpression t
   makeTuple :: m v -> m (Expression v z,Expression v z)
   makeTuple v
    = (,) <$> (makeExpression (forOne "fst" ts "fst" v))
          <*> (makeExpression (forOne "snd" ts "snd" v))
   makeExpression :: m v -> m (Expression v z)
   makeExpression v
    = forOneOrNone ts "atom"     v (fmap (ExprAtom . transAtom)) $
      forOneOrNone ts "conjunct" v (fmap (uncurry Conjunction) . makeTuple) $
      forOneOrNone ts "compose"  v (fmap (uncurry Compose    ) . makeTuple) $
      forOneOrNone ts "converse" v (fmap Flp . makeExpression) $
      pure I
