{-# OPTIONS_GHC -Wall #-} {-# LANGUAGE RankNTypes, TypeFamilies, BangPatterns, LambdaCase, ApplicativeDo, OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveTraversable, FlexibleInstances, FlexibleContexts #-}
module Helpers ((↦),(∋),TripleStore,Triple(..),findInMap,forEachOf,lkpRight,insertTriple
 ,restrictTo, unionTS,showT,forOne,forOneOrNone,getRel
 ,twords,tlength,tnull,ifThenJust,filterBy,mapRel,getPost,findSelfMap
 ,module Control.Monad.Identity,module Data.Monoid,module Data.Map,module Control.Arrow,module Data.Char,module Data.Text.Lazy.IO,module Control.Applicative,module Data.Text.Lazy, module System.Environment, module Control.Monad.State,module Control.Monad.Fix, module Data.Foldable, module Data.String, module Data.Maybe
 ,TransactionVariable(..),Set,difference) where
import Control.Applicative
import Control.Monad.Fix
import Data.Monoid
import Data.Foldable
import Data.String (IsString(..))
import Data.Maybe
import Data.Map (Map,fromListWith,findWithDefault,insert,keys,keysSet,insertWith)
import Data.Set (Set,difference)
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.Environment
import Control.Monad.State hiding (fail)
import Control.Monad.Identity hiding (fail)
import Data.Text.Lazy (Text,pack,unpack,intercalate,split,unlines,take,drop,break,splitAt,lines,head,tail,span,snoc,dropEnd,isSuffixOf,isPrefixOf,stripPrefix)
import Data.Text.Lazy.IO
import Data.Text.Lazy as Text (length,null,words)
import Data.Char (readLitChar,isAlphaNum,isSpace)
import Control.Arrow (first)

tnull :: Text -> Bool
tnull = Text.null
tlength :: Text -> Int
tlength = fromIntegral . Text.length
twords :: Text -> [Text]
twords = Text.words

findInMap :: (Monoid a, Ord k) => k -> Map k a -> a
findInMap = Map.findWithDefault mempty
findSelfMap :: (Ord k) => Map k k -> k -> k
findSelfMap mp x = Map.findWithDefault x x mp

ifThenJust :: (a -> Bool) -> a -> Maybe a
ifThenJust f v = case f v of {True -> Just v;False -> Nothing}

-- | forEachOf r a b gets all pairs from the relation a that have b as source
forEachOf,lkpRight :: (Ord b, Ord a) => TripleStore a b -> a -> b -> [b]
forEachOf r a b = Set.toList . findInMap a . fst . findInMap b $ r

-- | As with forEachOf, but for the reversed relation
lkpRight r a b = Set.toList . findInMap a . snd . findInMap b $ r

-- | Get all tuples in a relation from a triplestore.
-- | The list in the second part of the tuple is guaranteed to be non-empty
getRel :: (Ord v, Ord y) => TripleStore y v -> y -> [(v, [v])]
getRel mps r = [ (v1,Set.toList resSet)
               | (v1,(v1Pairs,_)) <- Map.toList mps
               , let resSet = findInMap r v1Pairs
               , not (Set.null resSet)]

-- | Insert a triple in a TripleStore
-- | Returns whether or not it was already present
insertTriple :: (Ord a, Ord b)
             => Triple a b -> TripleStore a b -> (TripleStore a b, Bool)
insertTriple (Triple rel' a' b') revLk
  = addRv True (a',rel',b') (addRv False (b',rel',a') (revLk,True))
  where 
    addRv _ _ (mp,False) = (mp,False) -- no change needed
    addRv firstNotSecond (a,rel,b) (mp,True) -- TODO: use lenses, but check which approach is faster! (Requires benchmarks)
     = ( if change then insert a newPair mp else mp -- TODO: check whether this if-then-else is actually faster then just leaving the Map.insert
       , change
       )
     where mapPair = findInMap a mp
           (mapElem,newPair)
            = if firstNotSecond then (fst mapPair, (newElem,snd mapPair))
                                else (snd mapPair, (fst mapPair,newElem))
           newElem = insert rel newSet mapElem
           relSet = findInMap rel mapElem
           change = not (Set.member b relSet)
           newSet = Set.insert b relSet

type TripleStore a b = (Map b (Map a (Set b), Map a (Set b)))
data Triple r a = Triple{relation::r, t_fst::a, t_snd::a} deriving Functor

data TransactionVariable x =
     TransactionPre x | TransactionDuring x | TransactionPost x
     deriving (Functor, Traversable, Foldable, Eq, Ord)

getPost :: TransactionVariable a -> Maybe a
getPost (TransactionPost v) = Just v
getPost _ = Nothing

mapRel :: forall r a t. (t -> r) -> Triple t a -> Triple r a
mapRel f (Triple r a b) = Triple (f r) a b

restrictTo :: (Ord k) => [k] -> TripleStore k b -> TripleStore k b
restrictTo rs'
 = fmap (d2$flip Map.intersection rs)
 where rs = Map.fromList [(r,()) | r<-rs']
       d2 f (x,y) = (f x,f y)
filterBy :: Eq v => (k -> Maybe v) -- must be weakly monotonic (= preserve order)
         -> TripleStore k b -> TripleStore v b
filterBy rs
 = fmap (d2 (\m -> Map.fromAscList [(v,b) | (k,b)<-Map.toAscList m, Just v <- [rs k]]))
 where d2 f (x,y) = (f x,f y)
unionTS :: (Ord k,Ord b)=> TripleStore k b -> TripleStore k b -> TripleStore k b
unionTS = Map.unionWith (d2 (Map.unionWith Set.union))
 where d2 f (x1,y1) (x2,y2) = (f x1 x2,f y1 y2)

infixr 5 ↦, ∋
(∋) :: forall r a. r -> (a, a) -> Triple r a
(∋) rel (a,b) = Triple rel a b
(↦) :: forall a b. a -> b -> (a, b)
(↦) = (,)

showT :: Show a => a -> Text
showT = pack . show

forOne :: (Ord a, Ord t) => c -> TripleStore a t -> a -> t -> (t -> c) -> c
forOne fl r a b fOne = ((\case {[a']->fOne a';_->fl}) . forEachOf r a) b
forOneOrNone :: (Ord b, Ord a)
             => t -> TripleStore a b -> a -> b -> (b -> t) -> t -> t
forOneOrNone fl r a b fOne bNone
 = case forEachOf r a b of
     [one] -> fOne one
     [] -> bNone
     _ -> fl

