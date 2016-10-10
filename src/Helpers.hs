{-# OPTIONS_GHC -Wall #-} {-# LANGUAGE TypeFamilies,BangPatterns, LambdaCase, ApplicativeDo, OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveTraversable, FlexibleInstances, FlexibleContexts #-}
module Helpers (Rule(..),(↦),(∋),Expression(..),RelInsert(..),TripleStore,Triple(..)
 ,getNewTuples,checkIfExists,findInMap,RelLookup(..), fmapE
 ,restrictTo, unionTS,showT,forOne,forOneOrNone
 ,twords,tlength,tnull,ifThenJust
 ,module Data.Monoid,module Data.Map,module Control.Arrow,module Data.Char,module Data.Text.Lazy.IO,module Control.Applicative,module Data.Text.Lazy, module System.Environment, module Control.Monad.State,module Fail, module Control.Monad.Fix, module Data.Foldable, module Data.String, module Data.Maybe
 ,Set) where
import Control.Monad.Fail as Fail
import Control.Applicative
import Control.Monad
import Control.Monad.Fix
import Data.Monoid
import Data.Foldable
import Data.String (IsString(..))
import Data.Maybe
import Data.Map (Map,fromListWith,findWithDefault,insert,keys,keysSet,insertWith)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.Environment
import Control.Monad.State hiding (fail)
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

ifThenJust :: (a -> Bool) -> a -> Maybe a
ifThenJust f v = case f v of {True -> Just v;False -> Nothing}

class RelLookup r where
  type RelType r
  type AtomType r
  forEachOf :: r -> RelType r -> AtomType r -> [AtomType r]
  lkpLeft  :: r -> RelType r -> AtomType r -> [AtomType r]
  lkpLeft = forEachOf
  lkpRight :: r -> RelType r -> AtomType r -> [AtomType r]
  getAtom :: AtomType r -> r -- get both, for all relations
          -> ([(RelType r,[AtomType r])] -- outgoing relations
             ,[(RelType r,[AtomType r])])-- incoming relations
  getRel :: r -> RelType r -> [(AtomType r,[AtomType r])]
class (RelLookup r, Monoid r) => RelInsert r where
  insertTriple :: Triple (RelType r) (AtomType r) -> r -> (r,Bool) -- insert into the triple store and return whether the new triple store is different
  removeAtoms :: r -> Map (AtomType r) b -> r

type TripleStore a b = (Map b (Map a (Set b), Map a (Set b)))
data Triple r a = Triple{relation::r, t_fst::a, t_snd::a} deriving Functor
data Rule r a = Subset{lhs::Expression a r,rhs::Expression a r}
data Expression a r
 = ExprAtom r
 | I
 | Conjunction (Expression a r) (Expression a r)
 | Compose (Expression a r) (Expression a r)
 | Flp (Expression a r)
 | Bot
 | Pair a a
 deriving (Functor,Foldable,Traversable)

restrictTo :: (Ord k) => [k] -> TripleStore k b -> TripleStore k b
restrictTo rs'
 = fmap (d2$flip Map.intersection rs)
 where rs = Map.fromList [(r,()) | r<-rs']
       d2 f (x,y) = (f x,f y)
unionTS :: (Ord k,Ord b)=> TripleStore k b -> TripleStore k b -> TripleStore k b
unionTS = Map.unionWith (d2 (Map.unionWith Set.union))
 where d2 f (x1,y1) (x2,y2) = (f x1 x2,f y1 y2)


instance Functor (Rule r) where
   fmap f (Subset l r) = Subset (fmapE f l) (fmapE f r)

fmapE :: (t -> a) -> Expression t r -> Expression a r
fmapE _ (ExprAtom r) = ExprAtom r
fmapE _ (I) = I
fmapE f (Conjunction a b) = Conjunction (fmapE f a) (fmapE f b)
fmapE f (Compose a b) = Compose (fmapE f a) (fmapE f b)
fmapE f (Flp x) = Flp (fmapE f x)
fmapE _ (Bot) = Bot
fmapE f (Pair a b) = Pair (f a) (f b)
 
instance (Ord a,Ord b) => RelLookup (TripleStore a b) where
  type RelType (TripleStore a b) = a
  type AtomType (TripleStore a b) = b
  forEachOf r a b = Set.toList . findInMap a . fst . findInMap b $ r
  lkpRight r a b = Set.toList . findInMap a . snd . findInMap b $ r
  getAtom b r = (listify m1,listify m2)
    where (m1,m2) = findInMap b r
          listify m = Map.toList (fmap Set.toList m)
  getRel mps r = [ (v1,Set.toList resSet)
                 | (v1,(v1Pairs,_)) <- Map.toList mps
                 , let resSet = findInMap r v1Pairs
                 , not (Set.null resSet)]

instance (Ord a,Ord b) => RelInsert (TripleStore a b) where
  insertTriple (Triple rel' a' b') revLk
    = addRv True (a',rel',b') (addRv False (b',rel',a') (revLk,True))
    where 
      addRv _ _ (mp,False) = (mp,False) -- no change needed
      addRv firstNotSecond (a,rel,b) (mp,True) -- TODO: use lenses, but check which approach is faster! (Requires benchmarks)
       = ( if change then insert a newPair mp else mp -- TODO: check whether this if-then-else is actually faster then just leaving the Map.insert
         , change
         )
       where mapElem,newElem :: Map a (Set b)
             mapPair,newPair :: (Map a (Set b), Map a (Set b))
             mapPair = findInMap a mp
             (mapElem,newPair)
              = if firstNotSecond then (fst mapPair, (newElem,snd mapPair))
                                  else (snd mapPair, (fst mapPair,newElem))
             newElem = insert rel newSet mapElem
             relSet = findInMap rel mapElem
             change = not (Set.member b relSet)
             newSet = Set.insert b relSet
  removeAtoms x y = fmap (\(a,b) -> (rm a, rm b)) (Map.difference x y)
     where rm = fmap (flip Set.difference (Map.keysSet y))

-- inside out lookup
getNewTuples :: forall a b r. (Eq a,Eq b,RelLookup r, a ~ RelType r, b ~ AtomType r)
             => Triple a b -> r -> Expression b a -> [(b,b)]
getNewTuples (Triple a b1' b2') revLk = replace1
 where
   replace1 :: Expression b a -> [(b,b)]
   replace1 (ExprAtom a') = if a == a' then [(b1',b2')] else []
   replace1 I = [(b1',b1'),(b2',b2')]
   replace1 (Conjunction e1 e2)
    = [e1' | e1' <- replace1 e1,checkIfExists revLk e1' e2] ++
      [e2' | e2' <- replace1 e2,checkIfExists revLk e2' e1]
   replace1 (Compose e1 e2)
    = [(b1,b3) | (b1,b2) <- replace1 e1,b3 <- findIn revLk True b2 e2] ++
      [(b1,b3) | (b2,b3) <- replace1 e2,b1 <- findIn revLk False b2 e1]
   replace1 (Flp e)
    = [(b2,b1) | (b1,b2) <- replace1 e]
   replace1 Bot = []
   replace1 (Pair _ _) = []

checkIfExists :: (Eq b, RelLookup r, a ~ RelType r, b ~ AtomType r)
              => r -> (b, b) -> Expression b a -> Bool
-- first several lines are redundant, but give more efficient lookup
checkIfExists _ (b1,b2) I            = b1 == b2
checkIfExists revLk (b1,b2) (Flp e)  = checkIfExists revLk (b2,b1) e
checkIfExists _ _ Bot                = False
checkIfExists _ (b1,b2) (Pair a1 a2) = b1 == a1 && b2 == a2
checkIfExists revLk bs (Conjunction e1 e2)
 = checkIfExists revLk bs e1 && checkIfExists revLk bs e2
checkIfExists revLk (b1,b2) (Compose e1 e2)
 = or [checkIfExists revLk (v1,b2) e2 | v1 <- findIn revLk True b1 e1]
-- base case (can be used to catch all):
checkIfExists revLk (b1,b2) e
 = or [v == b2 | v <- findIn revLk True b1 e]

findIn :: (Eq b, RelLookup r, a ~ RelType r, b ~ AtomType r)
       => r -> Bool -> b -> Expression b a -> [b]
findIn _     _ b I                = [b]
findIn _     True  b (Pair a1 a2) = if a1 == b then [a2] else []
findIn _     False b (Pair a1 a2) = if a2 == b then [a1] else []
findIn _ _ _ Bot                  = []
findIn revLk ltr b (Flp e)        = findIn revLk (not ltr) b e
findIn revLk ltr b (Conjunction e1 e2)
 = [v | v <- findIn revLk ltr b e1
      , checkIfExists revLk (if ltr then (b,v) else (v,b)) e2 -- the tuple found must be in e2 too
      ]
findIn revLk True b (Compose e1 e2)
 = mconcat [findIn revLk True  v e2 | v <- findIn revLk True  b e1]
findIn revLk False b (Compose e1 e2)
 = mconcat [findIn revLk False v e1 | v <- findIn revLk False b e2]
findIn revLk True  b (ExprAtom a) = lkpLeft  revLk a b
findIn revLk False b (ExprAtom a) = lkpRight revLk a b

infixr 5 ↦, ∋
(∋) :: forall r a. r -> (a, a) -> Triple r a
(∋) rel (a,b) = Triple rel a b
(↦) :: forall a b. a -> b -> (a, b)
(↦) = (,)

showT :: Show a => a -> Text
showT = pack . show

forOne :: (RelLookup r, MonadFail f) => String -> r -> RelType r -> (AtomType r) -> f (AtomType r)
forOne s r a b = ((\case {[a']->pure a';_->Fail.fail ("Expecting one "++s)})
                 . forEachOf r a) b
forOneOrNone :: (RelLookup r, MonadFail f, Show(RelType r))
        => r -> RelType r -> AtomType r -> (AtomType r -> f b) -> f b -> f b
forOneOrNone r a b fOne bNone
 = case forEachOf r a b of
     [one] -> fOne one
     [] -> bNone
     lst -> Fail.fail ("Expecting one or none items in "++show a++", got "++show (Prelude.length lst))

