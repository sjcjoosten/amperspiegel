{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TypeFamilies, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
module Relations(Rule(..),(⨟),(⊆),(∩),Expression(..),RelInsert(..),RelTwoWayLookup(..),TripleStore,Triple(..),getNewTuples,checkIfExists,findInMap,RelLookup(..),FullRelLookup(..)) where
import Data.Map as Map
import Data.Set as Set
import Data.String


findInMap :: (Monoid a, Ord k) => k -> Map k a -> a
findInMap itm mp = Map.findWithDefault mempty itm mp

instance Show r => Show (Rule r) where
  show (Subset l r) = show l++" ⊆ "++show r
instance Show r => Show (Expression r) where
  show (ExprAtom r) = show r
  show (I) = "I"
  show (Compose e1 e2) = "("++show e1++"⨟"++show e2++")"
  show (Conjunction e1 e2) = "("++show e1++"∩"++show e2++")"
  show (Flp e1) = "Flp "++show e1

infixl 6 ∩
infix 4 ⊆
infixl 8 ⨟
(⊆) :: Expression r -> Expression r -> Rule r
(⊆) a b = Subset a b

-- note: ⨾ sign is U+2A3E, Z NOTATION RELATIONAL COMPOSITION (and not the identically-looking U+2A1F)
(⨟),(∩) :: Expression r -> Expression r -> Expression r
(⨟) = Compose
(∩) = Conjunction

instance IsString x => IsString (Expression x) where
  fromString = ExprAtom . fromString

class RelLookup r where
  type RelType r
  type AtomType r
  forEachOf :: r -> RelType r -> AtomType r -> [AtomType r]
class RelLookup r => RelTwoWayLookup r where
  lkpLeft  :: r -> RelType r -> AtomType r -> [AtomType r]
  lkpLeft = forEachOf
  lkpRight :: r -> RelType r -> AtomType r -> [AtomType r]
  getAtom :: AtomType r -> r -- get both, for all relations
          -> ([(RelType r,[AtomType r])] -- outgoing relations
             ,[(RelType r,[AtomType r])] -- incoming relations
             )
class RelLookup r => FullRelLookup r where
  getRel :: r -> RelType r -> [(AtomType r,[AtomType r])]
class (RelLookup r, Monoid r) => RelInsert r where
  insertTriple :: Triple (RelType r) (AtomType r) -> r -> (r,Bool) -- insert into the triple store and return whether the new triple store is different
  removeAtoms :: r -> Map (AtomType r) b -> r

type TripleStore a b = (Map b (Map a (Set b), Map a (Set b)))
data Triple r a = Triple{relation::r, t_fst::a, t_snd::a} deriving Functor
data Rule r = Subset{lhs::Expression r,rhs::Expression r} deriving Functor
data Expression r
 = ExprAtom r
 | I
 | Conjunction (Expression r) (Expression r)
 | Compose (Expression r) (Expression r)
 | Flp (Expression r)
 deriving (Functor,Foldable,Traversable)
 
instance (Ord a,Ord b) => RelLookup (TripleStore a b) where
  type RelType (TripleStore a b) = a
  type AtomType (TripleStore a b) = b
  forEachOf r a b = Set.toList . Map.findWithDefault mempty a . fst . Map.findWithDefault mempty b $ r
instance (Ord a,Ord b) => FullRelLookup (TripleStore a b) where
  getRel mps r = [ (v1,Set.toList resSet)
                 | (v1,(v1Pairs,_)) <- Map.toList mps
                 , let resSet = Map.findWithDefault mempty r v1Pairs
                 , not (Set.null resSet)]
instance (Ord a,Ord b) => RelTwoWayLookup (TripleStore a b) where
  lkpRight r a b = Set.toList . Map.findWithDefault mempty a . snd . Map.findWithDefault mempty b $ r
  getAtom b r = (listify m1,listify m2)
    where (m1,m2) = findInMap b r
          listify m = Map.toList (fmap Set.toList m)
instance (Ord a,Ord b) => RelInsert (TripleStore a b) where
  insertTriple (Triple rel' a' b') revLk
    = addRv True (a',rel',b') (addRv False (b',rel',a') (revLk,True))
    where 
      addRv :: Bool
            -> (b,a,b)
            -> (TripleStore a b, Bool)
            -> (TripleStore a b, Bool)
      addRv _ _ (mp,False) = (mp,False) -- no change needed
      addRv firstNotSecond (a,rel,b) (mp,True) -- TODO: use lenses, but check which approach is faster! (Requires benchmarks)
       = ( if change then Map.insert a newPair mp else mp -- TODO: check whether this if-then-else is actually faster then just leaving the Map.insert
         , change
         )
       where mapElem,newElem :: Map a (Set b)
             mapPair,newPair :: (Map a (Set b), Map a (Set b))
             mapPair = findInMap a mp
             (mapElem,newPair)
              = if firstNotSecond then (fst mapPair, (newElem,snd mapPair))
                                  else (snd mapPair, (fst mapPair,newElem))
             newElem = Map.insert rel newSet mapElem
             relSet = findInMap rel mapElem
             change = not (Set.member b relSet)
             newSet = Set.insert b relSet
  removeAtoms = Map.difference

getNewTuples :: forall a b r. (Eq a,Eq b,RelTwoWayLookup r, a ~ RelType r, b ~ AtomType r)
             => Triple a b -> r -> Expression a -> [(b,b)]
getNewTuples (Triple a b1' b2') revLk = replace1
 where
   replace1 :: Expression a -> [(b,b)]
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

checkIfExists :: (Eq b, RelTwoWayLookup r, a ~ RelType r, b ~ AtomType r)
              => r -> (b, b) -> Expression a -> Bool
-- first several lines are redundant, but give more efficient lookup
checkIfExists _ (b1,b2) I = b1 == b2
checkIfExists revLk bs (Conjunction e1 e2)
 = checkIfExists revLk bs e1 && checkIfExists revLk bs e2
checkIfExists revLk (b1,b2) (Compose e1 e2)
 = or [checkIfExists revLk (v1,b2) e2 | v1 <- findIn revLk True b1 e1]
checkIfExists revLk (b1,b2) (Flp e)
 = checkIfExists revLk (b2,b1) e
checkIfExists revLk (b1,b2) e
 = or [v == b2 | v <- findIn revLk True b1 e]
-- findIn l b e | trace ("Finding from "++show b++" in "++show e++" ("++show l++")") False = undefined 
findIn :: (Eq b, RelTwoWayLookup r, a ~ RelType r, b ~ AtomType r)
       => r -> Bool -> b -> Expression a -> [b]
findIn _     _ b I = [b]
findIn revLk ltr b (Flp e) = findIn revLk (not ltr) b e
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