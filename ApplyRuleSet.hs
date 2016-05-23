{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-} -- for the scanner position
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module ApplyRuleSet(applySystem) where
import Data.Foldable
import Relations
import Data.Map as Map

applySystem :: forall m a b r sys.
               (Monad m, Ord a, Ord b
               ,sys ~ (r, Map.Map b b, [Triple a b])
               ,a ~ RelType r
               ,b ~ AtomType r
               ,RelTwoWayLookup r, RelInsert r)
            => m b -- generate fresh constant
            -> [Rule a] -- set of rules
            -> [Triple a b] -- set of initial triples
            -> m r
applySystem fg allRules originalTriples
 = incrementTriple (mempty,mempty,originalTriples)
 where
  relevant v = Map.findWithDefault [] v relevantMap ++ iRules
  -- rules with I on lhs are always relevant, but never included in relevantMap
  iRules = [rl | rl@(Subset I _) <- allRules]
  relevantMap :: Map.Map a [Rule a]
  relevantMap
   = (Map.fromListWith (++) [(a,[rl]) | rl<-allRules
                                      , a<-Data.Foldable.toList (lhs rl)])
  lkp a = Map.findWithDefault a a
  lkpF v m = let newv=lkp v m
             in if v == newv then (newv,m) else
                let (r,m2) = lkpF newv (Map.insert v r m)
                in (r,m2)

  incrementTriple :: sys
                  -> m r
  incrementTriple (v,rename,[])
   = pure$ removeAtoms v rename
  incrementTriple (revLk', synonyms0,(Triple rel a' b'):rest)
   = if ud then incrementTriple =<< foldrM (incrementRule tr) sys rules
           else incrementTriple sys
   where 
     sys = (revLk,synonyms2,rest)
     (a,synonyms1) = lkpF a' synonyms0
     (b,synonyms2) = lkpF b' synonyms1
     tr = Triple rel a b
     rules = relevant rel
     (revLk,ud) = insertTriple tr revLk'
  incrementRule :: Triple a b
                -> Rule a
                -> sys
                -> m sys
  incrementRule tr (Subset from to) sys@(revLk, _, _)
   = -- trace ("Adding "++show tr++" ==> Triggers: "++show r++" ("++show tuples++")")$
     foldrM (insertInExpr to) sys tuples
     where tuples = (getNewTuples tr revLk from)
  -- getNewTuples:
  -- consider a triple tr: (b1,b2) in r,
  -- consider the expression e: r;r
  -- (getNewTuples tr e) will return tuples in (b1,b2);r and r;(b1,b2)
  insertInExpr :: Expression a 
               -> (b, b) 
               -> sys
               -> m sys
  -- insertInExpr e b _ | trace ("Insert into "++show e++" ==> "++show b) False = undefined
  insertInExpr I (b1',b2') sys@(mps,m,trs)
   = if b1' == b2' then pure sys else -- ignore b2 from now on, use b1 instead
     pure (mps,Map.insert b2 b1 m,new1++new2++trs) -- it could be safe to do the new things first (they are tuples that were essentially already there, but just require renaming, so they shouldn't introduce much new stuff)
   where (b1,b2) = if b1'<b2' then (b1',b2') else (b2',b1')
         (m1,m2) = getAtom b2 mps
         new1 = [Triple a b1 v | (a,s) <- m1, v<-s]
         new2 = [Triple a v b1 | (a,s) <- m2, v<-s]
  insertInExpr (ExprAtom a) (b1,b2) (mps,m,trs)
   = pure (mps,m,trs++[Triple a b1 b2]) -- see Note[InsertInExpr ExprAtom]
  insertInExpr (Flp e) (b1,b2) sys = insertInExpr e (b2,b1) sys
  insertInExpr (Conjunction e1 e2) bs sys
   = insertInExpr e1 bs =<< (insertInExpr e2 bs sys)
  insertInExpr e bs sys@(revLk,_,_) | checkIfExists revLk bs e = pure sys
  insertInExpr (Compose e1 e2) (b1,b2) sys
   = do new <- fg
        sys1 <- insertInExpr e1 (b1,new) sys
        sys2 <- insertInExpr e2 (new,b2) sys1
        return sys2

-- note InsertInExpr ExprAtom:
-- depending on the order in which we execute rules, we may end up with a terminating or a non-terminating system.
-- The choice here is based on the following example:
-- ["s" ⊆ "n" ⨟ "p", "p" ⨟ (Flp "s" ⨟ "n") ⊆ I, "p" ⊆ "s"]
-- Start the system by inserting anything in s.
-- The observation is that the "⊆ I" rule does not fire until there are two fresh variables.
-- If we treat new triples first, we will end up iterating inserting stuff into "s", "n" and "p" via the first and the last rule without applying the second rule
-- Hence we start with the oldest triples, and delay the treatment of fresh triples as long as possible
