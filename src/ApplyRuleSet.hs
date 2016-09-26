{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-} -- for the scanner position
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
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
            => (forall x. m x) -- fail
            -> m b -- generate fresh constant
            -> [Rule a b] -- set of rules
            -> [Triple a b] -- set of initial triples
            -> m ( r -- new triple set
                 , Map.Map b b -- atoms proven to be equivalent
                 )
applySystem fl fg allRules originalTriples
 = process =<< (makeNewSystem allRules)
 where
  relevant v = Map.findWithDefault [] v relevantMap ++ iRules
  -- rules with just I on lhs are always relevant, but never included in relevantMap
  iRules = [rl | rl@(Subset I _) <- allRules]
  
  makeNewSystem :: [Rule a b] -> m sys
  makeNewSystem [] = pure (mempty,mempty,originalTriples)
  makeNewSystem (Subset a b:ruls)
   = Data.Foldable.foldr insertInExprM (makeNewSystem ruls) (makeSys a)
   where makeSys (Conjunction a1 a2) = [a' | a' <- makeSys a1, b' <- makeSys a2, a' == b']
         makeSys (Compose a1 a2) = [(c,d) | (c,v) <- makeSys a1, (v',d) <- makeSys a2, v == v']
         makeSys (Flp a1) = [(c,d) | (d,c) <- makeSys a1]
         makeSys (Pair c d) = [(c,d)]
         makeSys Bot = []
         makeSys I = []
         makeSys (ExprAtom _) = []
         insertInExprM v w = insertInExpr fl fg b v =<< w
  relevantMap :: Map.Map a [Rule a b]
  relevantMap
   = (Map.fromListWith (++) [(a,[rl]) | rl<-allRules
                                      , a<-Data.Foldable.toList (lhs rl)])
  lkp a = Map.findWithDefault a a
  lkpF v m = let newv=lkp v m
             in if v == newv then (newv,m) else
                let (r,m2) = lkpF newv (Map.insert v r m)
                in (r,m2)

  process :: sys -> m (r, Map.Map b b)
  process (v,rename,[])
   = pure$ (removeAtoms v rename, rename)
  process (revLk', synonyms0, (Triple rel a' b'):rest)
   = if ud then process =<< foldrM (incrementRule tr) sys rules
           else process sys
   where 
     sys = (revLk,synonyms2,rest)
     (a,synonyms1) = lkpF a' synonyms0
     (b,synonyms2) = lkpF b' synonyms1
     tr = Triple rel a b
     rules = relevant rel
     (revLk,ud) = insertTriple tr revLk'
  incrementRule :: Triple a b
                -> Rule a b
                -> sys
                -> m sys
  incrementRule tr rl sys@(revLk, m, _)
   = foldrM (insertInExpr fl fg to) sys tuples
     where tuples = (getNewTuples tr revLk from)
           (Subset from to) = fmap (fst . flip lkpF m) rl -- TODO: this is  inefficient, and it really only has to be done after a rename
  -- getNewTuples:
  -- consider a triple tr: (b1,b2) in r,
  -- consider the expression e: r;r
  -- (getNewTuples tr e) will return tuples in (b1,b2);r and r;(b1,b2)
insertInExpr :: forall b a r sys m.
               (Monad m, Ord b
               ,(r, Map b b, [Triple a b]) ~ sys
               ,a ~ RelType r
               ,b ~ AtomType r
               ,RelTwoWayLookup r)
             => (forall x. m x) -- fail
             -> m b -- generate fresh constant
             -> Expression b a 
             -> (b, b) 
             -> sys
             -> m sys
insertInExpr fl fg = insertInExpr'
 where
  insertInExpr' I (b1',b2') sys@(mps,m,trs)
   = if b1' == b2' then pure sys else -- ignore b2 from now on, use b1 instead
     pure (mps,Map.insert b2 b1 m,trs++new1++new2) -- it could be safe to do the new things first (they are tuples that were essentially already there, but just require renaming, so they shouldn't introduce much new stuff)
   where (b1,b2) = if b1' < b2' then (b1',b2') else (b2',b1')
         (m1,m2) = getAtom b2 mps
         new1 = [Triple a b1 v | (a,s) <- m1, v<-s]
         new2 = [Triple a v b1 | (a,s) <- m2, v<-s]
  insertInExpr' (ExprAtom a) (b1,b2) (mps,m,trs)
   = pure (mps,m,trs++[Triple a b1 b2]) -- see Note[insertInExpr' ExprAtom]
  insertInExpr' (Flp e) (b1,b2) sys = insertInExpr' e (b2,b1) sys
  insertInExpr' (Conjunction e1 e2) bs sys
   = insertInExpr' e1 bs =<< (insertInExpr' e2 bs sys)
  insertInExpr' e bs sys@(revLk,_,_) | checkIfExists revLk bs e = pure sys
  insertInExpr' (Compose e1 e2) (b1,b2) sys
   = do new <- fg
        sys1 <- insertInExpr' e1 (b1,new) sys
        sys2 <- insertInExpr' e2 (new,b2) sys1
        return sys2
  insertInExpr' Bot _ _ = fl
  insertInExpr' (Pair a1 a2) (b1,b2) sys
   = insertInExpr' I (a1,b1) =<< (insertInExpr' I (a2,b2) sys)
