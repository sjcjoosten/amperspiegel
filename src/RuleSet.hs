{-# OPTIONS_GHC -Wall #-} {-# LANGUAGE RankNTypes, TypeFamilies, RankNTypes, BangPatterns, LambdaCase, ApplicativeDo, OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveTraversable, FlexibleInstances, FlexibleContexts #-}
module RuleSet(oldNewSystem,prePostRuleSet,applySystem,ruleSetRelations,Rule(..),Expression(..)) where
import Helpers
import qualified Data.Map as Map

ruleSetRelations :: IsString x => [x]
ruleSetRelations
 = ["rule","eFst","eSnd","pre","post","during","conjunct","compose","converse"]


prePostRuleSet :: forall m v z y. (Applicative m, IsString y, Ord y, Ord v)
                     => (forall x. m x)
                     -> (v -> m z)
                     -> TripleStore y v
                     -> m [Rule (TransactionVariable z) v]
prePostRuleSet fl transAtom ts
 = traverse makeRule [t | (_,t_list) <- getRel ts "rule", t<-t_list]
 where
   pre  = fmap (ExprAtom . TransactionPre) . transAtom
   post = fmap (ExprAtom . TransactionPre) . transAtom
   duri = fmap (ExprAtom . TransactionPre) . transAtom
   makeRule v = uncurry Subset <$> makeTuple v
   makeTuple v
    = (,) <$> (forOne fl ts "eFst" v makeExpression)
          <*> (forOne fl ts "eSnd" v makeExpression)
   makeExpression v
    = forOneOrNone fl ts "conjunct" v (fmap (uncurry Conjunction) . makeTuple) $
      forOneOrNone fl ts "compose"  v (fmap (uncurry Compose    ) . makeTuple) $
      forOneOrNone fl ts "converse" v (fmap Flp . makeExpression) $
      forOneOrNone fl ts "pre"    v pre  $
      forOneOrNone fl ts "post"   v post $
      forOneOrNone fl ts "during" v duri $
      pure I

oldNewSystem :: (Ord a, Ord b, Monad m) =>
                      (forall v. m v)
                      -> m b
                      -> [Rule (TransactionVariable a) b]
                      -> [Triple a b]
                      -> m (TripleStore a b, Map b b)
oldNewSystem fl fg rls tps
 = first (filterBy getPost) <$> applySystem fl fg rls (map (mapRel TransactionPre) tps)

applySystem :: forall a b m sys r.
 (sys~(r, Map b b, [Triple a b]),r~TripleStore a b,Ord b,Ord a, Monad m)
 => m sys -- ^ Failure upon inserting in expression
 -> m b -- ^ Fresh variable generator
 -> [Rule a b] -> [Triple a b] -> m (r, Map b b)
applySystem fl fg allRules originalTriples
 = process =<< (makeNewSystem allRules)
 where
  relevant v = findInMap v relevantMap ++ iRules
  -- rules with just I on lhs are always relevant, but never included in relevantMap
  iRules = [rl | rl@(Subset I _) <- allRules]
  
  makeNewSystem :: [Rule a b] -> m sys
  makeNewSystem [] = pure (mempty,mempty,originalTriples)
  makeNewSystem (Subset a b:ruls)
   = Helpers.foldr insertInExprM (makeNewSystem ruls) (makeSys a)
   where makeSys :: Expression b a -> [(b, b)]
         makeSys (Conjunction a1 a2) = [a' | a' <- makeSys a1, b' <- makeSys a2, a' == b']
         makeSys (Compose a1 a2) = [(c,d) | (c,v) <- makeSys a1, (v',d) <- makeSys a2, v == v']
         makeSys (Flp a1) = [(c,d) | (d,c) <- makeSys a1]
         makeSys (Pair c d) = [(c,d)]
         makeSys Bot = []
         makeSys I = []
         makeSys (ExprAtom _) = []
         insertInExprM v w = insertInExpr fl fg b v =<< w
  relevantMap :: Map a [Rule a b]
  relevantMap
   = (fromListWith (++) [(a,[rl]) | rl<-allRules
                                      , a<-Helpers.toList (lhs rl)])
  lkp a = findWithDefault a a
  lkpF v m = let newv=lkp v m
             in if v == newv then (newv,m) else
                let (r,m2) = lkpF newv (insert v r m)
                in (r,m2)
  
  process :: sys -> m (r, Map b b)
  process (v,rename,[])
   = pure$ ( fmap (\(a,b) -> (rm a, rm b)) (Map.difference v rename), rename)
   where rm = fmap (flip difference (Map.keysSet rename))
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

insertInExpr :: (Ord a, Ord b, Monad m, sys~(TripleStore a b, Map b b, [Triple a b]))
             => m sys -> m b -> Expression b a -> (b, b) -> sys -> m sys
insertInExpr fl fg = insertInExpr'
 where
  insertInExpr' I (b1',b2') sys@(mps,m,trs)
   = if b1' == b2' then pure sys else -- ignore b2 from now on, use b1 instead
     pure (mps,insert b2 b1 m,trs++new1++new2) -- it could be safe to do the new things first (they are tuples that were essentially already there, but just require renaming, so they shouldn't introduce much new stuff)
   where (b1,b2) = if b1' < b2' then (b1',b2') else (b2',b1')
         (m1,m2) = findInMap b2 mps
         new1 = [Triple a b1 v | (a,s) <- Map.toList m1, v<-toList s]
         new2 = [Triple a v b1 | (a,s) <- Map.toList m2, v<-toList s]
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

instance Functor (Rule r) where
   fmap f (Subset lf rt) = Subset (fmapE lf) (fmapE rt)
     where fmapE (ExprAtom r) = ExprAtom r
           fmapE I = I
           fmapE (Conjunction a b) = Conjunction (fmapE a) (fmapE b)
           fmapE (Compose a b) = Compose (fmapE a) (fmapE b)
           fmapE (Flp x) = Flp (fmapE x)
           fmapE (Bot) = Bot
           fmapE (Pair a b) = Pair (f a) (f b)

-- inside out lookup
getNewTuples :: (Ord a, Ord b)
             => Triple a b -> TripleStore a b -> Expression b a -> [(b, b)]
getNewTuples (Triple a b1' b2') revLk = replace1
 where
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

checkIfExists :: (Ord a, Ord b) => TripleStore a b -> (b, b) -> Expression b a -> Bool
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

findIn :: (Ord a, Ord b) => TripleStore a b -> Bool -> b -> Expression b a -> [b]
findIn _     _ b I                = [b]
findIn _     True  b (Pair a1 a2) = if a1 == b then [a2] else []
findIn _     False b (Pair a1 a2) = if a2 == b then [a1] else []
findIn _ _ _ Bot                  = []
findIn revLk ltr b (Flp e)        = findIn revLk (not ltr) b e
findIn revLk ltr b (Conjunction e1 e2)
 = [v | v <- findIn revLk ltr b e1
      , checkIfExists revLk (if ltr then (b,v) else (v,b)) e2]
findIn revLk True b (Compose e1 e2)
 = mconcat [findIn revLk True  v e2 | v <- findIn revLk True  b e1]
findIn revLk False b (Compose e1 e2)
 = mconcat [findIn revLk False v e1 | v <- findIn revLk False b e2]
findIn revLk True  b (ExprAtom a) = forEachOf revLk a b
findIn revLk False b (ExprAtom a) = lkpRight  revLk a b

