

data TripleStore rel atm res
 = TripleStore{ getRel :: rel -> [(atm,[atm])]
              , forEachOf :: rel -> atm -> [atm]
              , getAtom :: atm -> res
              }
-- TODO: experiment which of these is fastest:
   -- using vectors/arrays
   -- instead of returning an Int, return a datatype that has all the necessary links already there?
   -- instead of returning an Int, return the type "y" itself?
-- Note: instead of changing this implementation, it should be possible to have several implementations
makeTripleStore :: forall y x. (Ord y, Ord x)
                => [Triple x y]
                -> TripleStore x Int y
makeTripleStore trps
 = TripleStore{ getRel = getR
              , forEachOf = forE
              , getAtom = (IntMap.!) g
              }
 where
   getR r = [ (src,IntSet.toList tgt_set)
            | (src,tgt_set) <- IntMap.toList (getR' r)
            ]
   forE r a = IntSet.toList (IntMap.findWithDefault IntSet.empty a (getR' r))
   getR' :: x -> IntMap IntSet
   getR' r = Map.findWithDefault IntMap.empty r relLookup
   relLookup :: Map.Map x (IntMap IntSet)
   g :: IntMap y
   ((!g,_),!relLookup)
     = Data.Foldable.foldr extendMaps ((IntMap.empty,Map.empty),Map.empty) trps
   
   lookupOrInsert :: y -> (IntMap y, Map y Int) -> (Int, (IntMap y, Map y Int))
   lookupOrInsert a (rv,mp)
     = case Map.lookup a mp of
         Nothing -> let i = Map.size mp
                    in (i,(IntMap.insert i a rv,Map.insert a i mp))
         Just v -> (v,(rv,mp))
   
   extendMaps :: Triple x y
              -> ((IntMap y,Map y Int), Map.Map x (IntMap IntSet))
              -> ((IntMap y,Map y Int), Map.Map x (IntMap IntSet))
   extendMaps Triple{relation=r,t_fst=at1,t_snd=at2} (mp',relmp)
    = (nmp
      ,Map.insertWith (const addPair)
                      r (IntMap.singleton at1i singleAt2)
                      relmp
      )
    where
      (at1i,mp1) = lookupOrInsert at1 mp'
      (at2i,nmp) = lookupOrInsert at2 mp1
      singleAt2 = IntSet.singleton at2i
      {-# INLINE singleAt2 #-}
      addPair = IntMap.insertWith (const addAtm) at1i singleAt2
      addAtm = IntSet.insert at2i 
