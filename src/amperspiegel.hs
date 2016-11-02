{-# OPTIONS_GHC -Wall #-} {-# LANGUAGE BangPatterns, LambdaCase, ApplicativeDo, OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveTraversable, FlexibleInstances, FlexibleContexts #-}
module Main (main) where
import Helpers
import Data.Set as Set (toList)
import ParseRulesFromTripleStore(ParseRule(..),ParseAtom(..),tripleStoreToParseRules,fmap23)
import TokenAwareParser(Atom(..),freshTokenSt,parseText,deAtomize,deAtomizeString,freshenUp,parseListOf,runToken,Token,LinePos,showPos,builtIns,makeQuoted)
import RuleSet(oldNewSystem,prePostRuleSet,Rule(..),Expression(..))
import System.IO (stderr)
import System.Exit (exitFailure)
import System.Console.Terminal.Size (size,width)
import BaseState
import qualified Data.Map as Map

main :: IO ()
main = do as <- getChunks =<< getArgs
          evalStateT (forM_ as (uncurry doCommand))
                     (initialstate as)
       where getChunks' [] = ([],[])
             getChunks' (a:as)
               = let (res,spl) = getChunks' as
                 in case a of
                      ('-':cmd) -> ((pack cmd,spl):res,[])
                      _ -> (res,pack a:spl)
             getChunks as
               = case getChunks' as of
                   (r,[]) -> return r
                   (_,_ ) -> finishError "First argument should be a command, that is: it should start with '-'"

popFromLst :: [Triple (Atom Text) (Atom Text)] -> Population
popFromLst = TR . storeFromLst

storeFromLst :: [Triple (Atom Text) (Atom Text)] -> FullStore
storeFromLst = foldl' (\v w -> fst (insertTriple w v)) mempty

newtype Population
 = TR { getPop   :: FullStore}
type FullStore = TripleStore (Atom Text) (Atom Text)
type FullParser = [ParseRule (Atom Text) Text Text]
type FullRules = [Rule (TransactionVariable (Atom Text)) (Atom Text)]
type SpiegelState a = StateT (Map Text Population) IO a

doCommand :: Text -> [Text] -> SpiegelState ()
doCommand cmd
 = findWithDefault
       (\_ -> lift$ finishError ("Not a valid command: "<>cmd<>"\nGet a list of commands using: -h"))
       cmd lkp'
 where lkp' = fmap snd (fromListWith const commands)

showUnexpected :: Token (LinePos Text, Bool)
               -> Text -> Maybe Text
               -> Either Text x
showUnexpected tk expc mby
 = Left $ "Parse error, unexpected "<> (showPs tk)<>"\n  Expecting: "<> expc
     <> (case mby of {Nothing -> "";Just v ->"\n  mby(TODO: fix me into something more descriptive):"<> v})
 where showPs = showPos id . fst . runToken

parse :: (Monad m, IsString z, Ord z, Show z)
      => [ParseRule (Atom Text) Text z] -> Text
      -> SpiegelState (StateT Int m [Triple (Atom Text) (Atom Text)])
parse p = eitherError id . parseText id (parseListOf builtIns (p,"Statement")) showUnexpected

commands :: [ ( Text, ( Text, [Text] -> SpiegelState () ) ) ]
commands
 = [ ( "i"
     , ( "parse file as input"
       , (\files -> parseAsIn files)))
   , ( "h"
     , ( "display this help"
       , \_ -> liftIO (Helpers.putStrLn . helpText =<< size)))
   , ( "list"
     , ( "show a list of all triple-stores"
       , noArgs "list"$
           lift . sequenceA_ . map Helpers.putStrLn . keys
             =<< get
       ))
   , ( "show"
     , ( "display the triples as a list"
       , eachPop (lift . Helpers.putStrLn . prettyPPopulation)))
   , ( "showP"
     , ( "display the triples as a set of parse-rules"
       , eachDo (lift . Helpers.putStrLn . prettyPParser) getParser))
   , ( "showR"
     , ( "display the triples as a set of parse-rules"
       , eachDo (lift . Helpers.putStrLn . prettyPRules) getRules))
   , ( "showTS"
     , ( "display for populations generated with -collect"
       , eachDo (lift . Helpers.putStrLn . prettyPPopulations)
                (\v -> eitherError id . makePops =<< retrieve v)
       ))
   , ( "print"
     , ( "Print the second argument(s) using syntax of the first argument. Missing arguments default to \"population\". Prints to stdout"
       , \args ->
           let (synt,pops) = case args of
                 [] -> ("population",["population"])
                 [x] -> (x,["population"])
                 (x:xs) -> (x,xs)
           in do parser <- getParser synt
                 pop <- mconcat <$> mapM (fmap getList . retrieve) pops
                 printPop parser (popFromLst pop)
       )
     )
   , ( "count"
     , ( "count the number of triples"
       , eachPop (lift . Prelude.putStrLn . show . length . getList)))
   , ( "asParser"
     , ( "turn the population into the parser for -i"
       , noArgs "asParser" $
         do parser <- apply "asParser" ["population"]
            overwrite "parser" (TR parser)
            overwrite "population" (TR parser)))
   , ( "apply"
     , ( "apply the rule-system of first argument and put result into final argument (overwrite what was there). The remaining arguments form the population the system is applied to (or to the final argument if there are no remaining arguments given)."
       , \args ->
           let (rsys,from,targ) = case args of
                 [] -> ("population",["population"],"population")
                 [x] -> (x,[x],x)
                 (x:xs) -> (x,init xs,last xs)
           in overwrite targ . TR =<< apply rsys from
       ))
   , ( "collect"
     , ( "collect the current state of amperspiegel and put the result into the population"
       , oneArg "collect"
           (\arg -> overwrite arg . popFromLst . popsToPop =<< get)
       ))
   , ( "distribute"
     , ( "set the population as the current state of amperspiegel"
       , oneArg "distribute"
           (\arg -> put =<< eitherError id . makePops =<< retrieve arg)
       ))
   ]
 where
  parseAsIn files
   = do txts <- lift$ mapM (Helpers.readFile . unpack) files
        p <- getParser "parser"
        trps <- traverse (parse p) txts
        r <- getRules "parser"
        res <- unFresh (ruleConsequences r . mconcat =<< sequence trps)
        overwrite "population" (TR res)
        return ()
  pass f v = const v <$> f v
  printPop :: FullParser -> Population -> SpiegelState ()
  printPop pr (TR pop)
   = sequenceA_ [ (liftIO . traverse Helpers.putStrLn) =<< matchStart pa
                | pa <- findInMap "Statement" pm ]
   where
    -- parse map based on all parse rules (faster lookup)
    pm :: Map Text [[ParseAtom (Atom Text) Text Text]]
    pm = Map.fromListWith merge [(k,[v]) | ParseRule k v <-
      ParseRule "StringAndOrigin" [(ParseRef "string" "String")] : pr]
    merge [] l = l
    merge l [] = l
    merge o1@(h1:l1) o2@(h2:l2)
     = if numRefs h1 < numRefs h2 then h2 : merge o1 l2 else h1 : merge l1 o2
    numRefs lst = length [() | ParseRef _ _ <- lst]
    matchStart :: [ParseAtom (Atom Text) Text Text] -> SpiegelState [Text]
    matchStart [] = pure []
    matchStart (ParseString v:r) = map ((v<>" ")<>) <$> matchStart r
    matchStart (ParseRef rel cont:r)
     = sequence [ mappend . intercalate " " <$> sequence h <*> 
                   (intercalate " " <$> sequence r')
                | (k,v@(_:_))<-getRel pop rel
                -- we might want to make sure that (length v == 1)?
                -- otherwise, parsing back yields different source objects
                , Just h <- [traverse (printAs cont) v]
                , Just r' <- [traverse (match k) r]
                ]
    printAs :: Text -> Atom Text -> Maybe (SpiegelState Text)
    printAs cont v
     = if cont `elem` ["String", "QuotedString", "UnquotedString"]
       then -- Just . pure$ showT v
            Just$ eitherError (mappend "Not a String: ".showT) $ deAtomizeString v
       else pickBest -- print the first of all matching patterns
             [ sequence r
             | pa <- findInMap cont pm, Just r <- [traverse (match v) pa]]
    match :: Atom Text
          -> ParseAtom (Atom Text) Text Text
          -> Maybe (SpiegelState Text)
    match _ (ParseString v) = Just (pure v)
    -- maybe throw an error upon multiple
    match v (ParseRef rel cont)
     = case forEachOf pop rel v of
         [] -> Nothing -- no match
         lst -> (fmap (intercalate " match ") . sequence <$> traverse (printAs cont) lst)
    pickBest :: [SpiegelState [Text]] -> Maybe (SpiegelState Text)
    pickBest [] = Nothing
    pickBest (h:tl)
     = Just$ chooseBest (pickBest tl) =<< h
    chooseBest (Just v) [] = v
    chooseBest _ h = return (intercalate " " h)
  ruleConsequences :: forall x. MonadIO x
                   => FullRules
                   -> [Triple (Atom Text) (Atom Text)]
                   -> StateT Int x FullStore
  ruleConsequences r v
    = fst <$> (pass (liftIO . renameWarnings) =<<
          oldNewSystem (liftIO$finishError "Error occurred in applying rule-set: rules & data lead to an inconsistency.")
                       freshTokenSt r v)
  -- renameAndAdd v (v',n) = (storeFromLst . (map (fmap (findSelfMap n)) v <>) . getList . TR) v'
  apply :: Text -> [Text] -> SpiegelState FullStore
  apply rsys from
   = do pops <- mapM (fmap getList . retrieve) from
        let pop = mconcat <$> traverse (freshenUp freshTokenSt) pops
        r <- getRules rsys
        unFresh (ruleConsequences r =<< pop)
  noArgs :: Text -> SpiegelState () -> [t] -> SpiegelState ()
  noArgs s f
   = \case {[] -> f;_->lift$finishError (s <> " takes no arguments")}
  oneArg :: Text -> (Text -> SpiegelState ()) -> [Text] -> SpiegelState ()
  oneArg s f
   = \case [] -> f "population";
           [i] -> f i
           v->lift$finishError (s <> " takes one argument (given: "<>showT (length v)<>")")
  eachPop :: (Population -> SpiegelState ()) -> [Text] -> SpiegelState ()
  eachPop f = eachDo f retrieve
  eachDo :: (a -> SpiegelState ())
         -> (Text -> SpiegelState a)
         -> ([Text] -> SpiegelState ())
  eachDo f g = \case [] -> f =<< g "population"
                     l  -> mapM_ (\v -> f =<< g v) l
  renameWarnings (_,res)
   = sequenceA_ [ Helpers.hPutStrLn stderr ("Application of rules caused "<>showT v<>" to be equal to "<> showT r)
                | (v,r) <- Map.toList res
                , case v of {Fresh _ -> False; _ -> True}]
  helpText Nothing
   = mconcat [ s <> "\t" <> d <> "\n" | (s,(d,_)) <- commands ]
  helpText (Just wdw)
   = "These are the switches you can use: "<> "\n\n" <>
        mconcat [ pad maxw ("  " <> s) <> wrap 0 (twords d) <>"\n"
                | (s,(d,_)) <- commands]
   where
     maxw :: Int
     maxw = 3 + foldr max 0 (map (tlength . fst) commands)
     wrap _ [] = ""
     wrap cur (w:r)
      = case tlength w + 1 of
          v | cur + v > lim -> "\n " <> pad maxw "" <> w <> wrap v r
          v -> " "<>w<>wrap (cur + v) r
     lim = max 20 (width wdw - maxw)

unFresh :: Monad m => StateT Int m a -> m a
unFresh v = evalStateT v 0

makePops :: Population -> Either Text (Map Text Population)
makePops (TR ts)
 = fmap popFromLst . fromListWith (++) <$> traverse toTripList (getRel ts "contains")
 where asTriple :: Atom Text -> Either Text (Triple (Atom Text) (Atom Text))
       asTriple trp = Triple <$> forOne (Left "'relation' must be a function") ts "relation" trp pure
                             <*> forOne (Left "'source' must be a function")   ts "source"   trp pure
                             <*> forOne (Left "'target' must be a function")   ts "target"   trp pure
       toTripList :: (Atom Text, [Atom Text]) -> Either Text (Text, [(Triple (Atom Text) (Atom Text))])
       toTripList (p,tgt) = (,) <$> (case deAtomize p of {Left v -> Left (showT v);Right v -> Right v})
                                <*> traverse asTriple tgt

popsToPop :: Map Text Population -> [Triple (Atom Text) (Atom Text)]
popsToPop = concat . runIdentity . unFresh . traverse mkContains . Map.toList
  where mkContains (nm,p)
          = do tps <- freshenUp freshTokenSt (getList p)
               concat <$> (traverse (\(Triple n s t) ->
                                 (\fr -> [ Triple "contains" (makeQuoted nm) fr
                                         , Triple "relation" fr n
                                         , Triple "source" fr s
                                         , Triple "target" fr t
                                         ]) <$> freshTokenSt) tps)

prettyPParser :: FullParser -> Text
prettyPParser [] = ""
prettyPParser o@(ParseRule t _:_)
 = t <> " := " <>
   Helpers.intercalate ("\n  "<>pad (tlength t) ""<>"| ")
                       res <> "\n" <> prettyPParser tl
 where (res,tl) = mapsplit (\(ParseRule t' lst)
                            -> if t == t' then Just (pp lst) else Nothing) o
       pp = Helpers.intercalate ", " . map showT
       mapsplit _ [] = ([],[])
       mapsplit f o'@(a:r)
         = case f a of
             Just v -> let (rs,rm) = mapsplit f r in (v:rs,rm)
             Nothing -> ([],o')

prettyPRules :: FullRules -> Text
prettyPRules = mconcat . map (\v -> pRule v <> "\n")
  where pRule (Subset l r) = pExp l<>" |- "<>pExp r
        pExp (ExprAtom r) = showT r
        pExp I            = "I"
        pExp (Compose e1 e2) = "("<>pExp e1<>";"<>pExp e2<>")"
        pExp (Conjunction e1 e2) = "("<>pExp e1<>" /\\ "<>pExp e2<>")"
        pExp (Flp e1) = pExp e1<>"~"
        pExp Bot = "Bot"
        pExp (Pair a1 a2) = "< "<>showT a1<>" , "<>showT a2<>" >"

prettyPPopulation :: Population -> Text
prettyPPopulation v
 = Helpers.unlines [ showPad w1 n <> "\8715 "<>showPad w2 s<>" \8614 "<>showT t
                   | Triple n s t <- l]
 where (w1,w2) = foldr max2 (0,0) l
       l = getList v
       max2 (Triple a b _) (al,bl)
         = (max al (length (show a)), max bl (length (show b)))

prettyPPopulations :: (Map Text Population) -> Text
prettyPPopulations v
 = intercalate "\n  , "
     [ "( "<>showT k<>"\n    , [ " <> 
       intercalate "\n      , " [showT n <> " \8715 "<>showT s<>" \8614 "<>showT t
                                | Triple n s t <- getList p ] <> "\n      ])"
     | (k,p)<-Map.toList v]

showPad :: forall a. Show a => Int -> a -> Text
showPad w = pad w . showT

pad :: Int -> Text -> Text
pad w s
 = let x = w - (tlength) s
   in s <> pack (Prelude.take x (repeat ' '))

getList :: Population -> [Triple (Atom Text) (Atom Text)]
getList x = mconcat . map getTripls . Map.toList $ getPop x
  where getTripls (a,(mp,_))
          = [(Triple nm a b) | (nm,bs) <- Map.toList mp, b<-Set.toList bs]

overwrite :: Monad b => Text -> Population -> StateT (Map Text Population) b ()
overwrite s p = modify (insert s p)

retrieve :: Monad b => Text -> StateT (Map Text Population) b Population
retrieve s
 = do mp <- get
      return $ findWithDefault (popFromLst []) s mp

getParser :: Text -> SpiegelState FullParser
getParser s
 = do mp <- retrieve s
      unAtomize =<< tripleStoreToParseRules (liftIO$finishError "TripleStoreToParseRules could not make a parser out of the population") pure (getPop mp)
 where unAtomize :: [ParseRule (Atom Text) (Atom Text) (Atom Text)] -> SpiegelState FullParser
       unAtomize = traverse (eitherError (("error: "<>) . showT) . fmap23 deAtomize deAtomize)

eitherError ::(MonadIO m) => (t -> Text) -> Either t a -> m a
eitherError sh (Left a) = liftIO$finishError (sh a)
eitherError _ (Right a) = pure a

getRules :: Text -> SpiegelState FullRules
getRules s
 = do mp <- retrieve s
      prePostRuleSet (liftIO$finishError "tripleStoreToRuleSet could not make a set of rules out of the population") pure (getPop mp)
    
finishError :: Text -> IO a
finishError s = hPutStrLn stderr s >> exitFailure

selfZip :: Monad m => [a] -> StateT Int m [((a, Atom y), Maybe (Atom y))]
selfZip lst = do l <- traverse (\v -> (,) v <$> freshTokenSt) lst
                 return (zip l (Nothing:map (Just . snd) l))

parseSwitch :: Monad m => (((a, [a]), Atom a), Maybe (Atom a))
                       -> StateT Int m [Triple (Atom Text) (Atom a)]
parseSwitch o = (parseArgument "cur" id (makeQuoted . fst) o ++)
              . concatMap (parseArgument "first" (const (snd (fst o))) makeQuoted)
              <$> selfZip (snd (fst (fst o)))
 where parseArgument fs c q (arg,prev) 
          = [ case prev of Nothing -> Triple fs (c (snd arg)) (snd arg)
                           Just v -> Triple "next" v (snd arg)
            , Triple "string" (snd arg) (q (fst arg)) ]

-- TODO: think of a way to get this out of the source code
initialstate :: [(Text,[Text])] -> Map Text Population
initialstate switches
  = fromListWith const $
    [ ( "switches" , popFromLst . runIdentity . unFresh . fmap concat $
                     do sw <- selfZip switches
                        traverse parseSwitch sw )
    ] ++ map (fmap popFromLst) baseState