{-# OPTIONS_GHC -Wall #-} {-# LANGUAGE BangPatterns, LambdaCase, ApplicativeDo, OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveTraversable, FlexibleInstances, FlexibleContexts #-}
module Main (main) where
import Helpers
import Data.Set as Set (toList)
import ParseRulesFromTripleStore(ParseRule(..),tripleStoreToParseRules,fmap23)
import TokenAwareParser(Atom(..),freshTokenSt,parseText,deAtomize,freshenUp,parseListOf,runToken,Token,LinePos,showPos,builtIns,makeQuoted)
import RuleSet(oldNewSystem,ruleSetRelations,prePostRuleSet,Rule(..),Expression(..))
import System.IO (stderr)
import System.Exit (exitFailure)
import System.Console.Terminal.Size (size,width)
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

newtype Population
 = TR { getPop   :: FullStore}

popFromLst :: [Triple (Atom Text) (Atom Text)] -> Population
popFromLst = TR . storeFromLst

storeFromLst :: [Triple (Atom Text) (Atom Text)] -> FullStore
storeFromLst = foldl' (\v w -> fst (insertTriple w v)) mempty

type FullParser = [ParseRule (Atom Text) Text Text]
type FullRules = [Rule (TransactionVariable (Atom Text)) (Atom Text)]
type FullStore = TripleStore (Atom Text) (Atom Text)
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
   , ( "count"
     , ( "count the number of triples"
       , eachPop (lift . Prelude.putStrLn . show . length . getList)))
   , ( "asParser"
     , ( "turn the population into the parser for -i"
       , noArgs "asParser" $
         do TR pop <- retrieve "population"
            parser <- apply "asParser" ["population"]
            let rules = restrictTo ruleSetRelations pop
            overwrite "parser" (TR parser)
            overwrite "rules" (TR rules)
            overwrite "population" (TR (parser <> rules))
       ))
   , ( "apply"
     , ( "apply the rule-system of first argument and put result into final argument (overwrite what was there). The remaining arguments form the population the system is applied to (or to the final argument if there are no remaining arguments given)."
       , \args ->
           let (rsys,from,targ) = case args of
                 [] -> ("population",["population"],"population")
                 [x] -> (x,[x],x)
                 (x:xs) -> (x,init xs,last xs)
           in do v<- apply rsys from
                 overwrite targ (TR v)
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
        r <- getRules "rules"
        res <- unFresh (ruleConsequences r . mconcat =<< sequence trps)
        -- liftIO$ renameWarnings res
        overwrite "population" (TR res)
        return ()
  pass f v = do{_<-f v;return v}
  ruleConsequences r v
    = renameAndAdd v <$> (pass (liftIO . renameWarnings) =<<
          oldNewSystem (liftIO$finishError "Error occurred in applying rule-set: rules & data lead to an inconsistency.")
                       freshTokenSt r v)
  renameAndAdd v (v',n) = (storeFromLst . (map (fmap (findSelfMap n)) v <>) . getList . TR) v'
  apply :: Text -> [Text] -> SpiegelState FullStore
  apply rsys from
   = do pops <- mapM (fmap getList . retrieve) from
        let pop = mconcat <$> traverse (freshenUp freshTokenSt) pops
        r <- getRules rsys
        res <- unFresh (oldNewSystem (liftIO$finishError "Error occurred in applying rule-set: rules & data lead to an inconsistency.")
                                       freshTokenSt r =<< pop)
        liftIO$ renameWarnings res
        return (fst res)
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
        pExp I            = "="
        pExp (Compose e1 e2) = "("<>pExp e1<>";"<>pExp e2<>")"
        pExp (Conjunction e1 e2) = "("<>pExp e1<>" /\\ "<>pExp e2<>")"
        pExp (Flp e1) = pExp e1<>"~"
        pExp Bot = "Bot"
        pExp (Pair a1 a2) = "Pair "<>showT a1<>" "<>showT a2

prettyPPopulation :: Population -> Text
prettyPPopulation v
 = Helpers.unlines [ showPad w1 n <> "\8715 "<>showPad w2 s<>" \8614 "<>showT t
                   | Triple n s t <- l]
 where (w1,w2) = foldr max2 (0,0) l
       l = getList v
       max2 (Triple a b _) (al,bl)
         = (max al (length (show a)), max bl (length (show b)))
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
  = fromListWith const
    [ ( "switches" , popFromLst . runIdentity . unFresh . fmap concat $
                     do sw <- selfZip switches
                        traverse parseSwitch sw )
    , ( "parser"
      , popFromLst
            [ "choice"      ∋ "Classification"          ↦ Fresh 110
            , "choice"      ∋ "ClassificationStatement" ↦ Fresh 98
            , "choice"      ∋ "ConceptList"             ↦ Fresh 120
            , "choice"      ∋ "ConceptList"             ↦ Fresh 128
            , "choice"      ∋ "ConsConceptList"         ↦ Fresh 120
            , "choice"      ∋ "ConsSyntaxList"          ↦ Fresh 162
            , "choice"      ∋ "Declaration"             ↦ Fresh 140
            , "choice"      ∋ "DeclarationStatement"    ↦ Fresh 102
            , "choice"      ∋ "DeclarationType"         ↦ Fresh 132
            , "choice"      ∋ "QuotedStringElement"     ↦ Fresh 174
            , "choice"      ∋ "RelationElement"         ↦ Fresh 178
            , "choice"      ∋ "Statement"               ↦ Fresh 98
            , "choice"      ∋ "Statement"               ↦ Fresh 102
            , "choice"      ∋ "Statement"               ↦ Fresh 106
            , "choice"      ∋ "Syntax"                  ↦ Fresh 148
            , "choice"      ∋ "SyntaxElement"           ↦ Fresh 174
            , "choice"      ∋ "SyntaxElement"           ↦ Fresh 178
            , "choice"      ∋ "SyntaxList"              ↦ Fresh 162
            , "choice"      ∋ "SyntaxList"              ↦ Fresh 170
            , "choice"      ∋ "SyntaxStatement"         ↦ Fresh 106
            , "nonTerminal" ∋ "classification"          ↦ "Classification"
            , "nonTerminal" ∋ "concept"                 ↦ "String"
            , "nonTerminal" ∋ "conceptList"             ↦ "ConceptList"
            , "nonTerminal" ∋ "concepts"                ↦ "DeclarationType"
            , "nonTerminal" ∋ "declaration"             ↦ "Declaration"
            , "nonTerminal" ∋ "fst"                     ↦ "String"
            , "nonTerminal" ∋ "head1"                   ↦ "String"
            , "nonTerminal" ∋ "head2"                   ↦ "SyntaxElement"
            , "nonTerminal" ∋ "mainConcept"             ↦ "String"
            , "nonTerminal" ∋ "qstring"                 ↦ "QuotedString"
            , "nonTerminal" ∋ "relation"                ↦ "StringAndOrigin"
            , "nonTerminal" ∋ "relationName"            ↦ "UnquotedString"
            , "nonTerminal" ∋ "snd"                     ↦ "String"
            , "nonTerminal" ∋ "syntax"                  ↦ "Syntax"
            , "nonTerminal" ∋ "syntaxList"              ↦ "SyntaxList"
            , "nonTerminal" ∋ "tail1"                   ↦ "ConceptList"
            , "nonTerminal" ∋ "tail2"                   ↦ "SyntaxList"
            , "recogniser"  ∋ Fresh 98                  ↦ "classification"
            , "recogniser"  ∋ Fresh 102                 ↦ "declaration"
            , "recogniser"  ∋ Fresh 106                 ↦ "syntax"
            , "continuation"∋ Fresh 110                 ↦ Fresh 112
            , "recogniser"  ∋ Fresh 110                 ↦ "\"CLASSIFY\""
            , "continuation"∋ Fresh 112                 ↦ Fresh 114
            , "recogniser"  ∋ Fresh 112                 ↦ "mainConcept"
            , "continuation"∋ Fresh 114                 ↦ Fresh 116
            , "recogniser"  ∋ Fresh 114                 ↦ "\"IS\""
            , "recogniser"  ∋ Fresh 116                 ↦ "conceptList"
            , "continuation"∋ Fresh 120                 ↦ Fresh 122
            , "recogniser"  ∋ Fresh 120                 ↦ "head1"
            , "continuation"∋ Fresh 122                 ↦ Fresh 124
            , "recogniser"  ∋ Fresh 122                 ↦ "\"/\\\\\""
            , "recogniser"  ∋ Fresh 124                 ↦ "tail1"
            , "recogniser"  ∋ Fresh 128                 ↦ "head1"
            , "continuation"∋ Fresh 132                 ↦ Fresh 134
            , "recogniser"  ∋ Fresh 132                 ↦ "fst"
            , "continuation"∋ Fresh 134                 ↦ Fresh 136
            , "recogniser"  ∋ Fresh 134                 ↦ "\"*\""
            , "recogniser"  ∋ Fresh 136                 ↦ "snd"
            , "continuation"∋ Fresh 140                 ↦ Fresh 142
            , "recogniser"  ∋ Fresh 140                 ↦ "relation"
            , "continuation"∋ Fresh 142                 ↦ Fresh 144
            , "recogniser"  ∋ Fresh 142                 ↦ "\"::\""
            , "recogniser"  ∋ Fresh 144                 ↦ "concepts"
            , "continuation"∋ Fresh 148                 ↦ Fresh 150
            , "recogniser"  ∋ Fresh 148                 ↦ "\"VIEW\""
            , "continuation"∋ Fresh 150                 ↦ Fresh 152
            , "recogniser"  ∋ Fresh 150                 ↦ "concept"
            , "continuation"∋ Fresh 152                 ↦ Fresh 154
            , "recogniser"  ∋ Fresh 152                 ↦ "\"=\""
            , "continuation"∋ Fresh 154                 ↦ Fresh 156
            , "recogniser"  ∋ Fresh 154                 ↦ "\"[\""
            , "continuation"∋ Fresh 156                 ↦ Fresh 158
            , "recogniser"  ∋ Fresh 156                 ↦ "syntaxList"
            , "recogniser"  ∋ Fresh 158                 ↦ "\"]\""
            , "continuation"∋ Fresh 162                 ↦ Fresh 164
            , "recogniser"  ∋ Fresh 162                 ↦ "head2"
            , "continuation"∋ Fresh 164                 ↦ Fresh 166
            , "recogniser"  ∋ Fresh 164                 ↦ "\",\""
            , "recogniser"  ∋ Fresh 166                 ↦ "tail2"
            , "recogniser"  ∋ Fresh 170                 ↦ "head2"
            , "recogniser"  ∋ Fresh 174                 ↦ "qstring"
            , "recogniser"  ∋ Fresh 178                 ↦ "relationName"]
      )
    , ( "asParser"
      , popFromLst
            [ "rule"    ∋ Fresh 0   ↦ Fresh 1
            , "eFst"    ∋ Fresh 1   ↦ Fresh 2
            , "eSnd"    ∋ Fresh 1   ↦ Fresh 3
            , "pre"     ∋ Fresh 2   ↦ "conceptList"
            , "during"  ∋ Fresh 3   ↦ "conceptLists"
            , "rule"    ∋ Fresh 4   ↦ Fresh 5
            , "eFst"    ∋ Fresh 5   ↦ Fresh 6
            , "eSnd"    ∋ Fresh 5   ↦ Fresh 3
            , "compose" ∋ Fresh 6   ↦ Fresh 7
            , "eFst"    ∋ Fresh 7   ↦ Fresh 3
            , "eSnd"    ∋ Fresh 7   ↦ Fresh 9
            , "pre"     ∋ Fresh 9   ↦ "tail1"
            , "rule"    ∋ Fresh 11  ↦ Fresh 12
            , "eFst"    ∋ Fresh 12  ↦ Fresh 13
            , "eSnd"    ∋ Fresh 12  ↦ Fresh 21
            , "compose" ∋ Fresh 13  ↦ Fresh 14
            , "eFst"    ∋ Fresh 14  ↦ Fresh 15
            , "eSnd"    ∋ Fresh 14  ↦ Fresh 20
            , "compose" ∋ Fresh 15  ↦ Fresh 16
            , "eFst"    ∋ Fresh 16  ↦ Fresh 17
            , "eSnd"    ∋ Fresh 16  ↦ Fresh 3
            , "converse"∋ Fresh 17  ↦ Fresh 18
            , "pre"     ∋ Fresh 18  ↦ "mainConcept"
            , "pre"     ∋ Fresh 20  ↦ "head1"
            , "during"  ∋ Fresh 21  ↦ "subConcepts"
            , "rule"    ∋ Fresh 22  ↦ Fresh 23
            , "eFst"    ∋ Fresh 23  ↦ Fresh 24
            , "eSnd"    ∋ Fresh 23  ↦ Fresh 21
            , "compose" ∋ Fresh 24  ↦ Fresh 25
            , "eFst"    ∋ Fresh 25  ↦ Fresh 21
            , "eSnd"    ∋ Fresh 25  ↦ Fresh 21
            , "rule"    ∋ Fresh 29  ↦ Fresh 30
            , "eFst"    ∋ Fresh 30  ↦ Fresh 31
            , "eSnd"    ∋ Fresh 30  ↦ Fresh 21
            , "conjunct"∋ Fresh 31  ↦ Fresh 32
            , "eFst"    ∋ Fresh 32  ↦ Fresh 33
            , "eSnd"    ∋ Fresh 32  ↦ Fresh 38
            , "compose" ∋ Fresh 33  ↦ Fresh 34
            , "eFst"    ∋ Fresh 34  ↦ Fresh 17
            , "eSnd"    ∋ Fresh 34  ↦ Fresh 18
            , "rule"    ∋ Fresh 40  ↦ Fresh 41
            , "eFst"    ∋ Fresh 41  ↦ Fresh 42
            , "eSnd"    ∋ Fresh 41  ↦ Fresh 21
            , "conjunct"∋ Fresh 42  ↦ Fresh 43
            , "eFst"    ∋ Fresh 43  ↦ Fresh 44
            , "eSnd"    ∋ Fresh 43  ↦ Fresh 49
            , "compose" ∋ Fresh 44  ↦ Fresh 45
            , "eFst"    ∋ Fresh 45  ↦ Fresh 46
            , "eSnd"    ∋ Fresh 45  ↦ Fresh 47
            , "converse"∋ Fresh 46  ↦ Fresh 47
            , "pre"     ∋ Fresh 47  ↦ "concept"
            , "rule"    ∋ Fresh 51  ↦ Fresh 52
            , "eFst"    ∋ Fresh 52  ↦ Fresh 53
            , "eSnd"    ∋ Fresh 52  ↦ Fresh 54
            , "pre"     ∋ Fresh 53  ↦ "qstring"
            , "rule"    ∋ Fresh 55  ↦ Fresh 56
            , "eFst"    ∋ Fresh 56  ↦ Fresh 57
            , "eSnd"    ∋ Fresh 56  ↦ Fresh 58
            , "pre"     ∋ Fresh 57  ↦ "relationName"
            , "rule"    ∋ Fresh 59  ↦ Fresh 60
            , "eFst"    ∋ Fresh 60  ↦ Fresh 61
            , "eSnd"    ∋ Fresh 60  ↦ Fresh 66
            , "compose" ∋ Fresh 61  ↦ Fresh 62
            , "eFst"    ∋ Fresh 62  ↦ Fresh 63
            , "eSnd"    ∋ Fresh 62  ↦ Fresh 64
            , "pre"     ∋ Fresh 63  ↦ "string"
            , "converse"∋ Fresh 64  ↦ Fresh 63
            , "rule"    ∋ Fresh 67  ↦ Fresh 68
            , "eFst"    ∋ Fresh 68  ↦ Fresh 69
            , "eSnd"    ∋ Fresh 68  ↦ Fresh 57
            , "compose" ∋ Fresh 69  ↦ Fresh 70
            , "eFst"    ∋ Fresh 70  ↦ Fresh 71
            , "eSnd"    ∋ Fresh 70  ↦ Fresh 63
            , "compose" ∋ Fresh 71  ↦ Fresh 72
            , "eFst"    ∋ Fresh 72  ↦ Fresh 73
            , "eSnd"    ∋ Fresh 72  ↦ Fresh 74
            , "pre"     ∋ Fresh 73  ↦ "declaration"
            , "pre"     ∋ Fresh 74  ↦ "relation"
            , "rule"    ∋ Fresh 77  ↦ Fresh 78
            , "eFst"    ∋ Fresh 78  ↦ Fresh 79
            , "eSnd"    ∋ Fresh 78  ↦ Fresh 86
            , "compose" ∋ Fresh 79  ↦ Fresh 80
            , "eFst"    ∋ Fresh 80  ↦ Fresh 81
            , "eSnd"    ∋ Fresh 80  ↦ Fresh 85
            , "compose" ∋ Fresh 81  ↦ Fresh 82
            , "eFst"    ∋ Fresh 82  ↦ Fresh 73
            , "eSnd"    ∋ Fresh 82  ↦ Fresh 84
            , "pre"     ∋ Fresh 84  ↦ "concepts"
            , "pre"     ∋ Fresh 85  ↦ "snd"
            , "post"    ∋ Fresh 86  ↦ "nonTerminal"
            , "rule"    ∋ Fresh 87  ↦ Fresh 88
            , "eFst"    ∋ Fresh 88  ↦ Fresh 89
            , "eSnd"    ∋ Fresh 88  ↦ Fresh 98
            , "compose" ∋ Fresh 89  ↦ Fresh 90
            , "eFst"    ∋ Fresh 90  ↦ Fresh 91
            , "eSnd"    ∋ Fresh 90  ↦ Fresh 97
            , "compose" ∋ Fresh 91  ↦ Fresh 92
            , "eFst"    ∋ Fresh 92  ↦ Fresh 93
            , "eSnd"    ∋ Fresh 92  ↦ Fresh 46
            , "converse"∋ Fresh 93  ↦ Fresh 21
            , "pre"     ∋ Fresh 97  ↦ "syntaxList"
            , "post"    ∋ Fresh 98  ↦ "choice"
            , "rule"    ∋ Fresh 99  ↦ Fresh 100
            , "eFst"    ∋ Fresh 100 ↦ Fresh 101
            , "eSnd"    ∋ Fresh 100 ↦ Fresh 102
            , "pre"     ∋ Fresh 101 ↦ "head2"
            , "post"    ∋ Fresh 102 ↦ "recogniser"
            , "rule"    ∋ Fresh 103 ↦ Fresh 104
            , "eFst"    ∋ Fresh 104 ↦ Fresh 105
            , "eSnd"    ∋ Fresh 104 ↦ Fresh 106
            , "pre"     ∋ Fresh 105 ↦ "tail2"
            , "post"    ∋ Fresh 106 ↦ "continuation"
            ] )
    ]