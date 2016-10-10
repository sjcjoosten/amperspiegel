{-# OPTIONS_GHC -Wall #-} {-# LANGUAGE BangPatterns, LambdaCase, ApplicativeDo, OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveTraversable, FlexibleInstances, FlexibleContexts #-}
module Main (main) where
import Helpers
import Data.String (IsString)
import Data.Set as Set (toList)
import ParseRulesFromTripleStore(ParseRule(..),tripleStoreRelations,tripleStoreToParseRules,fmap23)
import TokenAwareParser(Atom(..),freshTokenSt,parseText,deAtomize,freshenUp,parseListOf,runToken,Token,LinePos,showPos,builtIns)
import ApplyRuleSet(applySystem)
import RuleSetFromTripleStore(ruleSetRelations,tripleStoreToRuleSet)
import System.IO (stderr)
import System.Exit (exitFailure)
import System.Console.Terminal.Size (size,width)
import qualified Data.Map as Map

initialstate :: Map Text Population
initialstate
  = fromListWith const
    [ ( "parser"
      , LST [ "choice"      ∋ "Classification"          ↦ Fresh 110
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
      , LST ["rule"    ∋ Fresh 0   ↦ Fresh 1
            ,"eFst"    ∋ Fresh 1   ↦ Fresh 2
            ,"eSnd"    ∋ Fresh 1   ↦ Fresh 3
            ,"atom"    ∋ Fresh 2   ↦ "conceptList"
            ,"atom"    ∋ Fresh 3   ↦ "conceptLists"
            ,"rule"    ∋ Fresh 4   ↦ Fresh 5
            ,"eFst"    ∋ Fresh 5   ↦ Fresh 6
            ,"eSnd"    ∋ Fresh 5   ↦ Fresh 10
            ,"compose" ∋ Fresh 6   ↦ Fresh 7
            ,"eFst"    ∋ Fresh 7   ↦ Fresh 8
            ,"eSnd"    ∋ Fresh 7   ↦ Fresh 9
            ,"atom"    ∋ Fresh 8   ↦ "conceptLists"
            ,"atom"    ∋ Fresh 9   ↦ "tail1"
            ,"atom"    ∋ Fresh 10  ↦ "conceptLists"
            ,"rule"    ∋ Fresh 11  ↦ Fresh 12
            ,"eFst"    ∋ Fresh 12  ↦ Fresh 13
            ,"eSnd"    ∋ Fresh 12  ↦ Fresh 21
            ,"compose" ∋ Fresh 13  ↦ Fresh 14
            ,"eFst"    ∋ Fresh 14  ↦ Fresh 15
            ,"eSnd"    ∋ Fresh 14  ↦ Fresh 20
            ,"compose" ∋ Fresh 15  ↦ Fresh 16
            ,"eFst"    ∋ Fresh 16  ↦ Fresh 17
            ,"eSnd"    ∋ Fresh 16  ↦ Fresh 19
            ,"converse"∋ Fresh 17  ↦ Fresh 18
            ,"atom"    ∋ Fresh 18  ↦ "mainConcept"
            ,"atom"    ∋ Fresh 19  ↦ "conceptLists"
            ,"atom"    ∋ Fresh 20  ↦ "head1"
            ,"atom"    ∋ Fresh 21  ↦ "subConcepts"
            ,"rule"    ∋ Fresh 22  ↦ Fresh 23
            ,"eFst"    ∋ Fresh 23  ↦ Fresh 24
            ,"eSnd"    ∋ Fresh 23  ↦ Fresh 28
            ,"compose" ∋ Fresh 24  ↦ Fresh 25
            ,"eFst"    ∋ Fresh 25  ↦ Fresh 26
            ,"eSnd"    ∋ Fresh 25  ↦ Fresh 27
            ,"atom"    ∋ Fresh 26  ↦ "subConcepts"
            ,"atom"    ∋ Fresh 27  ↦ "subConcepts"
            ,"atom"    ∋ Fresh 28  ↦ "subConcepts"
            ,"rule"    ∋ Fresh 29  ↦ Fresh 30
            ,"eFst"    ∋ Fresh 30  ↦ Fresh 31
            ,"eSnd"    ∋ Fresh 30  ↦ Fresh 39
            ,"conjunct"∋ Fresh 31  ↦ Fresh 32
            ,"eFst"    ∋ Fresh 32  ↦ Fresh 33
            ,"eSnd"    ∋ Fresh 32  ↦ Fresh 38
            ,"compose" ∋ Fresh 33  ↦ Fresh 34
            ,"eFst"    ∋ Fresh 34  ↦ Fresh 35
            ,"eSnd"    ∋ Fresh 34  ↦ Fresh 37
            ,"converse"∋ Fresh 35  ↦ Fresh 36
            ,"atom"    ∋ Fresh 36  ↦ "mainConcept"
            ,"atom"    ∋ Fresh 37  ↦ "mainConcept"
            ,"atom"    ∋ Fresh 39  ↦ "subConcepts"
            ,"rule"    ∋ Fresh 40  ↦ Fresh 41
            ,"eFst"    ∋ Fresh 41  ↦ Fresh 42
            ,"eSnd"    ∋ Fresh 41  ↦ Fresh 50
            ,"conjunct"∋ Fresh 42  ↦ Fresh 43
            ,"eFst"    ∋ Fresh 43  ↦ Fresh 44
            ,"eSnd"    ∋ Fresh 43  ↦ Fresh 49
            ,"compose" ∋ Fresh 44  ↦ Fresh 45
            ,"eFst"    ∋ Fresh 45  ↦ Fresh 46
            ,"eSnd"    ∋ Fresh 45  ↦ Fresh 48
            ,"converse"∋ Fresh 46  ↦ Fresh 47
            ,"atom"    ∋ Fresh 47  ↦ "concept"
            ,"atom"    ∋ Fresh 48  ↦ "concept"
            ,"atom"    ∋ Fresh 50  ↦ "subConcepts"
            ,"rule"    ∋ Fresh 51  ↦ Fresh 52
            ,"eFst"    ∋ Fresh 52  ↦ Fresh 53
            ,"eSnd"    ∋ Fresh 52  ↦ Fresh 54
            ,"atom"    ∋ Fresh 53  ↦ "syntaxList"
            ,"atom"    ∋ Fresh 54  ↦ "syntaxLists"
            ,"rule"    ∋ Fresh 55  ↦ Fresh 56
            ,"eFst"    ∋ Fresh 56  ↦ Fresh 57
            ,"eSnd"    ∋ Fresh 56  ↦ Fresh 61
            ,"compose" ∋ Fresh 57  ↦ Fresh 58
            ,"eFst"    ∋ Fresh 58  ↦ Fresh 59
            ,"eSnd"    ∋ Fresh 58  ↦ Fresh 60
            ,"atom"    ∋ Fresh 59  ↦ "syntaxList"
            ,"atom"    ∋ Fresh 60  ↦ "tail2"
            ,"atom"    ∋ Fresh 61  ↦ "syntaxLists"
            ,"rule"    ∋ Fresh 62  ↦ Fresh 63
            ,"eFst"    ∋ Fresh 63  ↦ Fresh 64
            ,"eSnd"    ∋ Fresh 63  ↦ Fresh 65
            ,"atom"    ∋ Fresh 64  ↦ "qstring"
            ,"rule"    ∋ Fresh 66  ↦ Fresh 67
            ,"eFst"    ∋ Fresh 67  ↦ Fresh 68
            ,"eSnd"    ∋ Fresh 67  ↦ Fresh 69
            ,"atom"    ∋ Fresh 68  ↦ "relationName"
            ,"rule"    ∋ Fresh 70  ↦ Fresh 71
            ,"eFst"    ∋ Fresh 71  ↦ Fresh 72
            ,"eSnd"    ∋ Fresh 71  ↦ Fresh 77
            ,"compose" ∋ Fresh 72  ↦ Fresh 73
            ,"eFst"    ∋ Fresh 73  ↦ Fresh 74
            ,"eSnd"    ∋ Fresh 73  ↦ Fresh 75
            ,"atom"    ∋ Fresh 74  ↦ "string"
            ,"converse"∋ Fresh 75  ↦ Fresh 76
            ,"atom"    ∋ Fresh 76  ↦ "string"
            ,"rule"    ∋ Fresh 78  ↦ Fresh 79
            ,"eFst"    ∋ Fresh 79  ↦ Fresh 80
            ,"eSnd"    ∋ Fresh 79  ↦ Fresh 87
            ,"compose" ∋ Fresh 80  ↦ Fresh 81
            ,"eFst"    ∋ Fresh 81  ↦ Fresh 82
            ,"eSnd"    ∋ Fresh 81  ↦ Fresh 86
            ,"compose" ∋ Fresh 82  ↦ Fresh 83
            ,"eFst"    ∋ Fresh 83  ↦ Fresh 84
            ,"eSnd"    ∋ Fresh 83  ↦ Fresh 85
            ,"atom"    ∋ Fresh 84  ↦ "declaration"
            ,"atom"    ∋ Fresh 85  ↦ "relation"
            ,"atom"    ∋ Fresh 86  ↦ "string"
            ,"atom"    ∋ Fresh 87  ↦ "relationName"
            ,"rule"    ∋ Fresh 88  ↦ Fresh 89
            ,"eFst"    ∋ Fresh 89  ↦ Fresh 90
            ,"eSnd"    ∋ Fresh 89  ↦ Fresh 97
            ,"compose" ∋ Fresh 90  ↦ Fresh 91
            ,"eFst"    ∋ Fresh 91  ↦ Fresh 92
            ,"eSnd"    ∋ Fresh 91  ↦ Fresh 96
            ,"compose" ∋ Fresh 92  ↦ Fresh 93
            ,"eFst"    ∋ Fresh 93  ↦ Fresh 94
            ,"eSnd"    ∋ Fresh 93  ↦ Fresh 95
            ,"atom"    ∋ Fresh 94  ↦ "declaration"
            ,"atom"    ∋ Fresh 95  ↦ "concepts"
            ,"atom"    ∋ Fresh 96  ↦ "snd"
            ,"atom"    ∋ Fresh 97  ↦ "nonTerminal"
            ,"rule"    ∋ Fresh 98  ↦ Fresh 99
            ,"eFst"    ∋ Fresh 99  ↦ Fresh 100
            ,"eSnd"    ∋ Fresh 99  ↦ Fresh 109
            ,"compose" ∋ Fresh 100 ↦ Fresh 101
            ,"eFst"    ∋ Fresh 101 ↦ Fresh 102
            ,"eSnd"    ∋ Fresh 101 ↦ Fresh 108
            ,"compose" ∋ Fresh 102 ↦ Fresh 103
            ,"eFst"    ∋ Fresh 103 ↦ Fresh 104
            ,"eSnd"    ∋ Fresh 103 ↦ Fresh 106
            ,"converse"∋ Fresh 104 ↦ Fresh 105
            ,"atom"    ∋ Fresh 105 ↦ "subConcepts"
            ,"converse"∋ Fresh 106 ↦ Fresh 107
            ,"atom"    ∋ Fresh 107 ↦ "concept"
            ,"atom"    ∋ Fresh 108 ↦ "syntaxList"
            ,"atom"    ∋ Fresh 109 ↦ "choice"
            ,"rule"    ∋ Fresh 110 ↦ Fresh 111
            ,"eFst"    ∋ Fresh 111 ↦ Fresh 112
            ,"eSnd"    ∋ Fresh 111 ↦ Fresh 113
            ,"atom"    ∋ Fresh 112 ↦ "head2"
            ,"atom"    ∋ Fresh 113 ↦ "recogniser"
            ,"rule"    ∋ Fresh 114 ↦ Fresh 115
            ,"eFst"    ∋ Fresh 115 ↦ Fresh 116
            ,"eSnd"    ∋ Fresh 115 ↦ Fresh 117
            ,"atom"    ∋ Fresh 116 ↦ "tail2"
            ,"atom"    ∋ Fresh 117 ↦ "continuation"])
    ]

main :: IO ()
main = do as <- getChunks =<< getArgs
          evalStateT (forM_ as (uncurry doCommand))
                     initialstate
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

data Population
 = TR  { _getPop   :: FullStore
       , popParser :: Maybe FullParser
       , popRules  :: Maybe FullRules}
 | LST { _getList  :: [Triple (Atom Text) (Atom Text)]}

getPop :: Population -> TripleStore (Atom Text) (Atom Text)
getPop (LST a) = foldl' (\v w -> fst (insertTriple w v)) mempty a
getPop r = _getPop r

type FullParser = [ParseRule (Atom Text) Text Text]
type FullRules = [Rule (Atom Text) (Atom Text)]
type FullStore = TripleStore (Atom Text) (Atom Text)

doCommand :: Text -> [Text] -> StateT (Map Text Population) IO ()
doCommand cmd
 = findWithDefault
       (\_ -> lift$ finishError ("Not a valid command: "<>cmd<>"\nGet a list of commands using: -h"))
       cmd lkp'
 where lkp' = fmap snd (fromListWith const commands)

showUnexpected :: Token (LinePos Text, Bool)
             -> String -> Maybe String
             -> StateT (Map Text Population) IO
                  (m [Triple (Atom Text) (Atom Text)])
showUnexpected tk expc mby
 = liftIO . finishError $
   "Parse error, unexpected "<> pack (showPs tk)<>"\n  Expecting: "<>pack expc
     <> (case mby of {Nothing -> "";Just v ->"\n  mby(TODO: fix me into something more descriptive):"<>pack v})
 where showPs = showPos unpack . fst . runToken

commands :: [ ( Text
                , ( Text
                  , [Text]
                     -> StateT (Map Text (Population))
                               IO ()
                  ) ) ]
commands = [ ( "i"
             , ( "parse file as input"
               , (\files -> do txts <- lift$ mapM (Helpers.readFile . unpack) files
                               p <- getParser "parser"
                               trps <- traverse (parseText show (parseListOf builtIns (p,"Statement")) showUnexpected) txts
                               overwrite "population" =<< unFresh (LST . mconcat <$> sequence trps)
                               res <- apply "rules" ["population"]
                               overwrite "population" (TR res Nothing Nothing)
                               return ()
                               )))
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
                 do res <- apply "asParser" ["population"]
                    let parser = restrictTo tripleStoreRelations res
                    let rules = restrictTo ruleSetRelations res
                    overwrite "parser" (TR parser Nothing Nothing)
                    overwrite "rules" (TR rules Nothing Nothing)
                    overwrite "population" (TR (unionTS parser rules) Nothing Nothing)
               ))
           , ( "apply"
             , ( "apply the rule-system of first argument and put result into final argument (overwrite what was there). The remaining arguments form the population the system is applied to (or to the final argument if there are no remaining arguments given)."
               , \args ->
                   let (rsys,from,targ) = case args of
                         [] -> ("population",["population"],"population")
                         [x] -> (x,[x],x)
                         (x:xs) -> (x,init xs,last xs)
                   in do v<- apply rsys from
                         overwrite targ (TR v Nothing Nothing)
               )
             )
           ]
           where
             apply :: Text -> [Text] -> StateT (Map Text Population) IO FullStore
             apply rsys from
                   = do pops <- mapM (fmap getList . retrieve) from
                        let pop = mconcat <$> traverse (freshenUp freshTokenSt) pops
                        r <- getRules rsys
                        res <- unFresh (applySystem (liftIO$finishError "Error occurred in applying rule-set: rules & data lead to an inconsistency.")
                                                       freshTokenSt r =<< pop)
                        liftIO$ renameWarnings res
                        return (fst res)
             unFresh v = evalStateT v 0
             noArgs :: Text
                      -> StateT (Map Text Population) IO ()
                      -> [t]
                      -> StateT (Map Text Population) IO ()
             noArgs s f
              = \case {[] -> f;_->lift$finishError (s <> " takes no arguments")}
             eachPop :: (Population -> StateT (Map Text Population) IO ())
                       -> [Text] -> StateT (Map Text Population) IO ()
             eachPop f = eachDo f retrieve
             eachDo :: (a -> StateT (Map Text Population) IO ())
                    -> (Text -> StateT (Map Text Population) IO a)
                    -> ([Text] -> StateT (Map Text Population) IO ())
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
prettyPRules = mconcat . map (\v -> pack (show v) <> "\n")

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
getList (LST v) = v
getList x = mconcat . map getTripls . Map.toList $ getPop x
  where getTripls (a,(mp,_))
          = [(Triple nm a b) | (nm,bs) <- Map.toList mp, b<-Set.toList bs]

add :: Monad b => Text -> Population -> StateT (Map Text Population) b ()
add s p = modify (insertWith extend s p)
  where extend _ (LST _) = p
        extend _ (TR po pa ru)
          = TR po
               (case popParser p of {Nothing -> pa; v -> v})
               (case popRules p of {Nothing -> ru; v -> v})

overwrite :: Monad b => Text -> Population -> StateT (Map Text Population) b ()
overwrite s p = modify (insert s p)

retrieve :: Monad b => Text -> StateT (Map Text Population) b Population
retrieve s
 = do mp <- get
      return $ findWithDefault (LST []) s mp

getParser :: Text -> StateT (Map Text Population) IO FullParser
getParser s
 = do mp <- retrieve s
      case mp of
        (TR{popParser = Just v}) -> return v
        v' -> let v = getPop v' in putBack v =<< (unAtomize =<< tripleStoreToParseRules pure v)
 where putBack v p
         = do add s (TR v (Just p) Nothing)
              return p
       unAtomize :: [ParseRule (Atom Text) (Atom Text) (Atom Text)] -> StateT (Map Text Population) IO FullParser
       unAtomize = traverse (fmap23 deAtomize deAtomize)

getRules :: Text -> StateT (Map Text Population) IO FullRules
getRules s
 = do mp <- retrieve s
      case mp of
        (TR{popRules = Just v}) -> return v
        v' -> let v = getPop v' in putBack v =<< (tripleStoreToRuleSet return v)
 where putBack v p
         = do add s (TR v Nothing (Just p))
              return p
    
finishError :: Text -> IO a
finishError s = hPutStrLn stderr s >> exitFailure

