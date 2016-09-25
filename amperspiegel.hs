{-# OPTIONS_GHC -Wall -Wno-unused-imports #-}
{-# LANGUAGE BangPatterns, LambdaCase #-} -- for the scanner position
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module Main where
import Data.Text.Lazy (Text,pack,unlines)
import qualified Data.Text.Lazy as Text
import Data.Text.Lazy.IO as Text (readFile,hPutStrLn,putStrLn)
import Data.String
import Data.Set as Set (toList)
import ParseRulesFromTripleStore(ParseRule(..),tripleStoreToParseRules,parseRuleToTripleStore,fmap23,tripleStoreRelations)
import Tokeniser(showPos,runToken,Token, LinePos,ScanResult,showPos,runLinePos)
import TokenAwareParser(Atom,freshTokenSt,parseText,parseListOf,deAtomize)
import Relations(Rule(..),(⨟),(⊆),(∩),Expression(..),Triple(..),TripleStore,insertTriple,restrictTo)
import ApplyRuleSet(applySystem)
import SimpleHelperMonads
import RuleSetFromTripleStore
import Control.Monad.Fail as F
import Data.Map as Map (Map,fromList,findWithDefault,insert,empty,lookup,toList)
import System.Environment
import Data.Foldable
import Control.Monad.State
import System.IO (stderr)
import System.Exit
import Data.Monoid
import Text.Earley (Report)

initialstate :: Map Text Population
initialstate
  = Map.fromList
     [ ( "parser"
       , Parser (error "default parser not bootstrapped yet (TODO)") mParser)
     ]

main :: IO ()
main = do as <- getChunks =<< getArgs
          evalStateT (forM_ as (uncurry doCommand))
                     initialstate
       where getChunks' [] = ([],[])
             getChunks' (a:as)
               = let (res,spl) = getChunks' as
                 in case a of
                      ('-':cmd) -> ((cmd,spl):res,[])
                      _ -> (res,a:spl)
             getChunks as
               = case getChunks' as of
                   (r,[]) -> return r
                   (_,_ ) -> finishError "First argument should be a command, that is: it should start with '-'"

data Population
 = TR {_getPop::TripleStore (Atom Text) (Atom Text)}
 | LST {_getList::[Triple (Atom Text) (Atom Text)]}
 | Parser {_getPop::TripleStore (Atom Text) (Atom Text)
          ,_popParser::FullParser}

getPop :: Population -> TripleStore (Atom Text) (Atom Text)
getPop (LST a) = foldl' (\v w -> fst (insertTriple w v)) Map.empty a
getPop r = _getPop r

type FullParser 
  = [ParseRule (Atom Text) Text Text]

doCommand :: String -> [String] -> StateT (Map Text Population) IO ()
doCommand cmd
 = Map.findWithDefault
       (\_ -> lift$ finishError ("Not a valid command: "<>pack cmd<>"\nGet a list of commands using: -h"))
       cmd lkp'
 where lkp' = fmap snd (Map.fromList commands)

showUnexpected :: Token (LinePos Text, Bool)
             -> String -> Maybe String
             -> StateT (Map Text Population) IO
                  (FreshnessGenerator [Triple (Atom Text) (Atom Text)])
showUnexpected tk expc mby
 = liftIO . finishError $
   "Parse error, unexpected "<> pack (showPs tk)<>"\n  Expecting: "<>pack expc
     <> (case mby of {Nothing -> "";Just v ->"\n  mby(TODO: fix me into something more descriptive):"<>pack v})
 where showPs = showPos . fst . runToken

commands :: [ ( String
                , ( String
                  , [String]
                     -> StateT (Map Text (Population))
                               IO ()
                  ) ) ]
commands = [ ( "i"
             , ( "parse file as input"
               , (\files -> do txts <- lift$ mapM Text.readFile files
                               p <- getParser "parser"
                               trps <- combinePops <$> (traverse (parseText (parseListOf (p,"Statement")) showUnexpected) txts)
                               add "population" (LST trps)
                               return ()
                               )))
           , ( "h"
             , ( "display this help"
               , \_ -> lift$ Prelude.putStrLn helpText))
           , ( "show"
             , ( "display the triples as a list"
               , eachPop (lift . Text.putStrLn . prettyPPopulation)))
           , ( "showP"
             , ( "display the triples as a set of parse-rules"
               , eachDo (lift . Text.putStrLn . prettyPParser) getParser))
           , ( "count"
             , ( "count the number of triples"
               , eachPop (lift . Prelude.putStrLn . show . length . getList)))
           , ( "asParser"
             , ( "Turn the population into the parser for -i"
               , \case [] -> do pop <- retrieve "population"
                                -- trans <- retrieve "asParser" TODO
                                res <- evalStateT (applySystem (liftIO$finishError "Error occurred in applying rule-set: rules & data lead to an inconsistency.") freshTokenSt ruleList (getList pop)) 0 -- TODO: apply a filter
                                let res' = fst res
                                let parser = restrictTo tripleStoreRelations res'
                                add "parser" (TR parser)
                                add "population" (TR res')
                       _ -> lift$finishError "asParser takes no arguments"
               ))
           ]
           where
             eachPop :: (Population -> StateT (Map Text Population) IO ())
                       -> [String] -> StateT (Map Text Population) IO ()
             eachPop f = eachDo f retrieve
             eachDo :: (a -> StateT (Map Text Population) IO ())
                    -> (Text -> StateT (Map Text Population) IO a)
                    -> ([String] -> StateT (Map Text Population) IO ())
             eachDo f g = \case [] -> f =<< g "population"
                                l  -> mapM_ (\v -> f =<< g (pack v)) l
             helpText
              = "These are the switches you can use:\n\n" ++
                   concat [ "  "++s++"  \t"++d++"\n"
                          | (s,(d,_)) <- commands]

prettyPParser :: FullParser -> Text
prettyPParser [] = ""
prettyPParser o@(ParseRule t _:_)
 = t <> " := " <>
   Text.intercalate ("\n  "<>pack (take (fromIntegral$Text.length t)
                                        (repeat ' '))<>"| ")
                    res <> "\n" <> prettyPParser tl
 where (res,tl) = mapsplit (\(ParseRule t' lst)
                            -> if t == t' then Just (pp lst) else Nothing) o
       pp = Text.intercalate ", " . map (pack . show)
       mapsplit _ [] = ([],[])
       mapsplit f o'@(a:r)
         = case f a of
             Just v -> let (rs,rm) = mapsplit f r in (v:rs,rm)
             Nothing -> ([],o')

prettyPPopulation :: Population -> Text
prettyPPopulation v
 = Text.unlines [ showPad w1 n <> ": "<>showPad w2 s<>" |--> "<>pack (show t)
                | Triple n s t <- getList v]
 where (w1,w2) = foldr max2  (0,0) (getList v)
       max2 (Triple a b _) (al,bl)
         = (max al (length (show a)), max bl (length (show b)))
showPad :: forall a. Show a => Int -> a -> Text
showPad w s
 = let t = show s
       x = w - length t
   in pack (show s <> take x (repeat ' '))

getList :: Population -> [Triple (Atom Text) (Atom Text)]
getList (LST v) = v
getList x = concat . map getTripls . Map.toList $ getPop x
  where getTripls (a,(mp,_))
          = [(Triple nm a b) | (nm,bs) <- Map.toList mp, b<-Set.toList bs]

combinePops :: [FreshnessGenerator [Triple (Atom Text) (Atom Text)]]
            -> [Triple (Atom Text) (Atom Text)]
combinePops = concat . snd . ($0) . runFg . sequence

add :: Monad b => Text -> Population -> StateT (Map Text Population) b ()
add s p = modify (Map.insert s p)

retrieve :: Monad b => Text -> StateT (Map Text Population) b Population
retrieve s
 = do mp <- get
      case Map.lookup s mp of
        Nothing -> return (LST [])
        Just v  -> return v

getParser :: Text -> StateT (Map Text Population) IO FullParser
getParser s
 = do mp <- retrieve s
      case mp of
        (Parser _ v) -> return v
        v' -> let v = getPop v' in putBack v =<< (unAtomize =<< tripleStoreToParseRules id v)
 where putBack v p
         = do add s (Parser v p)
              return p
       unAtomize :: [ParseRule (Atom Text) (Atom Text) (Atom Text)] -> StateT (Map Text Population) IO FullParser
       unAtomize = traverse (fmap23 deAtomize deAtomize)
       
finishError :: Text -> IO a
finishError s = hPutStrLn stderr s >> exitFailure

mParser :: (IsString x,IsString y,IsString z) => [ParseRule x y z]
mParser
   = [ParseRule "Classification"  ["CLASSIFY"
                                  ,"mainConcept" "String"
                                  ,"IS"
                                  ,"conceptList" "ConceptList"]
     ,ParseRule "DeclarationType" ["fst" "String"
                                  ,"*"
                                  ,"snd" "String"] 
     ,ParseRule "Declaration"     ["relation" "StringAndOrigin"
                                  ,"::"
                                  ,"concepts" "DeclarationType"]
     ,ParseRule "Syntax"          ["VIEW"
                                  ,"concept" "String"
                                  ,"="
                                  ,"["
                                  ,"syntaxList" "SyntaxList"
                                  ,"]"]
     ,ParseRule "ConceptList"     ["head1" "String"
                                  ,"/\\"
                                  ,"tail1" "ConceptList"]
     ,ParseRule "ConceptList"     ["head1" "String"]
     ,ParseRule "SyntaxList"      ["head2" "SyntaxElement"
                                  ,","
                                  ,"tail2" "SyntaxList"]
     ,ParseRule "SyntaxList"      ["head2" "SyntaxElement"]
     ,ParseRule "SyntaxElement"   ["qstring" "QuotedString"]
     ,ParseRule "SyntaxElement"   ["relationName" "UnquotedString"]
     ,ParseRule "Statement"       ["classification" "Classification"]
     ,ParseRule "Statement"       ["declaration" "Declaration"]
     ,ParseRule "Statement"       ["syntax" "Syntax"]
     ]

ruleList :: (IsString x) => [Rule x y]
ruleList
  = [ "conceptList" ⊆ "conceptLists"
    , "conceptLists" ⨟ "tail1" ⊆ "conceptLists"
    , Flp "mainConcept" ⨟ "conceptLists" ⨟ "head1" ⊆ "subConcepts"
    , "subConcepts" ⨟ "subConcepts" ⊆ "subConcepts"
    , Flp "mainConcept" ⨟ "mainConcept" ∩ I ⊆ "subConcepts"
    , Flp "concept" ⨟ "concept" ∩ I ⊆ "subConcepts"
    , "syntaxList" ⊆ "syntaxLists"
    , "syntaxList" ⨟ "tail2" ⊆ "syntaxLists"
    , "qstring" ⊆ I
    , "relationName" ⊆ I
    , "string" ⨟ Flp "string" ⊆ I -- this rule means every relation has a unique name. Unfortunately, there is no other way to disambiguate declarations.
    , "declaration" ⨟ "relation" ⨟ "string" ⊆ "relationName"
    , "declaration" ⨟ "concepts" ⨟ "snd" ⊆ "nonTerminal"
    , Flp "subConcepts" ⨟ Flp "concept" ⨟ "syntaxList" ⊆ "choice"
    , "head2" ⊆ "recogniser"
    , "tail2" ⊆ "continuation"
    -- 'wrong' rule: lists must be infinite (causes infinite loop):
    -- , "tail" ⊆ "tail" ⨟ ("tail" ⨟ Flp "tail" ∩ I) -- TODO: make this terminate by somehow using isomorphisms
    -- TODO: find out whether the order of rules can influence the end-result (apart from termination and fresh-variable-ordering)
    -- not needed:
    -- , Flp "relation" ⨟ "relation" ⊆ I
    -- , Flp "declaration" ⨟ "declaration" ⊆ I
    -- , "syntaxList" ⨟ Flp "syntaxList" ⊆ I
    -- , "concept" ⨟ Flp "concept" ⊆ I
    -- , "declaration" ⨟ Flp "declaration" ⊆ I
    -- , Flp "head" ⨟ "head" ⊆ I
    -- , Flp "tail" ⨟ "tail" ⊆ I
    -- ,   "relationName" ⨟ Flp "relationName" ∩ I ⊆ "declaration" ⨟ Flp "declaration"
    -- ,   "declaration" ⨟ "concepts" ⨟ "fst" ⊆ Flp "head" ⨟ Flp "syntaxLists" ⨟ "concept"
    -- ,   Flp "head" ⨟ Flp "syntaxLists" ⨟ "concept" ⊆ "declaration" ⨟ "concepts" ⨟ "fst"
    -- , "relationName" ⊆ "declaration" ⨟ "relation" ⨟ "string"
    ]
    

