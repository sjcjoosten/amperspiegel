{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns, LambdaCase #-} -- for the scanner position
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module Main (main) where
import Data.Text.Lazy (Text,pack,unpack)
import qualified Data.Text.Lazy as Text
import Data.Text.Lazy.IO as Text (readFile,hPutStrLn,putStrLn)
import Data.String (IsString)
import Data.Set as Set (toList)
import ParseRulesFromTripleStore(ParseRule(..),tripleStoreToParseRules,fmap23,tripleStoreRelations)
import Tokeniser(showPos,runToken,Token, LinePos,showPos)
import TokenAwareParser(Atom,freshTokenSt,parseText,parseListOf,deAtomize)
import Relations(Rule(..),(⨟),(⊆),(∩),Expression(..),Triple(..),TripleStore,insertTriple,restrictTo,unionTS)
import ApplyRuleSet(applySystem)
import SimpleHelperMonads(FreshnessGenerator,runFg)
import RuleSetFromTripleStore(ruleSetRelations,tripleStoreToRuleSet)
import Data.Map (Map)
import qualified Data.Map as Map
import System.Environment
import Data.Foldable
import Control.Monad.State
import System.IO (stderr)
import System.Exit (exitFailure)
import Data.Monoid

initialstate :: Map Text Population
initialstate
  = Map.fromList
    [ ( "parser"
      , TR (error "default parser not bootstrapped yet (TODO)") (Just mParser) (Just []))
    , ( "asParser"
      , TR (error "default parse-ruleset not bootstrapped yet (TODO)") (Just []) (Just ruleList))
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
 = TR {_getPop::TripleStore (Atom Text) (Atom Text)
      ,popParser :: Maybe FullParser
      ,popRules :: Maybe FullRules}
 | LST {_getList::[Triple (Atom Text) (Atom Text)]}

getPop :: Population -> TripleStore (Atom Text) (Atom Text)
getPop (LST a) = foldl' (\v w -> fst (insertTriple w v)) Map.empty a
getPop r = _getPop r

type FullParser 
  = [ParseRule (Atom Text) Text Text]
type FullRules
  = [Rule (Atom Text) (Atom Text)]

doCommand :: Text -> [Text] -> StateT (Map Text Population) IO ()
doCommand cmd
 = Map.findWithDefault
       (\_ -> lift$ finishError ("Not a valid command: "<>cmd<>"\nGet a list of commands using: -h"))
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

commands :: [ ( Text
                , ( Text
                  , [Text]
                     -> StateT (Map Text (Population))
                               IO ()
                  ) ) ]
commands = [ ( "i"
             , ( "parse file as input"
               , (\files -> do txts <- lift$ mapM (Text.readFile . unpack) files
                               p <- getParser "parser"
                               r <- getRules "rules"
                               trps <- combinePops <$> (traverse (parseText (parseListOf (p,"Statement")) showUnexpected) txts)
                               res <- evalStateT (applySystem
                                        (liftIO$finishError "Error occurred in applying rule-set: rules & data lead to an inconsistency.")
                                        freshTokenSt r trps) 0
                               overwrite "population" (TR (fst res) Nothing Nothing)
                               return ()
                               )))
           , ( "h"
             , ( "display this help"
               , \_ -> lift$ Text.putStrLn helpText))
           , ( "list"
             , ( "show a list of all triple-stores"
               , noArgs "list"$
                   lift . sequenceA_ . map Text.putStrLn . Map.keys
                     =<< get
               ))
           , ( "show"
             , ( "display the triples as a list"
               , eachPop (lift . Text.putStrLn . prettyPPopulation)))
           , ( "showP"
             , ( "display the triples as a set of parse-rules"
               , eachDo (lift . Text.putStrLn . prettyPParser) getParser))
           , ( "showR"
             , ( "display the triples as a set of parse-rules"
               , eachDo (lift . Text.putStrLn . prettyPRules) getRules))
           , ( "count"
             , ( "count the number of triples"
               , eachPop (lift . Prelude.putStrLn . show . length . getList)))
           , ( "asParser"
             , ( "turn the population into the parser for -i"
               , noArgs "asParser" $
                 do pop <- retrieve "population"
                    -- trans <- retrieve "asParser" TODO
                    r <- getRules "asParser"
                    res <- evalStateT (applySystem (liftIO$finishError "Error occurred in applying rule-set: rules & data lead to an inconsistency.") freshTokenSt r (getList pop)) 0 -- TODO: apply a filter
                    let res' = fst res
                    let parser = restrictTo tripleStoreRelations res'
                    let rules = restrictTo ruleSetRelations res'
                    overwrite "parser" (TR parser Nothing Nothing)
                    overwrite "rules" (TR rules Nothing Nothing)
                    overwrite "population" (TR (unionTS res' rules) Nothing Nothing)
               ))
           ]
           where
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
             helpText
              = "These are the switches you can use:\n\n" <>
                   mconcat [ "  " <> pad maxw s <> "  " <> d <>"\n"
                           | (s,(d,_)) <- commands]
              where
                maxw :: Int
                maxw = fromIntegral$foldr max 0
                         (map (Text.length . fst) commands)

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

prettyPRules :: FullRules -> Text
prettyPRules = mconcat . map (\v -> pack (show v) <> "\n")

prettyPPopulation :: Population -> Text
prettyPPopulation v
 = Text.unlines [ showPad w1 n <> ": "<>showPad w2 s<>" |--> "<>pack (show t)
                | Triple n s t <- getList v]
 where (w1,w2) = foldr max2 (0,0) (getList v)
       max2 (Triple a b _) (al,bl)
         = (max al (length (show a)), max bl (length (show b)))
showPad :: forall a. Show a => Int -> a -> Text
showPad w = pad w . pack . show
pad :: Int -> Text -> Text
pad w s
 = let x = w - (fromIntegral . Text.length) s
   in s <> pack (take x (repeat ' '))

getList :: Population -> [Triple (Atom Text) (Atom Text)]
getList (LST v) = v
getList x = concat . map getTripls . Map.toList $ getPop x
  where getTripls (a,(mp,_))
          = [(Triple nm a b) | (nm,bs) <- Map.toList mp, b<-Set.toList bs]

combinePops :: [FreshnessGenerator [Triple (Atom Text) (Atom Text)]]
            -> [Triple (Atom Text) (Atom Text)]
combinePops = concat . snd . ($0) . runFg . sequence

add :: Monad b => Text -> Population -> StateT (Map Text Population) b ()
add s p = modify (Map.insertWith extend s p)
  where extend _ (LST _) = p
        extend _ (TR po pa ru)
          = TR po
               (case popParser p of {Nothing -> pa; v -> v})
               (case popRules p of {Nothing -> ru; v -> v})

overwrite :: Monad b => Text -> Population -> StateT (Map Text Population) b ()
overwrite s p = modify (Map.insert s p)

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
        (TR{popParser = Just v}) -> return v
        v' -> let v = getPop v' in putBack v =<< (unAtomize =<< tripleStoreToParseRules id v)
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
    

