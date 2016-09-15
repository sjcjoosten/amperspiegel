-- this is the main file. To be run within ghci
-- ghci-8.0.0.20160421 ParseToRelations.hs -XOverloadedStrings
-- scriptToParser "rel1 :: A * B rel2 :: A * C VIEW A = [rel1] VIEW D = [rel2,\"hi\"] CLASSIFY A IS D"
-- ([ParseRule "A" ["rel1" "B"],ParseRule "A" ["rel2" "C","\"hi\""],ParseRule "D" ["rel2" "C","\"hi\""]],"Statement")

{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-} -- for the scanner position
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module ParseToRelations where
import Data.Text.Lazy as Text
import Data.String
import ParseRulesFromTripleStore(ParseRule(..),tripleStoreToParseRules)
import Tokeniser(showPos,runToken)
import TokenAwareParser(Atom,freshTokens,parseText,parseListOf)
import Relations(Rule(..),(⨟),(⊆),(∩),Expression(..),Triple(..),TripleStore)
import ApplyRuleSet(applySystem)
import SimpleHelperMonads
import RuleSetFromTripleStore
import Control.Monad.Fail
import Data.Map (Map)

scriptToParser' :: String -> FreshnessGenerator
                   ([ParseRule (Atom Text) (Atom Text) (Atom Text)], Atom Text)
scriptToParser' s = fmap runFailingMonad.fmap (tripleStoreToParseRules id =<<).sequenceA $
                   aptSys
                  where aptSys = (fmap fst . applyRules ruleList) <$> parseTextI s

scriptToParser :: String -> FreshnessGenerator
                   (FailingMonad ([ParseRule (Atom Text) (Atom Text) (Atom Text)], Atom Text))
scriptToParser s = fmap (tripleStoreToParseRules id =<<).sequenceA $
                  aptSys
                 where aptSys = (fmap fst . applyRules ruleList) <$> parseTextI s

applyRules :: [Rule Text (Atom Text)] -> FreshnessGenerator [Triple Text (Atom Text)]
           -> FreshnessGenerator (TripleStore Text (Atom Text), Map (Atom Text) (Atom Text))
applyRules r = (applySystem (error "reached contradiction applying rules") freshTokens r =<<)

parseTextI :: MonadFail m =>
              String -> m (FreshnessGenerator [Triple Text (Atom Text)])
parseTextI s = parseText (parseListOf (mParser::([ParseRule Text Text String], String)))
                         (showPos . fst . runToken) (pack s)

mParser :: (IsString x,IsString y,IsString z) => ([ParseRule x y z],z)
mParser
  = ([ParseRule "Classification"  ["CLASSIFY"
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
     ,ParseRule "ConceptList"     ["head" "String"
                                  ,"/\\"
                                  ,"tail" "ConceptList"]
     ,ParseRule "ConceptList"     ["head" "String"]
     ,ParseRule "SyntaxList"      ["head" "SyntaxElement"]
     ,ParseRule "SyntaxList"      ["head" "SyntaxElement"
                                  ,","
                                  ,"tail" "SyntaxList"]
     ,ParseRule "SyntaxElement"   ["qstring" "QuotedString"]
     ,ParseRule "SyntaxElement"   ["relationName" "UnquotedString"]
     ,ParseRule "Statement"       ["classification" "Classification"]
     ,ParseRule "Statement"       ["declaration" "Declaration"]
     ,ParseRule "Statement"       ["syntax" "Syntax"]
     ], "Statement")

ruleList :: (IsString x) => [Rule x y]
ruleList
  = [ "conceptList" ⊆ "conceptLists"
    , "conceptLists" ⨟ "tail" ⊆ "conceptLists"
    , Flp "mainConcept" ⨟ "conceptLists" ⨟ "head" ⊆ "subConcepts"
    , "subConcepts" ⨟ "subConcepts" ⊆ "subConcepts"
    , Flp "mainConcept" ⨟ "mainConcept" ∩ I ⊆ "subConcepts"
    , Flp "concept" ⨟ "concept" ∩ I ⊆ "subConcepts"
    , "syntaxList" ⊆ "syntaxLists"
    , "syntaxList" ⨟ "tail" ⊆ "syntaxLists"
    , "qstring" ⊆ I
    , "relationName" ⊆ I
    , "string" ⨟ Flp "string" ⊆ I -- this rule means every relation has a unique name. Unfortunately, there is no other way to disambiguate declarations.
    , "declaration" ⨟ "relation" ⨟ "string" ⊆ "relationName"
    , "declaration" ⨟ "concepts" ⨟ "snd" ⊆ "nonTerminal"
    , "subConcepts" ⨟ Flp "concept" ⨟ "syntaxList" ⊆ "choice"
    , "head" ⊆ "recogniser"
    , "tail" ⊆ "continuation"
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
    

