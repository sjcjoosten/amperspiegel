{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-} -- for the scanner position
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module ParseToRelations(test) where
import Data.Text.Lazy as Text
import Data.String
import ParseRulesFromTripleStore(ParseRule(..),tripleStoreToParseRules)
import Tokeniser(showPos,runToken)
import TokenAwareParser(Atom,freshTokens,parseText,parseListOf)
import Relations(Rule(..),(⨟),(⊆),(∩),Expression(..),Triple(..),TripleStore)
import ApplyRuleSet(applySystem)
import SimpleHelperMonads
import RuleSetFromTripleStore

test :: String -> FreshnessGenerator
                   ([ParseRule (Atom Text) (Atom Text) (Atom Text)], Atom Text)
test s = fmap runFailingMonad.fmap (tripleStoreToParseRules id =<<).sequenceA
       $ (applySystem' freshTokens ruleList =<<) 
         <$> parseText (parseListOf (mParser::([ParseRule Text Text String], String)))
                       (showPos . fst . runToken) (pack s)
    where applySystem' a b c = applySystem a b c :: FreshnessGenerator (TripleStore Text (Atom Text))

-- ghci-8.0.0.20160421 ParseToRelations.hs -XOverloadedStrings
-- fmap runFailingMonad.fmap (tripleStoreToParseRules id =<<).sequenceA$ (applySystem freshTokens ruleList =<<) <$> parseText' "rel1 :: A * B rel2 :: A * C VIEW A = [rel1] VIEW D = [rel2,\"hi\"] CLASSIFY A IS D"
-- ([ParseRule "A" [Fresh 0 "B"],ParseRule "A" [Fresh 4 "C","\"hi\""],ParseRule "D" [Fresh 4 "C","\"hi\""]],"Statement")

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

ruleList :: (IsString x) => [Rule x]
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
    , "tail" ⊆ "tail" ⨟ ("tail" ⨟ Flp "tail" ∩ I) -- TODO: make this terminate by somehow using isomorphisms
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
    

