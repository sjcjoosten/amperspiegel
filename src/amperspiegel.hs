{-# OPTIONS_GHC -Wall #-} {-# LANGUAGE BangPatterns, LambdaCase, ApplicativeDo, OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveTraversable, FlexibleInstances, FlexibleContexts #-}
module Main (main) where
import Helpers
import Data.String (IsString)
import Data.Set as Set (toList)
import ParseRulesFromTripleStore(ParseRule(..),tripleStoreRelations,tripleStoreToParseRules,fmap23)
import Tokeniser(showPos,runToken,Token, LinePos,showPos)
import TokenAwareParser(Atom(..),freshTokenSt,parseText,deAtomize,freshenUp,parseListOf)
import ApplyRuleSet(applySystem)
import RuleSetFromTripleStore(ruleSetRelations,tripleStoreToRuleSet)
import qualified Data.Map as Map
import System.IO (stderr)
import System.Exit (exitFailure)
import Data.Monoid
import System.Console.Terminal.Size (size,width)

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
 = TR  { _getPop   :: FullStore
       , popParser :: Maybe FullParser
       , popRules  :: Maybe FullRules}
 | LST { _getList  :: [Triple (Atom Text) (Atom Text)]}

getPop :: Population -> TripleStore (Atom Text) (Atom Text)
getPop (LST a) = foldl' (\v w -> fst (insertTriple w v)) Map.empty a
getPop r = _getPop r

type FullParser = [ParseRule (Atom Text) Text Text]
type FullRules = [Rule (Atom Text) (Atom Text)]
type FullStore = TripleStore (Atom Text) (Atom Text)

doCommand :: Text -> [Text] -> StateT (Map Text Population) IO ()
doCommand cmd
 = Map.findWithDefault
       (\_ -> lift$ finishError ("Not a valid command: "<>cmd<>"\nGet a list of commands using: -h"))
       cmd lkp'
 where lkp' = fmap snd (Map.fromList commands)

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
                               trps <- traverse (parseText (parseListOf (p,"Statement")) showUnexpected) txts
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
                   lift . sequenceA_ . map Helpers.putStrLn . Map.keys
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
 = Helpers.unlines [ showPad w1 n <> ": "<>showPad w2 s<>" |--> "<>showT t
                   | Triple n s t <- getList v]
 where (w1,w2) = foldr max2 (0,0) (getList v)
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
    

