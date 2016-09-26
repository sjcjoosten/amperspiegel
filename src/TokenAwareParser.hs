{-# OPTIONS_GHC -Wall #-} {-# LANGUAGE TypeFamilies, BangPatterns, LambdaCase, ApplicativeDo, OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveTraversable, FlexibleInstances, FlexibleContexts #-}
module TokenAwareParser(Atom(..),parseText,deAtomize,freshTokenSt,freshenUp,parseListOf) where
import Text.Earley
import Control.Applicative
import Control.Monad.Fix
import Data.Foldable
import Data.Text.Lazy (Text)
import Data.Int as Int
import Data.IntMap as IntMap
import Data.Map as Map
import Data.String
import Data.Maybe
import Control.Arrow (first)
import Data.List(intercalate)
import Tokeniser
import ParseRulesFromTripleStore(ParseRule(..),ParseAtom(..),traverseStrings)
import Relations
import Control.Monad.Fail as Fail
import Control.Monad.State

data Atom a
 = UserAtom (Token a)
 | Position Int64 Int64
 | Fresh Int
 deriving (Eq,Ord,Functor)

deAtomize :: (MonadFail m,Show a) => Atom a -> m a
deAtomize (UserAtom v) = pure$ runToken v
deAtomize x = Fail.fail ("Don't know what to do with the atom: "++show x)

freshenUp :: (Monad m)
          => m (Atom y)
          -> [Triple (Atom y) (Atom y)]
          -> m [Triple (Atom y) (Atom y)]
freshenUp fg trs
  = (\fr -> let f = \case{Fresh i -> IntMap.findWithDefault (Fresh 0) i fr;v->v}
            in [Triple (f r) (f a) (f b) | Triple r a b <-trs])
    <$> sequence (IntMap.fromList [ (i,fg) | Triple r a b <-trs
                                           , Fresh i <- [r,a,b] ])

instance Show a => Show (Atom a) where
  show (UserAtom a) = show a
  show (Position r c) = "Position "++show r++" "++show c
  show (Fresh i) = "Fresh "++show i
instance (Scannable a, IsString a) => IsString (Atom a) where
  fromString v = case scanPartitioned id (fromString v) of
       ([v'],LinePos _ _ Success) -> UserAtom (fmap (runLinePos . fst) v')
       _ -> UserAtom (fromString v)

instance IsString (Atom (LinePos Text)) where
  fromString v = UserAtom (fmap (LinePos 0 0) (fromString v))

instance Show y => Show (Triple y (Atom Text)) where
  showList ts = (++) ("makeTriples [" ++ Data.List.intercalate ", " [show (r,a,b) | Triple r a b <- ts] ++ "]")
  show (Triple r a b) = show (r,a,b)

freshTokenSt :: Applicative x => StateT Int x (Atom y)
freshTokenSt = StateT (\i -> pure (Fresh i,i+1))


-- combine an abstract parser with a tokeniser
-- TODO: find a nice way to move some of the functionality from here into the Tokeniser file. The pre-made "String" and "QuotedString" – as well as the way how exactMatch is written – really come across as belonging to the scanner, rather than the parser.
parseListOf :: forall y x z m. (Eq y,Show y,Scannable y,Ord z,IsString z
                               ,IsString x,Show z,Monad m)
            => ([ParseRule x y z], z)
            -> Either y (y -> ( ( [StateT Int m [Triple x (Atom y)]]
                                , Report String [Token (LinePos y, Bool)] )
                              ,LinePos (ScanResult y))
                        )
parseListOf (pg,ps)
 = do pg'<-traverse (traverseStrings stringOp) pg
      Right$ scanPartitioned
            (first (Prelude.map (fmap (fmap (fmap (fmap runLinePos))))) .
             fullParses (parser (readListGrammar exactMatch' [("String",fmap atomToStruct <$> Just)
                                                            ,("QuotedString",fmap atomToStruct <$> ifThenJust isQuoted)
                                                            ,("UnquotedString",fmap atomToStruct <$> ifThenJust isUnquoted)
                                                            ,("StringAndOrigin",getPlace)]
                                                 freshTokenSt
                                                 (\a b c -> [Triple a b c])
                                                 (pg',ps)
                                                 )))
 where
  atomToStruct a = pure (UserAtom (fmap fst a),mempty)
  stringOp v = case partitionedSuccess v of
                 Nothing -> Left v
                 Just x -> Right (v,x)
  getPlace v = Just (do new <- freshTokenSt
                        return (new,[Triple "string" new (UserAtom (fmap fst v))
                                    ,Triple "origin" new . position' . fst . runToken $ v]))
  position' (LinePos r c _) = Position r c

  exactMatch' (b,t) = exactMatch (\a->terminal a <?> "Token "++show b) t
  
  ifThenJust f v = case f v of {True -> Just v;False -> Nothing}

-- Convert something scannable to a set of triples
-- convenient way to use the parser
parseText :: forall y a m b t t1. (MonadFail m, Show y, Show b)
          => Either y (t -> (([a], Report String [t1]), LinePos (ScanResult b)))
          -> (t1 -> String -> Maybe String -> m a) -> t -> m a
parseText parseListOf' showUnexpected t
  = case parseListOf' of
      Left v -> Fail.fail ("Invalid parser. Not a valid token: "++show v)
      Right v -> case v t of{
      (([r] -- returns all possible parses. A succes means there is just one.
       ,Report _
               _  -- tokens that are expected at this point
               [] -- tokens that are left to be scanned
       )
      ,LinePos _ _
               Success -- result of the scanner. When unsuccesful, the succesfully scanned part is still sent to the parser
      ) -> return r;
      ((_
       ,Report _
               e  -- tokens that are expected at this point
               (u:_) -- tokens that are left to be scanned
       )
      ,scanResult -- regardless of the scanner, if there were tokens left to be scanned, the error should be about the unexpected token
      ) -> showUnexpected u (showTokens e)
            $ (showPos id <$> (traverse scanError scanResult));
      ((p,_),scanResult) ->
        Fail.fail
          (fromMaybe ("Ambiguous input:\n"++show (length p)++" possible parses.")
          $ showPos id <$> traverse scanError scanResult)
      }
  where scanError :: (ScanResult b) -> Maybe String
        scanError (Success) = Nothing
        scanError (ExpectClosingComment)
          = Just$ "The opened comment has to be closed by a -}"
        scanError (ExpectClosingQuote)
          = Just$ "The quoted string has to be closed by a \""
        scanError (InvalidChar c)
          = Just$ "Invalid character: "++showPos id (fmap show c)++" in the quoted string"
        
        showTokens :: [String] -> String
        showTokens [] = "end of file"
        showTokens [a] = a
        showTokens [a,b] = a ++" or "++b
        showTokens (h:lst) = h ++ ", "++showTokens lst


-- | Abstract grammar generator. Generates a Earley-grammar for a parserule-list (along with a designated element). Note that this function will never match undefined ParseRules. I.e. ([somesetofrules],notInTheSetOfRules) returns a parser that only matches the empty string
readListGrammar :: forall m a e b c r x y z res.
                (Ord z, Applicative m,Monoid res,e~String,Show z)
                => (x -> Prod r String a b) -- ^ Recognise exactly the token "x"
                -> [(z, a -> Maybe (m (c, res)))] -- ^ Any predefined elements
                -> m c -- ^ will generate a fresh constant of type c
                -> (y -> c -> c -> res) -- ^ the result to produce
                -> ([ParseRule y x z], z)
                -> Grammar r (Prod r String a (m res))
readListGrammar matchToken builtIn getFresh buildFn (grammar,gelem)
 = (\s -> (fmap mconcat <$> (traverse (fmap snd) <$> many s))) <$> statement
 where
   statement :: Grammar r (Prod r e a (m (c,res)))
   statement = fmap (findInMap gelem) (mfix (\res -> foldrM (insRule res) iniMap grammar))
   insRule :: Map z (Prod r e a (m (c, res)))
           -> ParseRule y x z
           -> Map z (Prod r e a (m (c, res)))
           -> Grammar r (Map z (Prod r e a (m (c, res))))
   insRule lookupMp (ParseRule nm lst) mp
     = (\v -> Map.insertWith (<|>) nm v mp) <$> rule (addAsChoice lst)
     where addAsChoice :: [ParseAtom y x z]
             -> Prod r e a (m (c, res))
           addAsChoice atms
             = (insNew . sequenceA <$> traverse atmToProd atms)
           atmToProd :: ParseAtom y x z -> Prod r e a (m (c -> res))
           atmToProd (ParseRef relName ref)
             = r relName (findInMap ref lookupMp)
           atmToProd (ParseString a)
             = matchToken a *> pure (pure (const mempty))
   insNew :: m [c -> res] -> m (c, res)
   insNew l
    = (\new lst' -> (new, mconcat (Prelude.map ($ new) lst')))
      <$> getFresh <*> l
   iniMap :: Map.Map z (Prod r e a (m (c, res)))
   iniMap = Map.fromListWith (<|>) (fmap builtInToProd builtIn)
   builtInToProd (z,f) = (z,terminal f <?> show z)
   r :: y
     -> Prod r e a (m (c, res))
     -> Prod r e a (m (c -> res))
   r w1 x1
    = fmap (\(v1,lst1) -> (\new -> mappend (buildFn w1 new v1) lst1)) <$> x1

    