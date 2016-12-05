{-# OPTIONS_GHC -Wall #-} {-# LANGUAGE TupleSections,RankNTypes, TypeFamilies, BangPatterns, LambdaCase, ApplicativeDo, OverloadedStrings, ScopedTypeVariables, DeriveFunctor, DeriveTraversable, FlexibleInstances, FlexibleContexts #-}
module TokenAwareParser(ParseRule(..),ParseAtom(..),tripleStoreToParseRules,fmap23,Atom(..),freshTokenSt,parseText,deAtomize,deAtomizeString,freshenUp,parseOf,runToken,Token,LinePos,showPos,builtIns,makeQuoted) where
import Text.Earley
import Data.IntMap as IntMap
import Data.Map as Map
import Helpers

data Atom a
 = UserAtom (Token a)
 | Position Int Int
 | Fresh Int
 deriving (Eq,Ord,Functor)

instance Show (TransactionVariable (Atom Text)) where
  show = (\case TransactionPre v    -> "pre "   ++unwrap v
                TransactionDuring v -> "during "++unwrap v
                TransactionPost v   -> "post "  ++unwrap v)
    where unwrap (UserAtom v) = unpack (runToken v)
          unwrap x = show x

makeQuoted :: a -> Atom a
makeQuoted = UserAtom . QuotedString

deAtomize :: Atom a -> Either (Atom a) a
deAtomize (UserAtom v) = pure$ runToken v
deAtomize x = Left x

deAtomizeString :: Atom Text -> Either Text Text
deAtomizeString (UserAtom v)
 = pure$ case v of QuotedString q -> showT q
                   NonQuoted _ o -> o
deAtomizeString (Position r c) = Left$ "Position "<>showT r<>" "<>showT c
deAtomizeString (Fresh i) = Left$"Fresh "<>showT i

freshenUp :: (Applicative m)
          => m (Atom y)
          -> [Triple (Atom y) (Atom y)]
          -> m [Triple (Atom y) (Atom y)]
freshenUp fg trs
  = (\fr -> let f = \case{Fresh i -> IntMap.findWithDefault (Fresh 0) i fr;v->v}
            in [Triple (f r) (f a) (f b) | Triple r a b <-trs])
    <$> sequenceA (IntMap.fromList [ (i,fg) | Triple r a b <-trs
                                           , Fresh i <- [r,a,b] ])

instance Show (Atom Text) where
  show = unpack . either id (showT . unpack) . deAtomizeString 
instance (Scannable a, IsString a) => IsString (Atom a) where
  fromString v = case scanPartitioned id (fromString v) of
       ([v'],LinePos _ _ Success) -> UserAtom (fmap (runLinePos . fst) v')
       _ -> UserAtom (fromString v)        
instance (Scannable a, IsString a) => IsString (Token a) where
  fromString v = case scanPartitioned id (fromString v) of
       ([v'],LinePos _ _ Success) -> (fmap (runLinePos . fst) v')
       _ -> QuotedString (fromString v)

freshTokenSt :: Applicative x => StateT Int x (Atom y)
freshTokenSt = StateT (\i -> pure (Fresh i,i+1))

-- combine an abstract parser with a tokeniser
parseOf :: forall y x z m. (Eq y,Show y,Scannable y,Ord z
                           ,Show z,Monad m)
        => [(z, Token (LinePos y, Bool) -> Maybe (StateT Int m (Atom (LinePos y), [Triple x (Atom (LinePos y))])))]
        -> ([ParseRule x y z], z)
        -> Either y (y -> ( ( [StateT Int m [Triple x (Atom y)]]
                            , Report Text [Token (LinePos y, Bool)] )
                          ,LinePos (ScanResult y))
                    )
parseOf bi (pg,ps)
 = do pg'<-traverse (traverseStrings stringOp) pg
      Right$ scanPartitioned
            (first (Prelude.map (fmap (fmap (fmap (fmap runLinePos))))) .
             fullParses (parser (readGrammar showT exactMatch' bi freshTokenSt (\a b c -> [Triple a b c]) (pg',ps))))
 where
  stringOp !v
    = case scan (LinePos 0 0 v) of
          (!r,LinePos _ _ Success) -> Right (v,Prelude.map (fmap (first runLinePos))
                                    (partitionTokens False r))
          _ -> Left v
  exactMatch' (b,t) = exactMatch (\a->terminal a <?> "Token "<>showT b) t

builtIns :: (IsString x, IsString y, Applicative m)
         => [(x, Token (LinePos s, Bool) -> Maybe
                             (StateT Int m (Atom (LinePos s), [Triple y (Atom (LinePos s))])))]
builtIns
 = [("String",fmap atomToStruct . Just)
   ,("QuotedString",fmap atomToStruct . ifThenJust isQuoted)
   ,("UnquotedString",fmap atomToStruct . ifThenJust isUnquoted)
   ,("StringAndOrigin",(\v -> Just (
      (\new -> (new,[Triple "string" new (UserAtom (fmap fst v))
                    ,Triple "origin" new . position' . fst . runToken $ v])) <$> freshTokenSt)))]
 where
  atomToStruct a = StateT (\i -> pure ((UserAtom (fmap fst a),mempty),i))
  position' (LinePos r c _) = Position r c

-- Convert something scannable to a set of triples
-- convenient way to use the parser
parseText :: forall y a b t t1. (Show y)
          => (b -> Text) -> Either y (t -> (([a], Report Text [t1]), LinePos (ScanResult b)))
          -> (Maybe t1 -> Text -> Maybe Text -> Either Text a) -> t -> Either Text a
parseText showC parseOf' showUnexpected t
  = case parseOf' of
      Left v -> Left ("Invalid parser. Not a valid token: "<>showT v)
      Right v -> case v t of{
      ( ( [r] -- returns all possible parses. A succes means there is just one.
        , Report _ _ []) -- no tokens are left to be scanned
      , LinePos _ _ Success -- result of the scanner. When unsuccesful, the succesfully scanned part is still sent to the parser
      ) -> return r;
      (([], Report _ e r) -- expected: e, found: u
      ,scanResult -- regardless of the scanner, if there were tokens left to be scanned, the error should be about the unexpected token
      ) -> showUnexpected (listToMaybe r) (showTokens e) $ (showPos id <$> (traverse scanError scanResult));
      ((p,_),scanResult) ->
        Left (fromMaybe ("Ambiguous input:\n"<>showT (length p)<>" possible parses.")
          $ showPos id <$> traverse scanError scanResult)
      }
  where scanError :: (ScanResult b) -> Maybe Text
        scanError (Success) = Nothing
        scanError (ExpectClosingComment)
          = Just$ "The opened comment {- has to be closed by a -}"
        scanError (ExpectClosingQuote)
          = Just$ "The quoted string has to be closed by a \""
        scanError (InvalidChar c)
          = Just$ "Invalid character: "<>showPos id (fmap showC c)<>" in the quoted string"
        
        showTokens :: [Text] -> Text
        showTokens [] = "end of file"
        showTokens [a] = a
        showTokens [a,b] = a <>" or "<>b
        showTokens (h:lst) = h <> ", " <> showTokens lst

-- | Abstract grammar generator. Generates a Earley-grammar for a parserule-list (along with a designated element). Note that this function will never match undefined ParseRules. I.e. ([somesetofrules],notInTheSetOfRules) returns a parser that only matches the empty string
readGrammar :: forall m a e b c r x y z res.
            (Ord z, Applicative m, Monoid res)
            => (z -> e)
            -> (x -> Prod r e a b) -- ^ Recognise exactly the token "x"
            -> [(z, a -> Maybe (m (c, res)))] -- ^ Any predefined elements
            -> m c -- ^ will generate a fresh constant of type c
            -> (y -> c -> c -> res) -- ^ the result to produce
            -> ([ParseRule y x z], z)
            -> Grammar r (Prod r e a (m res))
readGrammar shw matchToken builtIn getFresh buildFn (grammar,gelem)
 = fmap (fmap snd) <$> statement
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
           atmToProd (ParseRef relName ref _)
             = r relName (findInMap ref lookupMp)
           atmToProd (ParseString a)
             = matchToken a *> pure (pure (const mempty))
   insNew :: m [c -> res] -> m (c, res)
   insNew l
    = (\new lst' -> (new, mconcat (Prelude.map ($ new) lst')))
      <$> getFresh <*> l
   iniMap :: Map.Map z (Prod r e a (m (c, res)))
   iniMap = Map.fromListWith (<|>) (fmap builtInToProd builtIn)
   builtInToProd :: (z, t -> Maybe a1) -> (z, Prod r1 e t a1)
   builtInToProd (z,f) = (z, terminal f <?> shw z)
   r :: y -> Prod r e a (m (c, res)) -> Prod r e a (m (c -> res))
   r w1 x1
    = fmap (\(v1,lst1) -> (\new -> mappend (buildFn w1 new v1) lst1)) <$> x1

-- A grammar
data ParseRule a b refId = ParseRule refId [ParseAtom a b refId] deriving (Functor,Foldable,Traversable,Show)-- concatenation of strings
data ParseAtom a b refId = ParseString b | ParseRef a refId (Maybe b) deriving (Functor,Foldable,Traversable)

{-
fmap12 :: Applicative m => (t1 -> m a) -> (t -> m b) -> ParseRule t1 t refId -> m (ParseRule a b refId)
fmap12 f1 f2 (ParseRule r lst) = ParseRule r <$> (traverse (fmap12' f1 f2) lst)
fmap12' :: Applicative m => (t1 -> m a) -> (t -> m b) -> ParseAtom t1 t refId -> m (ParseAtom a b refId)
fmap12' _ f2 (ParseString b) = ParseString <$> f2 b
fmap12' f1 _ (ParseRef a rid) = flip ParseRef rid <$> (f1 a)
fmap13 :: Applicative m => (t1 -> m a) -> (refId -> m b) -> ParseRule t1 t refId -> m (ParseRule a t b)
fmap13 f1 f3 (ParseRule r lst) = ParseRule <$> f3 r <*> traverse (fmap13' f1 f3) lst
fmap13' :: Applicative f => (t -> f a) -> (t1 -> f refId) -> ParseAtom t b t1 -> f (ParseAtom a b refId)
fmap13' _ _ (ParseString b) = pure (ParseString b)
fmap13' f1 f3 (ParseRef a rid) = ParseRef <$> f1 a <*> f3 rid -}
fmap23 :: Applicative m => (t -> m a) -> (refId -> m b) -> ParseRule t1 t refId -> m (ParseRule t1 a b)
fmap23 f2 f3 (ParseRule r lst) = ParseRule <$> f3 r <*> traverse (fmap23' f2 f3) lst
fmap23' :: Applicative f => (t -> f b) -> (t1 -> f refId) -> ParseAtom a t t1 -> f (ParseAtom a b refId)
fmap23' f2 _ (ParseString b) = ParseString <$> f2 b
fmap23' f2 f3 (ParseRef a rid b) = ParseRef a <$> f3 rid <*> traverse f2 b

instance (Show a,Show b,Show refId) => Show (ParseAtom a b refId) where
  show (ParseString b) = show b
  show (ParseRef a refId _) = show a ++ " " ++ show refId

instance IsString b => IsString (ParseAtom a b c) where
  fromString = ParseString . fromString
instance ( string ~ String -- delay the conversion to a and force it to be a String here still, to avoid having to write a type: Ambiguous type variable ‘t0’ arising from the literal ‘"firstString"’ prevents the constraint ‘(IsString (t0 -> ParseAtom Text Text Text))’ from being solved
         , IsString a, IsString c)
      => IsString (string -> ParseAtom a b c) where
  fromString s = (\v -> ParseRef (fromString s) v Nothing) . fromString

traverseStrings :: Applicative f => (a -> f b) -> ParseRule x a z -> f (ParseRule x b z)
traverseStrings f (ParseRule r lst)
 = ParseRule r <$> traverse (traverseString f) lst

traverseString :: Applicative f => (a -> f b) -> ParseAtom x a z -> f (ParseAtom x b z)
traverseString f (ParseString a) = ParseString <$> f a
traverseString f (ParseRef x i b) = ParseRef x i <$> traverse f b

-- tripleStoreToParseRules takes a triple store that describes a parser, and turns it into the set of parserules that can be turned into a parser by parseListOf or readListGrammar
-- Requires the following relations:
  -- choice :: ParseRule*Expansion
  -- continuation :: Expansion*Expansion [UNI]
  -- recogniser :: Expension*Element [UNI]
  -- nonTerminal :: Reference*ParseRule [UNI,TOT]
  -- Reference ISA Element, String ISA Element
-- Requirements are cardinality constraints plus:
  -- I[Element] = I[Reference] (+) I[String]
  -- where (+) denotes the disjoint sum
-- The atom 'Statement' is returned as the thing to be parsed.
-- For [ParseRule x y z], we have: x ~ Reference, y ~ String, z ~ ParseRule
-- It makes sense for a list to satisfy the following (not-required):
--  recogniser;V = continuation;V[Expansion*ONE]
-- Totality of nonTerminal is used as a test between x and y.
  -- Consequently, anything other than x which may be an ELEMENT will be treated as an y.
  -- Additionally, anything used to describe the final relation (i.e. anything in x) will not be usable as an y.
  -- In other words: it is your own responsibility that the intersection of x and y is empty. This is why we require I[Element] = I[Reference] (+) I[String]
-- TODO: write this function in an &-INTERFACE-like syntax
tripleStoreToParseRules :: forall z v m y. ( Applicative m, IsString y, Ord v, Ord y)
                    => (forall x. Text -> m x) -> (v -> m z) -> TripleStore y v -> m [ParseRule z z z]
tripleStoreToParseRules fl transAtom ts
 = do r<-fA "choice" makeParseRule
      return r
 where
   fA :: y -> ((v,v) -> m (ParseRule z z z)) -> m [ParseRule z z z]
   fA c f = traversePair f (getRel ts c)
   traversePair :: ((v, v)    -> m (ParseRule z z z))
                -> [(v, [v])] -> m [ParseRule z z z]
   traversePair _ [] = pure []
   traversePair f ((src',tgts):as) = (++) <$> sequenceA [f (src', tgt') | tgt'<-tgts]
                                          <*> traversePair f as
   makeParseRule :: (v, v) -> m (ParseRule z z z)
   makeParseRule (s,t) = ParseRule <$> transAtom s <*> makeList t
   forOON :: String -> v -> (v -> m x) -> m x -> m x
   forOON a = forOneOrNone (fl$ "too many "<>fromString a<>"s") ts (fromString a)
   makeList :: v -> m [ParseAtom z z z]
   makeList cl
        = forOON "recogniser" cl (fmap (:) . makeAtom) (pure id) <*>
          forOON "continuation" cl makeList (pure [])
   makeAtom :: v -> m (ParseAtom z z z)
   makeAtom atm = forOON "nonTerminal" atm (makeRef atm) (makeString atm)
   makeRef atm v = ParseRef <$> transAtom atm <*> transAtom v <*> forOON "separator" atm (fmap Just . transAtom) (pure Nothing)
   makeString atm = ParseString <$> transAtom atm


-- Tokenizer.
-- We want expressions like "3+-4" to be interpretable as "(+) 3 (- 4)",
-- but also as "(+-) 3 4".
-- This can be achieved by turning "3+-4" into four separate tokens.
-- The mixfix operation +- then has an empty-only place between the + and the -.
-- Parsing "3+ -4" could not result in a match on the mixfix,
-- since we disallow the space between + and - in the parser.
-- 
-- On the other hand, we keep potential (unquoted) variable-names together,
-- so something like 4ab3_X_ is ONLY interpretable as a single token.
-- Consequently, a token can be:
-- # A single character not in the set [A-Za-z0-9_]
-- # A sequence of characters from the set [A-Za-z0-9_]
-- To allow for fancy texts, we distinguish two special token-cases:
-- # Quoted strings following Haskell conventions,
--   i.e. "strings that may have \"quotes\" inside like this string".
-- # LaTeX compatible strings,
--   which are strings starting with \ followed by any sequence of characters,
--   except for those characters in the String "[]{}()<>,;.\\ \t\r\n"
--   (i.e. the most common token-ending characters).
--   Note that the allowed characters are not necessarily valid in LaTeX
-- Any string can be tokenised as a single Quoted string,
--   though not every string can be tokenised as a LaTeX string.
-- We also allow for comments:
-- # Nested comments using {- this -} Haskell-syntax
--   (no mandatory whitespace before/after the - sign, but recommended)
-- # comments to the end of line, again haskell-like
--   (no mandatory whitespace after the --, but recommended)
-- We keep whitespace in our first parse, which makes for seven kinds of pre-tokens in total:

data PreToken a = SingleCharacter a
                | CharacterSequence a
                | QuotedString_Pre a -- characters like " no longer escaped
                | LaTeXString a
                | MultiLineComment [a]
                | EndOfLineComment a
                | WhiteSpace a
                deriving (Show,Functor,Eq,Ord)
-- PreToken allows us to easily reconstruct the original source,
-- but all the supporting characters are still required

data LinePos a = LinePos {_line :: !Int, _col :: !Int, runLinePos:: !a}
                 deriving (Functor,Ord,Eq, Foldable, Traversable)

-- LaTeX-style tokens always start with a \, so they do not overlap with the other set of tokens.
-- Quoted strings are parsed without their first and final quote and get a separate constructor.
-- This gives us two kinds of tokens:

data Token a = QuotedString {runToken::a} | NonQuoted {_pre::PreToken a,runToken::a}
             deriving (Eq, Ord, Functor)

exactMatch :: forall t y. (Eq y, Alternative t)
           => (forall v. (Token (LinePos y, Bool) -> Maybe v) -> t v)
           -> [Token (y, Bool)] -> t [Token (LinePos y)]
exactMatch end mpt = go mpt
    where
      go :: [Token (y, Bool)] -> t [Token (LinePos y)]
      go [NonQuoted _ (a',b)] = m b (\v' -> [v']) a'
      go (NonQuoted _ (a',b) : as)
        = m b (\v' -> (:) v') a' <*> go as
      go _ = Helpers.empty -- Invalid token / no match!
      m :: Bool -> (Token (LinePos y) -> a) -> y -> t a
      m b' f a'
        = end (\case NonQuoted p (v,b) | runLinePos v == a' && (not b' || b)
                       -> Just (f (NonQuoted (fmap fst p) v))
                     _ -> Nothing)

isQuoted :: Token t -> Bool
isQuoted QuotedString{} = True
isQuoted NonQuoted{} = False
isUnquoted :: Token t -> Bool
isUnquoted s
  = case tokenToPreToken s of
      CharacterSequence _ -> True
      _ -> False

data NonParsed a = MultiLine [a] | EndOfLine a | NPspace a
data ScanResult a = Success | ExpectClosingComment | ExpectClosingQuote
                  | InvalidChar (LinePos a) deriving (Functor)

class Scannable a where
  scan :: LinePos a -> ([LinePos (PreToken a)],LinePos (ScanResult a))

splitPreToken :: PreToken a -> Either (Token a) (NonParsed a)
splitPreToken o = case o of
   SingleCharacter a   -> Left (NonQuoted o a)
   CharacterSequence a -> Left (NonQuoted o a)
   QuotedString_Pre a  -> Left (QuotedString a)
   LaTeXString a       -> Left (NonQuoted o a)
   MultiLineComment lst -> Right (MultiLine lst)
   EndOfLineComment a   -> Right (EndOfLine a)
   WhiteSpace a -> Right (NPspace a)
tokenToPreToken :: Token a -> PreToken a
tokenToPreToken (QuotedString a) = QuotedString_Pre a
tokenToPreToken (NonQuoted o _) = o

instance Scannable Text where
  scan (LinePos lineNr colNr !p)
   | tnull p = done Success
   | otherwise
     = let !h = Helpers.head p
           c = cont (SingleCharacter (Helpers.take 1 p))
                      (LinePos lineNr (colNr+1) (Helpers.drop 1 p)) in
        if isSpace h then simple (Helpers.span isSpace p) WhiteSpace else
        if h == '-' then (if isPrefixOf "--" p then
                          simple (Helpers.break ((==) '\n') p)
                                (EndOfLineComment . Helpers.drop 2) else c) else
        if isSeqChar h then simple (Helpers.span isSeqChar p) CharacterSequence else
        if h == '"' then case completeQuoted lineNr (colNr + 1)
                                             "" (Helpers.tail p) of
                              Left e -> done e
                              Right (!h',!t) -> cont (QuotedString_Pre h') t else
        if h == '{' then (if isPrefixOf "{-" p then 
                         case completeComment 2 1 p (Helpers.drop 2 p) of
                           Nothing -> done ExpectClosingComment
                           Just (h',t) -> simple (h',t) mlc else c) else
        if h == '\\' then (let isSep v = elem v sepChars
                               sepChars :: String
                               sepChars = "[]{}()<>,;:.\\ \t\r\n"
                               (!h',!t) = Helpers.break isSep (Helpers.tail p)
                           in cont (LaTeXString (mappend (Helpers.take 1 p) h'))
                                   (incrPos (LinePos lineNr (colNr+1) t) h'))
        else c
   where done e = ([],LinePos lineNr colNr e)
         isSeqChar !c = isAlphaNum c || c == '-' || c == ':' || c == '_'
         cont !r !newTail = let (!scanTail,!scanRest) = scan newTail
                              in (LinePos lineNr colNr r:scanTail, scanRest)
         simple (!h,!t) f = cont (f h) (incrPos (LinePos lineNr colNr t) h)
         mlc = MultiLineComment . Helpers.lines . Helpers.drop 2 . dropEnd 2
         completeComment :: Int -> Int -> Text -> Text -> Maybe (Text, Text)
         completeComment !pos' 0 !str _ = Just (Helpers.splitAt (fromIntegral pos') str)
         completeComment !pos' !lvl !str !remainder
           | tnull remainder = Nothing -- expecting closing comment - }
           | otherwise = let (h,t) = Helpers.break ((==) '-') remainder
              in case (isSuffixOf "{" h,stripPrefix "-}" t) of
                 (True,_) -> completeComment (pos'+tlength h+1)
                                             (lvl+1) str (Helpers.drop 1 t)
                 (_,Just r)->completeComment (pos'+tlength h+2)
                                             (lvl-1) str r
                 (_,_)    -> completeComment (pos'+tlength h+1)
                                             lvl str (Helpers.drop 1 t)
         completeQuoted !l !c res remainder
           = let (!h,!t) = Helpers.break (\ !v -> v == '\\' || v == '"'
                                               || v == '\n') remainder
                 !c' = c + (tlength h)
              in case (tnull t,Helpers.head t) of
                  (False,'"') -> Right (mappend res h,LinePos l (c'+1) (Helpers.tail t))
                  (False,'\\')
                   -> let truncT = Helpers.take 9 t in
                      case readLitChar (unpack truncT) of -- \NUL is the longest possible string (or one of them), which is why we can take 4. Truncating is probably asymptotically faster: even though unpack produces a lazy 'rest', we still need to get the length of 'rest' to calculate 'siz'. Note that we cannot get the length of r, since '\^C'='\ETX', and there are more characters like that
                        [(r,rest)]
                         -> let siz = tlength truncT - Prelude.length rest
                            in completeQuoted l (c'+siz)
                                                (mappend res (snoc h r))
                                                (Helpers.drop (fromIntegral siz) t)
                        _ -> Left (InvalidChar (LinePos l c' truncT))
                  _ -> Left ExpectClosingQuote -- expecting closing quote

incrPos :: forall a. LinePos a -> Text -> LinePos a
incrPos orig@(LinePos l p' v) ps
  = case Helpers.split (=='\n') ps of
     [] -> orig
     [r] -> LinePos l (p' + tlength r) v
     o -> LinePos (l + fromIntegral (Prelude.length o) - 1)
                  (tlength (Prelude.last o)) v

partitionTokens :: Bool -> [LinePos (PreToken a)] -> [Token (LinePos a, Bool)]
partitionTokens b (LinePos i j a:as)
 = case splitPreToken a of
     Left v -> fmap (\v' -> (LinePos i j v',b)) v:partitionTokens True as
     Right _ -> partitionTokens False as
partitionTokens _ [] = []

scanPartitioned :: Scannable a
                => ([Token (LinePos a, Bool)] -> t)
                -> a -> (t, LinePos (ScanResult a))
scanPartitioned f inp
 = (f (partitionTokens False scanned),scanResult)
 where
    (scanned,scanResult) = scan (LinePos 0 0 inp)

showPos :: (IsString x,Monoid x) => (a->x)-> LinePos a -> x
showPos s (LinePos r c a) = s a <> " on " <> (fromString$ show (r+1)) <> ":" <> (fromString$ show (c+1))
