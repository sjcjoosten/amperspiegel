-- simplified boot.ASL
-- This should define the initially loaded parser

CLASSIFY ClassificationStatement IS Statement /\ ClassificationStatement
CLASSIFY DeclarationStatement IS Statement /\ DeclarationStatement
CLASSIFY SyntaxStatement IS Statement /\ SyntaxStatement
CLASSIFY ConsConceptList IS ConsConceptList /\ ConceptList -- non-empty list, i.e. ConceptList has a 'head' concept associated
CLASSIFY ConsSyntaxList IS ConsSyntaxList /\ SyntaxList
CLASSIFY QuotedStringElement IS QuotedStringElement /\ SyntaxElement
CLASSIFY RelationElement IS RelationElement /\ SyntaxElement

-- builtin:
-- string :: StringAndOrigin * String
-- origin :: StringAndOrigin * Position
-- CLASSIFY UnquotedString IS UnquotedString /\ String
-- CLASSIFY QuotedString IS QuotedString /\ String

classification :: ClassificationStatement * Classification
  mainConcept :: Classification * String
  conceptList :: Classification * ConceptList
  head1 :: ConceptList * String
  tail1 :: ConsConceptList * ConceptList
declaration :: DeclarationStatement * Declaration
  relation :: Declaration * StringAndOrigin
  concepts :: Declaration * DeclarationType
  fst :: DeclarationType * String
  snd :: DeclarationType * String
syntax :: SyntaxStatement * Syntax
  concept :: Syntax * String
  relationName :: RelationElement * UnquotedString
  syntaxList :: Syntax * SyntaxList
  head2 :: SyntaxList * SyntaxElement
  tail2 :: ConsSyntaxList * SyntaxList
  qstring :: QuotedStringElement * QuotedString

VIEW ClassificationStatement = [classification]
VIEW DeclarationStatement    = [declaration]
VIEW SyntaxStatement         = [syntax]

VIEW Classification      = ["CLASSIFY",mainConcept,"IS",conceptList]
VIEW ConsConceptList     = [head1,"/\\",tail1]
VIEW ConceptList         = [head1]
VIEW DeclarationType     = [fst,"*",snd]
VIEW Declaration         = [relation,"::",concepts]
VIEW Syntax              = ["VIEW",concept,"=","[",syntaxList,"]"]
VIEW ConsSyntaxList      = [head2,",",tail2]
VIEW SyntaxList          = [head2]
VIEW QuotedStringElement = [qstring] -- goes to QuotedString
VIEW RelationElement     = [relationName]

-- For parsing Rules:
CLASSIFY RuleStatement IS Statement /\ RuleStatement
rule :: RuleStatement * RuleSubset
eFst :: TwoExpressionArguments * PreExpression
eSnd :: TwoExpressionArguments * PostExpression
pre  :: PreExpression * UnquotedString -- Stands for a relation
post :: PostExpression * UnquotedString -- Stands for a relation
VIEW RuleStatement = ["RULE",rule]
VIEW RuleSubset = [eFst,"|-",eSnd]
VIEW PreExpression = [pre]
VIEW PostExpression = [post]
