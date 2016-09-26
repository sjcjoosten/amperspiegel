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

-- For parsing Rules, uncomment this section
CLASSIFY RuleStatement IS Statement /\ RuleStatement
CLASSIFY RuleSubset IS TwoExpressionArguments /\ RuleSubset
CLASSIFY Conjunct IS Conjunct /\ TwoExpressionArguments
CLASSIFY Compose IS Compose /\ TwoExpressionArguments
rule :: RuleStatement * RuleSubset
eFst :: TwoExpressionArguments * Expression
eSnd :: TwoExpressionArguments * Expression
conjunct :: Expression * Conjunct
converse :: Expression * Expression
compose :: Expression * Compose
atom :: Expression * UnquotedString -- Stands for a relation
VIEW RuleStatement = ["RULE",rule]
VIEW RuleSubset = [eFst,"|-",eSnd]
VIEW Expression = ["(",conjunct,")"]
VIEW Expression = ["(",compose,")"]
VIEW Expression = [converse,"~"]
VIEW Expression = [atom]
VIEW Expression = ["="]
VIEW Conjunct = [eFst,"/\\",eSnd]
VIEW Compose = [eFst,";",eSnd]