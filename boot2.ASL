-- full boot sequence
-- keep boot.ASL as close to the initial loader as possible
-- use this file to include many features

relationName :: RelationElement * String
identifier :: Concept * String

VIEW Concept = [identifier]

CLASSIFY ClassificationStatement IS Statement /\ ClassificationStatement
CLASSIFY DeclarationStatement IS Statement /\ DeclarationStatement
CLASSIFY SyntaxStatement IS Statement /\ SyntaxStatement
CLASSIFY ConsConceptList IS ConsConceptList /\ ConceptList -- non-empty list, i.e. ConceptList has a 'head' concept associated
CLASSIFY ConsSyntaxList IS ConsSyntaxList /\ SyntaxList
CLASSIFY QuotedStringElement IS QuotedStringElement /\ SyntaxElement
CLASSIFY RelationElement IS RelationElement /\ SyntaxElement
CLASSIFY Relation IS Relation /\ StringAndOrigin

-- builtin:
-- string :: StringAndOrigin * String
-- origin :: StringAndOrigin * Position
-- CLASSIFY UnquotedString IS UnquotedString /\ String
-- CLASSIFY QuotedString IS QuotedString /\ String

classification :: ClassificationStatement * Classification
  mainConcept :: Classification * Concept
  conceptList :: Classification * ConceptList
  head1 :: ConceptList * Concept
  tail1 :: ConsConceptList * ConceptList
declaration :: DeclarationStatement * Declaration
  relation :: Declaration * Relation
  concepts :: Declaration * DeclarationType
  fst :: DeclarationType * Concept
  snd :: DeclarationType * Concept
syntax :: SyntaxStatement * Syntax
  concept :: Syntax * Concept
  syntaxList :: Syntax * SyntaxList
  head2 :: SyntaxList * SyntaxElement
  tail2 :: ConsSyntaxList * SyntaxList
  string :: QuotedStringElement * QuotedString

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
VIEW QuotedStringElement = [string] -- goes to QuotedString
VIEW RelationElement     = [relation]

-- For parsing Rules, uncomment this section

rule :: 
