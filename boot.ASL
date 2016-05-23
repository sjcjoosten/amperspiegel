-- building this should make it possible to parse expressions.ASL

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
  head :: ConceptList * Concept
  tail :: ConsConceptList * ConceptList
declaration :: DeclarationStatement * Declaration
  relation :: Declaration * Relation
  concepts :: Declaration * DeclarationType
  fst :: DeclarationType * Concept
  snd :: DeclarationType * Concept
syntax :: SyntaxStatement * Syntax
  concept :: Syntax * Concept
  syntaxList :: Syntax * SyntaxList
  head :: SyntaxList * SyntaxElement
  tail :: ConsSyntaxList * SyntaxList
  string :: QuotedStringElement * QuotedString

VIEW ClassificationStatement = [classification]
VIEW DeclarationStatement    = [declaration]
VIEW SyntaxStatement         = [syntax]

VIEW Classification      = ["CLASSIFY",mainConcept,"IS",conceptList]
VIEW ConsConceptList     = [head,"/\",tail]
VIEW ConceptList         = [head]
VIEW DeclarationType     = [fst,"*",snd]
VIEW Declaration         = [relation,"::",concepts]
VIEW Syntax              = ["VIEW",concept,"=","[",syntaxList,"]"]
VIEW ConsSyntaxList      = [head,",",tail]
VIEW SyntaxList          = [head]
VIEW QuotedStringElement = [string] -- goes to QuotedString
VIEW RelationElement     = [relation]
