CLASSIFY UnaryExpression ISA Expression
CLASSIFY NullaryExpression ISA Expression
CLASSIFY BinaryExpression ISA Expression
CLASSIFY Relation ISA NullaryExpression
CLASSIFY Identity ISA NullaryExpression
CLASSIFY Universe ISA NullaryExpression
CLASSIFY Composition ISA BinaryExpression
CLASSIFY Intersection ISA BinaryExpression
CLASSIFY Difference ISA BinaryExpression
CLASSIFY Converse ISA UnaryExpression
CLASSIFY BracketedExpression ISA UnaryExpression

-- Built-in: IdentifierString and QuotedString
-- Reason: they will be part of the scanner, which is not specified here

RELATION identifier    [Relation         * IdentifierString]
RELATION identifier    [Concept          * IdentifierString]
RELATION concept       [Identity         * Concept         ]
RELATION concepts      [Universe         * ConceptPair     ]
RELATION fst           [ConceptPair      * Concept         ]
RELATION snd           [ConceptPair      * Concept         ]
RELATION fst           [BinaryExpression * Expression      ]
RELATION snd           [BinaryExpression * Expression      ]
RELATION subExpression [UnaryExpression  * Expression      ]

VIEW Relation = [identifier]
VIEW Concept = [identifier]
VIEW Identity = ["I[",concept,"]"]
VIEW Universe = ["V[",concepts,"]"]
VIEW ConceptPair = [fst,"*",snd]
VIEW BracketedExpression = ["(",subExpression,")"]
VIEW Converse = [subExpression,"~"]
VIEW Intersection = [fst,"/\",snd]
VIEW Difference = [fst,"-",snd]
-- the above implicitly defines a choice-based syntax for the concept Expression: any place an Expression is used, anything that is an expression may also be used

CLASSIFY ClassificationStatement ISA Statement
CLASSIFY DeclarationStatement ISA Statement
CLASSIFY SyntaxStatement ISA Statement

classification :: ClassificationStatement -> Classification
  mainConcept :: Classification -> Concept
  conceptList :: Classification -> ConceptList
  CLASSIFY UnaryConceptList ISA ConceptList
  concept :: UnaryConceptList -> Concept
  CLASSIFY ConsConceptList ISA ConceptList
  head :: ConsConceptList -> Concept
  tail :: ConsConceptList -> ConceptList
  VIEW Classification = ["CLASSIFY",mainConcept,"IS",conceptList]
  -- VIEW Classification = ["CLASSIFY",mainConcept/\(conceptList;head),"ISA",conceptList;tail]
  VIEW ConsConceptList = [head,"/\",tail]
  VIEW UnaryConceptList = [concept]
declaration :: DeclarationStatement -> Declaration
  relation :: Declaration -> Relation
  concepts :: Declaration -> ConceptPair
  CLASSIFY FunctionType ISA ConceptPair
  VIEW FunctionType = [fst,"->",snd]
  VIEW Declaration = [relation,"::",concepts] -- allowing VIEW for ConceptPair, but also for FunctionType
syntax :: SyntaxStatement -> Syntax
  concept :: Syntax -> Concept
  syntaxList :: Syntax -> SyntaxList
  CLASSIFY UnarySyntaxList ISA SyntaxList
  syntaxElement :: UnarySyntaxList -> SyntaxElement
  CLASSIFY ConsSyntaxList ISA SyntaxList
  head :: ConsSyntaxList -> SyntaxElement
  tail :: ConsSyntaxList -> SyntaxList
  VIEW Syntax = ["VIEW",concept,"=","[",syntaxList,"]"]
  VIEW ConsSyntaxList = [head,",",tail]
  CLASSIFY QuotedStringElement ISA SyntaxElement
  string :: QuotedStringElement -> QuotedString
  VIEW QuotedStringElement = [string]
  CLASSIFY ExpressionElement ISA SyntaxElement
  expression :: ExpressionElement -> Expression
  VIEW ExpressionElement = [expression]

VIEW ClassificationStatement = [classification]
VIEW DeclarationStatement = [declaration]
VIEW SyntaxStatement = [syntax]

