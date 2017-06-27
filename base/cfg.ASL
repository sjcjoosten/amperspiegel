start :: Start * Choice
more :: Start * Start
choice :: Choice * Continuation
continuation :: Continuation * Continuation
recogniser :: Continuation * Recogniser
nonTerminal :: Recogniser * UnquotedString
sameTerminal :: Recogniser * UnquotedString
UnquotedString :: X * UnquotedString
QuotedString :: X * QuotedString
recRelation :: Recogniser * UnquotedString
separator :: Recogniser * QuotedString

VIEW Statement    = [start]
VIEW Choice       = [UnquotedString, ">", choice]
VIEW Continuation = [recogniser, continuation]
VIEW Continuation = ["."]
VIEW Recogniser   = [QuotedString]
VIEW Recogniser   = [sameTerminal]
VIEW Recogniser   = ["[",recRelation,"]",nonTerminal]
VIEW Recogniser   = ["[",recRelation,"SEPBY",separator,"]",nonTerminal]

RULE pre UnquotedString |- I
RULE pre QuotedString |- I
RULE pre sameTerminal |- I
RULE pre sameTerminal |- pre nonTerminal
RULE pre recRelation |- I

UnquotedString :: X * UnquotedString
QuotedString :: X * QuotedString

CLASSIFY KeepStatement IS Statement /\ KeepStatement
CLASSIFY RuleStatement IS Statement /\ RuleStatement
CLASSIFY RuleSubset IS TwoExpressionArguments /\ RuleSubset
CLASSIFY Conjunct IS Conjunct /\ TwoExpressionArguments
CLASSIFY Compose IS Compose /\ TwoExpressionArguments
CLASSIFY PreExpression IS PreExpression /\ UnaryExpression
CLASSIFY UnaryExpression IS Expression /\ UnaryExpression
I :: PreExpression * Expression -- for parsing brackets
RULE pre I |- I

rule     :: RuleStatement * RuleSubset
eFst     :: TwoExpressionArguments * Expression
eSnd     :: TwoExpressionArguments * UnaryExpression
conjunct :: Expression * Conjunct
converse :: Expression * PreExpression
compose  :: Expression * Compose
pre      :: Expression * UnquotedString -- Stands for a relation
post     :: Expression * UnquotedString -- Stands for a relation
during   :: Expression * UnquotedString -- Stands for a relation
pair1    :: Expression * String -- Stands for an atom
pair2    :: Expression * String -- Stands for an atom
keep     :: KeepStatement * UnquotedString
pair     :: Expression * String -- Stands for both atoms
toPair   :: Expression * String -- Stands for both atoms
mapsTo   :: Expression * Expression
relaxSnd :: Expression * Expression

RULE pre mapsTo |- (post conjunct;(post eFst;(post compose;(post eFst /\ ((post eSnd;post compose);(post eSnd;post converse))))))
RULE pre toPair |- (post conjunct;((post eFst;((((post compose;post eSnd);post compose);post eFst);pre pair)) /\ post eSnd))
RULE (post compose ~ ; post compose) |- I -- compose is univalent
RULE (post conjunct ~ ; post conjunct) |- I -- conjunct is univalent
RULE (post eFst ~ ; post eFst) |- I -- eFst is univalent
RULE (post eSnd ~ ; post eSnd) |- I -- eSnd is univalent
RULE pre pair |- (post pair1 /\ post pair2)
RULE pre relaxSnd |- pre eSnd

RULE pre keep |- (post rule;((post eFst;post pre) /\ (post eSnd;post post)))
VIEW RuleStatement = ["RULE",rule]
VIEW RuleSubset = [eFst,"|-",relaxSnd]
VIEW PreExpression = ["(",I,")"]
VIEW Expression = [conjunct]
VIEW Expression = [compose]
VIEW UnaryExpression = [converse,"~"]
VIEW PreExpression = ["pre", pre]
VIEW PreExpression = ["post", post]
VIEW PreExpression = ["during", during]
VIEW PreExpression = ["[",mapsTo,"->",toPair,"]"]
VIEW UnaryExpression = ["<",pair1,",",pair2,">"]
VIEW UnaryExpression = ["<",pair,">"]
VIEW UnaryExpression = ["I"]
VIEW Conjunct = [eFst,"/\\",eSnd]
VIEW Compose = [eFst,";",eSnd]
VIEW KeepStatement = ["KEEP",keep]
