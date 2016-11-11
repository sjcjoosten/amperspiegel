start :: Start * Choice
more :: Start * Start
choice :: Choice * Continuation
continuation :: Continuation * Continuation
recogniser :: Continuation * Recogniser
nonTerminal :: Recogniser * UnquotedString
UnquotedString :: X * UnquotedString
QuotedString :: X * QuotedString

VIEW Start        = [more,start]
VIEW Start        = []
VIEW Choice       = [UnquotedString, ">", choice]
VIEW Continuation = [recogniser, continuation]
VIEW Continuation = []
VIEW Recogniser   = [QuotedString]
VIEW Recogniser   = [nonTerminal]

RULE pre UnquotedString |- I
RULE pre QuotedString |- I
RULE pre nonTerminal |- I