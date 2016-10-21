RULE conceptList |- conceptLists
RULE (conceptLists ; tail1) |- conceptLists
RULE (( mainConcept ~ ; conceptLists ) ; head1) |- subConcepts
RULE (subConcepts ; subConcepts) |- subConcepts
RULE ((mainConcept ~ ; mainConcept) /\ =) |- subConcepts
RULE ( (concept ~ ; concept) /\ =) |- subConcepts
RULE qstring |- =
RULE relationName |- =
RULE (string ; string ~) |- = -- this rule means every relation has a unique name.
-- Unfortunately, there is no other way to disambiguate declarations.
RULE ((declaration ; relation) ; string) |- relationName
RULE ((declaration ; concepts) ; snd) |- nonTerminal
RULE ((subConcepts ~ ;  concept ~) ; syntaxList) |- choice
RULE head2 |- recogniser
RULE tail2 |- continuation
RULE ((eFst;eFst ~) /\ (eSnd;eSnd ~)) |- =
RULE (conjunct;conjunct~) |- =
RULE (converse;converse~) |- =
RULE (compose;compose~)   |- =
RULE (pre ; pre ~)        |- =
RULE (post ; post ~)      |- =
RULE (during ; during ~)  |- =
