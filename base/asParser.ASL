RULE pre conceptList |- during conceptLists
RULE (during conceptLists;pre tail1) |- during conceptLists
RULE ((pre mainConcept~;during conceptLists);pre head1) |- during subConcepts
RULE (during subConcepts;during subConcepts) |- during subConcepts
RULE ((pre mainConcept~;pre mainConcept) /\ =) |- during subConcepts
RULE ((pre concept~;pre concept) /\ =) |- during subConcepts
RULE pre qstring |- =
RULE pre relationName |- =
RULE (pre string;pre string~) |- =
-- Unfortunately, there is no other way to disambiguate declarations.
RULE ((pre declaration;pre relation);pre string) |- pre relationName
RULE ((pre declaration;pre concepts);pre snd) |- post nonTerminal
RULE ((during subConcepts~;pre concept~);pre syntaxList) |- post choice
RULE pre head2 |- post recogniser
RULE pre tail2 |- post continuation
RULE ((pre eFst;pre eFst ~) /\ (pre eSnd;pre eSnd ~)) |- =
RULE (pre conjunct ; pre conjunct ~) |- =
RULE (pre converse ; pre converse ~) |- =
RULE (pre compose  ; pre compose ~)  |- =
RULE (pre pre      ; pre pre ~)      |- =
RULE (pre post     ; pre post ~)     |- =
RULE (pre during   ; pre during ~)   |- =
