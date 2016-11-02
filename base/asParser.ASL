RULE pre conceptList |- during conceptLists
RULE (during conceptLists;pre tail1) |- during conceptLists
RULE ((pre mainConcept~;during conceptLists);pre head1) |- during subConcepts
RULE (during subConcepts;during subConcepts) |- during subConcepts
RULE ((pre mainConcept~;pre mainConcept) /\ I) |- during subConcepts
RULE ((pre concept~;pre concept) /\ I) |- during subConcepts
RULE pre qstring |- I
RULE pre relationName |- I
RULE (pre string;pre string~) |- I
-- Unfortunately, there is no other way to disambiguate declarations.
RULE ((pre declaration;pre relation);pre string) |- pre relationName
RULE ((pre declaration;pre concepts);pre snd) |- post nonTerminal
RULE ((during subConcepts~;pre concept~);pre syntaxList) |- post choice
RULE pre head2 |- post recogniser
RULE pre tail2 |- post continuation
-- Identities to compress the system a bit (not strictly needed)
RULE ((post eFst;post eFst ~) /\ (post eSnd;post eSnd ~)) |- I
RULE (post conjunct ; post conjunct ~) |- I
RULE (post converse ; post converse ~) |- I
RULE (post compose  ; post compose ~)  |- I
RULE (post pre      ; post pre ~)      |- I
RULE (post post     ; post post ~)     |- I
RULE (post during   ; post during ~)   |- I
-- keep al the existing rules
RULE pre during |- post during
RULE pre pre |- post pre
RULE pre post |- post post
RULE pre converse |- post converse
RULE pre conjunct |- post conjunct
RULE pre eFst |- post eFst
RULE pre eSnd |- post eSnd
RULE pre compose |- post compose
RULE pre rule |- post rule
RULE pre pair1 |- post pair1
RULE pre pair2 |- post pair2
-- add extra rules for declarations (including the two built-in ones)
RULE pre declaration |- post rule
RULE (pre relation ; pre string) |- (post eFst ; post pre)
RULE (pre relation ; pre string) |- (post eSnd ; post post)
RULE < r1 , r1 > |- post rule
RULE < r2 , r2 > |- post rule
RULE < r1 , string > |- (post eFst ; post pre)
RULE < r1 , string > |- (post eSnd ; post post)
RULE < r2 , origin > |- (post eFst ; post pre)
RULE < r2 , origin > |- (post eSnd ; post post)