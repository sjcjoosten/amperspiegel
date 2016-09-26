parent :: Person * Person
dad :: Person * Man
name :: Person * String -- string is built-in (has a parser defined for it)

CLASSIFY Man IS Man /\ Person
CLASSIFY Woman IS Woman /\ Person

VIEW Man = ["Man", name]
VIEW Woman = ["Woman", name]
VIEW Person = ["Father", "of", name, "is", dad]

CLASSIFY Person IS Statement /\ Person -- Parser will parse a list of statements

RULE dad |- parent
 -- names identify the person (name is INJ)
RULE (name;name~) |- = -- symbol for identity relation is . for now

RULE name |- =