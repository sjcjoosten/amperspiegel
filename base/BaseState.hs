{-# OPTIONS_GHC -Wall -O0 #-} {-# LANGUAGE OverloadedStrings #-}
module BaseState (baseState) where{
import Helpers;import TokenAwareParser;
baseState :: [(Text,[Triple (Atom Text) (Atom Text)])];
baseState =
    [ ( "parser"
      , [ "choice"      ∋ "Classification"          ↦ Fresh 110
        , "choice"      ∋ "ClassificationStatement" ↦ Fresh 98
        , "choice"      ∋ "ConceptList"             ↦ Fresh 120
        , "choice"      ∋ "ConceptList"             ↦ Fresh 128
        , "choice"      ∋ "ConsConceptList"         ↦ Fresh 120
        , "choice"      ∋ "ConsSyntaxList"          ↦ Fresh 162
        , "choice"      ∋ "Declaration"             ↦ Fresh 140
        , "choice"      ∋ "DeclarationStatement"    ↦ Fresh 102
        , "choice"      ∋ "DeclarationType"         ↦ Fresh 132
        , "choice"      ∋ "QuotedStringElement"     ↦ Fresh 174
        , "choice"      ∋ "RelationElement"         ↦ Fresh 178
        , "choice"      ∋ "Statement"               ↦ Fresh 98
        , "choice"      ∋ "Statement"               ↦ Fresh 102
        , "choice"      ∋ "Statement"               ↦ Fresh 106
        , "choice"      ∋ "Syntax"                  ↦ Fresh 148
        , "choice"      ∋ "SyntaxElement"           ↦ Fresh 174
        , "choice"      ∋ "SyntaxElement"           ↦ Fresh 178
        , "choice"      ∋ "SyntaxList"              ↦ Fresh 162
        , "choice"      ∋ "SyntaxList"              ↦ Fresh 170
        , "choice"      ∋ "SyntaxStatement"         ↦ Fresh 106
        , "nonTerminal" ∋ "classification"          ↦ "Classification"
        , "nonTerminal" ∋ "concept"                 ↦ "String"
        , "nonTerminal" ∋ "conceptList"             ↦ "ConceptList"
        , "nonTerminal" ∋ "concepts"                ↦ "DeclarationType"
        , "nonTerminal" ∋ "declaration"             ↦ "Declaration"
        , "nonTerminal" ∋ "fst"                     ↦ "String"
        , "nonTerminal" ∋ "head1"                   ↦ "String"
        , "nonTerminal" ∋ "head2"                   ↦ "SyntaxElement"
        , "nonTerminal" ∋ "mainConcept"             ↦ "String"
        , "nonTerminal" ∋ "qstring"                 ↦ "QuotedString"
        , "nonTerminal" ∋ "relation"                ↦ "StringAndOrigin"
        , "nonTerminal" ∋ "relationName"            ↦ "UnquotedString"
        , "nonTerminal" ∋ "snd"                     ↦ "String"
        , "nonTerminal" ∋ "syntax"                  ↦ "Syntax"
        , "nonTerminal" ∋ "syntaxList"              ↦ "SyntaxList"
        , "nonTerminal" ∋ "tail1"                   ↦ "ConceptList"
        , "nonTerminal" ∋ "tail2"                   ↦ "SyntaxList"
        , "recogniser"  ∋ Fresh 98                  ↦ "classification"
        , "recogniser"  ∋ Fresh 102                 ↦ "declaration"
        , "recogniser"  ∋ Fresh 106                 ↦ "syntax"
        , "continuation"∋ Fresh 110                 ↦ Fresh 112
        , "recogniser"  ∋ Fresh 110                 ↦ "\"CLASSIFY\""
        , "continuation"∋ Fresh 112                 ↦ Fresh 114
        , "recogniser"  ∋ Fresh 112                 ↦ "mainConcept"
        , "continuation"∋ Fresh 114                 ↦ Fresh 116
        , "recogniser"  ∋ Fresh 114                 ↦ "\"IS\""
        , "recogniser"  ∋ Fresh 116                 ↦ "conceptList"
        , "continuation"∋ Fresh 120                 ↦ Fresh 122
        , "recogniser"  ∋ Fresh 120                 ↦ "head1"
        , "continuation"∋ Fresh 122                 ↦ Fresh 124
        , "recogniser"  ∋ Fresh 122                 ↦ "\"/\\\\\""
        , "recogniser"  ∋ Fresh 124                 ↦ "tail1"
        , "recogniser"  ∋ Fresh 128                 ↦ "head1"
        , "continuation"∋ Fresh 132                 ↦ Fresh 134
        , "recogniser"  ∋ Fresh 132                 ↦ "fst"
        , "continuation"∋ Fresh 134                 ↦ Fresh 136
        , "recogniser"  ∋ Fresh 134                 ↦ "\"*\""
        , "recogniser"  ∋ Fresh 136                 ↦ "snd"
        , "continuation"∋ Fresh 140                 ↦ Fresh 142
        , "recogniser"  ∋ Fresh 140                 ↦ "relation"
        , "continuation"∋ Fresh 142                 ↦ Fresh 144
        , "recogniser"  ∋ Fresh 142                 ↦ "\"::\""
        , "recogniser"  ∋ Fresh 144                 ↦ "concepts"
        , "continuation"∋ Fresh 148                 ↦ Fresh 150
        , "recogniser"  ∋ Fresh 148                 ↦ "\"VIEW\""
        , "continuation"∋ Fresh 150                 ↦ Fresh 152
        , "recogniser"  ∋ Fresh 150                 ↦ "concept"
        , "continuation"∋ Fresh 152                 ↦ Fresh 154
        , "recogniser"  ∋ Fresh 152                 ↦ "\"=\""
        , "continuation"∋ Fresh 154                 ↦ Fresh 156
        , "recogniser"  ∋ Fresh 154                 ↦ "\"[\""
        , "continuation"∋ Fresh 156                 ↦ Fresh 158
        , "recogniser"  ∋ Fresh 156                 ↦ "syntaxList"
        , "recogniser"  ∋ Fresh 158                 ↦ "\"]\""
        , "continuation"∋ Fresh 162                 ↦ Fresh 164
        , "recogniser"  ∋ Fresh 162                 ↦ "head2"
        , "continuation"∋ Fresh 164                 ↦ Fresh 166
        , "recogniser"  ∋ Fresh 164                 ↦ "\",\""
        , "recogniser"  ∋ Fresh 166                 ↦ "tail2"
        , "recogniser"  ∋ Fresh 170                 ↦ "head2"
        , "recogniser"  ∋ Fresh 174                 ↦ "qstring"
        , "recogniser"  ∋ Fresh 178                 ↦ "relationName"
        , "rule"        ∋ Fresh 190 ↦ Fresh 191
        , "eFst"        ∋ Fresh 191 ↦ Fresh 192
        , "eSnd"        ∋ Fresh 191 ↦ Fresh 193
        , "pre"         ∋ Fresh 192 ↦ "classification"
        , "post"        ∋ Fresh 193 ↦ "classification"
        , "rule"        ∋ Fresh 200 ↦ Fresh 201
        , "eFst"        ∋ Fresh 201 ↦ Fresh 202
        , "eSnd"        ∋ Fresh 201 ↦ Fresh 203
        , "pre"         ∋ Fresh 202 ↦ "concept"
        , "post"        ∋ Fresh 203 ↦ "concept"
        , "rule"        ∋ Fresh 210 ↦ Fresh 211
        , "eFst"        ∋ Fresh 211 ↦ Fresh 212
        , "eSnd"        ∋ Fresh 211 ↦ Fresh 213
        , "pre"         ∋ Fresh 212 ↦ "conceptList"
        , "post"        ∋ Fresh 213 ↦ "conceptList"
        , "rule"        ∋ Fresh 220 ↦ Fresh 221
        , "eFst"        ∋ Fresh 221 ↦ Fresh 222
        , "eSnd"        ∋ Fresh 221 ↦ Fresh 223
        , "pre"         ∋ Fresh 222 ↦ "concepts"
        , "post"        ∋ Fresh 223 ↦ "concepts"
        , "rule"        ∋ Fresh 230 ↦ Fresh 231
        , "eFst"        ∋ Fresh 231 ↦ Fresh 232
        , "eSnd"        ∋ Fresh 231 ↦ Fresh 233
        , "pre"         ∋ Fresh 232 ↦ "declaration"
        , "post"        ∋ Fresh 233 ↦ "declaration"
        , "rule"        ∋ Fresh 240 ↦ Fresh 241
        , "eFst"        ∋ Fresh 241 ↦ Fresh 242
        , "eSnd"        ∋ Fresh 241 ↦ Fresh 243
        , "pre"         ∋ Fresh 242 ↦ "fst"
        , "post"        ∋ Fresh 243 ↦ "fst"
        , "rule"        ∋ Fresh 250 ↦ Fresh 251
        , "eFst"        ∋ Fresh 251 ↦ Fresh 252
        , "eSnd"        ∋ Fresh 251 ↦ Fresh 253
        , "pre"         ∋ Fresh 252 ↦ "head1"
        , "post"        ∋ Fresh 253 ↦ "head1"
        , "rule"        ∋ Fresh 260 ↦ Fresh 261
        , "eFst"        ∋ Fresh 261 ↦ Fresh 262
        , "eSnd"        ∋ Fresh 261 ↦ Fresh 263
        , "pre"         ∋ Fresh 262 ↦ "head2"
        , "post"        ∋ Fresh 263 ↦ "head2"
        , "rule"        ∋ Fresh 270 ↦ Fresh 271
        , "eFst"        ∋ Fresh 271 ↦ Fresh 272
        , "eSnd"        ∋ Fresh 271 ↦ Fresh 273
        , "pre"         ∋ Fresh 272 ↦ "mainConcept"
        , "post"        ∋ Fresh 273 ↦ "mainConcept"
        , "rule"        ∋ Fresh 280 ↦ Fresh 281
        , "eFst"        ∋ Fresh 281 ↦ Fresh 282
        , "eSnd"        ∋ Fresh 281 ↦ Fresh 283
        , "pre"         ∋ Fresh 282 ↦ "qstring"
        , "post"        ∋ Fresh 283 ↦ "qstring"
        , "rule"        ∋ Fresh 290 ↦ Fresh 291
        , "eFst"        ∋ Fresh 291 ↦ Fresh 292
        , "eSnd"        ∋ Fresh 291 ↦ Fresh 293
        , "pre"         ∋ Fresh 292 ↦ "relation"
        , "post"        ∋ Fresh 293 ↦ "relation"
        , "rule"        ∋ Fresh 300 ↦ Fresh 301
        , "eFst"        ∋ Fresh 301 ↦ Fresh 302
        , "eSnd"        ∋ Fresh 301 ↦ Fresh 303
        , "pre"         ∋ Fresh 302 ↦ "relationName"
        , "post"        ∋ Fresh 303 ↦ "relationName"
        , "rule"        ∋ Fresh 310 ↦ Fresh 311
        , "eFst"        ∋ Fresh 311 ↦ Fresh 312
        , "eSnd"        ∋ Fresh 311 ↦ Fresh 313
        , "pre"         ∋ Fresh 312 ↦ "snd"
        , "post"        ∋ Fresh 313 ↦ "snd"
        , "rule"        ∋ Fresh 320 ↦ Fresh 321
        , "eFst"        ∋ Fresh 321 ↦ Fresh 322
        , "eSnd"        ∋ Fresh 321 ↦ Fresh 323
        , "pre"         ∋ Fresh 322 ↦ "syntax"
        , "post"        ∋ Fresh 323 ↦ "syntax"
        , "rule"        ∋ Fresh 330 ↦ Fresh 331
        , "eFst"        ∋ Fresh 331 ↦ Fresh 332
        , "eSnd"        ∋ Fresh 331 ↦ Fresh 333
        , "pre"         ∋ Fresh 332 ↦ "syntaxList"
        , "post"        ∋ Fresh 333 ↦ "syntaxList"
        , "rule"        ∋ Fresh 340 ↦ Fresh 341
        , "eFst"        ∋ Fresh 341 ↦ Fresh 342
        , "eSnd"        ∋ Fresh 341 ↦ Fresh 343
        , "pre"         ∋ Fresh 342 ↦ "tail1"
        , "post"        ∋ Fresh 343 ↦ "tail1"
        , "rule"        ∋ Fresh 350 ↦ Fresh 351
        , "eFst"        ∋ Fresh 351 ↦ Fresh 352
        , "eSnd"        ∋ Fresh 351 ↦ Fresh 353
        , "pre"         ∋ Fresh 352 ↦ "tail2"
        , "post"        ∋ Fresh 353 ↦ "tail2"
        , "rule"        ∋ Fresh 360 ↦ Fresh 361
        , "eFst"        ∋ Fresh 361 ↦ Fresh 362
        , "eSnd"        ∋ Fresh 361 ↦ Fresh 363
        , "pre"         ∋ Fresh 362 ↦ "string"
        , "post"        ∋ Fresh 363 ↦ "string"
        ]
      )
    , ( "asParser"
      , [ "rule"    ∋ Fresh 0   ↦ Fresh 1
        , "eFst"    ∋ Fresh 1   ↦ Fresh 2
        , "eSnd"    ∋ Fresh 1   ↦ Fresh 3
        , "pre"     ∋ Fresh 2   ↦ "conceptList"
        , "during"  ∋ Fresh 3   ↦ "conceptLists"
        , "rule"    ∋ Fresh 4   ↦ Fresh 5
        , "eFst"    ∋ Fresh 5   ↦ Fresh 6
        , "eSnd"    ∋ Fresh 5   ↦ Fresh 10
        , "compose" ∋ Fresh 6   ↦ Fresh 7
        , "eFst"    ∋ Fresh 7   ↦ Fresh 8
        , "eSnd"    ∋ Fresh 7   ↦ Fresh 9
        , "during"  ∋ Fresh 8   ↦ "conceptLists"
        , "pre"     ∋ Fresh 9   ↦ "tail1"
        , "during"  ∋ Fresh 10  ↦ "conceptLists"
        , "rule"    ∋ Fresh 11  ↦ Fresh 12
        , "eFst"    ∋ Fresh 12  ↦ Fresh 13
        , "eSnd"    ∋ Fresh 12  ↦ Fresh 21
        , "compose" ∋ Fresh 13  ↦ Fresh 14
        , "eFst"    ∋ Fresh 14  ↦ Fresh 15
        , "eSnd"    ∋ Fresh 14  ↦ Fresh 20
        , "compose" ∋ Fresh 15  ↦ Fresh 16
        , "eFst"    ∋ Fresh 16  ↦ Fresh 17
        , "eSnd"    ∋ Fresh 16  ↦ Fresh 19
        , "converse"∋ Fresh 17  ↦ Fresh 18
        , "pre"     ∋ Fresh 18  ↦ "mainConcept"
        , "during"  ∋ Fresh 19  ↦ "conceptLists"
        , "pre"     ∋ Fresh 20  ↦ "head1"
        , "during"  ∋ Fresh 21  ↦ "subConcepts"
        , "rule"    ∋ Fresh 22  ↦ Fresh 23
        , "eFst"    ∋ Fresh 23  ↦ Fresh 24
        , "eSnd"    ∋ Fresh 23  ↦ Fresh 28
        , "compose" ∋ Fresh 24  ↦ Fresh 25
        , "eFst"    ∋ Fresh 25  ↦ Fresh 26
        , "eSnd"    ∋ Fresh 25  ↦ Fresh 27
        , "during"  ∋ Fresh 26  ↦ "subConcepts"
        , "during"  ∋ Fresh 27  ↦ "subConcepts"
        , "during"  ∋ Fresh 28  ↦ "subConcepts"
        , "rule"    ∋ Fresh 29  ↦ Fresh 30
        , "eFst"    ∋ Fresh 30  ↦ Fresh 31
        , "eSnd"    ∋ Fresh 30  ↦ Fresh 39
        , "conjunct"∋ Fresh 31  ↦ Fresh 32
        , "eFst"    ∋ Fresh 32  ↦ Fresh 33
        , "eSnd"    ∋ Fresh 32  ↦ Fresh 38
        , "compose" ∋ Fresh 33  ↦ Fresh 34
        , "eFst"    ∋ Fresh 34  ↦ Fresh 35
        , "eSnd"    ∋ Fresh 34  ↦ Fresh 37
        , "converse"∋ Fresh 35  ↦ Fresh 36
        , "pre"     ∋ Fresh 36  ↦ "mainConcept"
        , "pre"     ∋ Fresh 37  ↦ "mainConcept"
        , "during"  ∋ Fresh 39  ↦ "subConcepts"
        , "rule"    ∋ Fresh 40  ↦ Fresh 41
        , "eFst"    ∋ Fresh 41  ↦ Fresh 42
        , "eSnd"    ∋ Fresh 41  ↦ Fresh 50
        , "conjunct"∋ Fresh 42  ↦ Fresh 43
        , "eFst"    ∋ Fresh 43  ↦ Fresh 44
        , "eSnd"    ∋ Fresh 43  ↦ Fresh 49
        , "compose" ∋ Fresh 44  ↦ Fresh 45
        , "eFst"    ∋ Fresh 45  ↦ Fresh 46
        , "eSnd"    ∋ Fresh 45  ↦ Fresh 48
        , "converse"∋ Fresh 46  ↦ Fresh 47
        , "pre"     ∋ Fresh 47  ↦ "concept"
        , "pre"     ∋ Fresh 48  ↦ "concept"
        , "during"  ∋ Fresh 50  ↦ "subConcepts"
        , "rule"    ∋ Fresh 51  ↦ Fresh 52
        , "eFst"    ∋ Fresh 52  ↦ Fresh 53
        , "eSnd"    ∋ Fresh 52  ↦ Fresh 54
        , "pre"     ∋ Fresh 53  ↦ "qstring"
        , "rule"    ∋ Fresh 55  ↦ Fresh 56
        , "eFst"    ∋ Fresh 56  ↦ Fresh 57
        , "eSnd"    ∋ Fresh 56  ↦ Fresh 58
        , "pre"     ∋ Fresh 57  ↦ "relationName"
        , "rule"    ∋ Fresh 59  ↦ Fresh 60
        , "eFst"    ∋ Fresh 60  ↦ Fresh 61
        , "eSnd"    ∋ Fresh 60  ↦ Fresh 66
        , "compose" ∋ Fresh 61  ↦ Fresh 62
        , "eFst"    ∋ Fresh 62  ↦ Fresh 63
        , "eSnd"    ∋ Fresh 62  ↦ Fresh 64
        , "pre"     ∋ Fresh 63  ↦ "string"
        , "converse"∋ Fresh 64  ↦ Fresh 65
        , "pre"     ∋ Fresh 65  ↦ "string"
        , "rule"    ∋ Fresh 67  ↦ Fresh 68
        , "eFst"    ∋ Fresh 68  ↦ Fresh 69
        , "eSnd"    ∋ Fresh 68  ↦ Fresh 76
        , "compose" ∋ Fresh 69  ↦ Fresh 70
        , "eFst"    ∋ Fresh 70  ↦ Fresh 71
        , "eSnd"    ∋ Fresh 70  ↦ Fresh 75
        , "compose" ∋ Fresh 71  ↦ Fresh 72
        , "eFst"    ∋ Fresh 72  ↦ Fresh 73
        , "eSnd"    ∋ Fresh 72  ↦ Fresh 74
        , "pre"     ∋ Fresh 73  ↦ "declaration"
        , "pre"     ∋ Fresh 74  ↦ "relation"
        , "pre"     ∋ Fresh 75  ↦ "string"
        , "pre"     ∋ Fresh 76  ↦ "relationName"
        , "rule"    ∋ Fresh 77  ↦ Fresh 78
        , "eFst"    ∋ Fresh 78  ↦ Fresh 79
        , "eSnd"    ∋ Fresh 78  ↦ Fresh 86
        , "compose" ∋ Fresh 79  ↦ Fresh 80
        , "eFst"    ∋ Fresh 80  ↦ Fresh 81
        , "eSnd"    ∋ Fresh 80  ↦ Fresh 85
        , "compose" ∋ Fresh 81  ↦ Fresh 82
        , "eFst"    ∋ Fresh 82  ↦ Fresh 83
        , "eSnd"    ∋ Fresh 82  ↦ Fresh 84
        , "pre"     ∋ Fresh 83  ↦ "declaration"
        , "pre"     ∋ Fresh 84  ↦ "concepts"
        , "pre"     ∋ Fresh 85  ↦ "snd"
        , "post"    ∋ Fresh 86  ↦ "nonTerminal"
        , "rule"    ∋ Fresh 87  ↦ Fresh 88
        , "eFst"    ∋ Fresh 88  ↦ Fresh 89
        , "eSnd"    ∋ Fresh 88  ↦ Fresh 98
        , "compose" ∋ Fresh 89  ↦ Fresh 90
        , "eFst"    ∋ Fresh 90  ↦ Fresh 91
        , "eSnd"    ∋ Fresh 90  ↦ Fresh 97
        , "compose" ∋ Fresh 91  ↦ Fresh 92
        , "eFst"    ∋ Fresh 92  ↦ Fresh 93
        , "eSnd"    ∋ Fresh 92  ↦ Fresh 95
        , "converse"∋ Fresh 93  ↦ Fresh 94
        , "during"  ∋ Fresh 94  ↦ "subConcepts"
        , "converse"∋ Fresh 95  ↦ Fresh 96
        , "pre"     ∋ Fresh 96  ↦ "concept"
        , "pre"     ∋ Fresh 97  ↦ "syntaxList"
        , "post"    ∋ Fresh 98  ↦ "choice"
        , "rule"    ∋ Fresh 99  ↦ Fresh 100
        , "eFst"    ∋ Fresh 100 ↦ Fresh 101
        , "eSnd"    ∋ Fresh 100 ↦ Fresh 102
        , "pre"     ∋ Fresh 101 ↦ "head2"
        , "post"    ∋ Fresh 102 ↦ "recogniser"
        , "rule"    ∋ Fresh 103 ↦ Fresh 104
        , "eFst"    ∋ Fresh 104 ↦ Fresh 105
        , "eSnd"    ∋ Fresh 104 ↦ Fresh 106
        , "pre"     ∋ Fresh 105 ↦ "tail2"
        , "post"    ∋ Fresh 106 ↦ "continuation"
        , "rule"    ∋ Fresh 107 ↦ Fresh 108
        , "eFst"    ∋ Fresh 108 ↦ Fresh 109
        , "eSnd"    ∋ Fresh 108 ↦ Fresh 121
        , "conjunct"∋ Fresh 109 ↦ Fresh 110
        , "eFst"    ∋ Fresh 110 ↦ Fresh 111
        , "eSnd"    ∋ Fresh 110 ↦ Fresh 116
        , "compose" ∋ Fresh 111 ↦ Fresh 112
        , "eFst"    ∋ Fresh 112 ↦ Fresh 113
        , "eSnd"    ∋ Fresh 112 ↦ Fresh 114
        , "post"    ∋ Fresh 113 ↦ "eFst"
        , "converse"∋ Fresh 114 ↦ Fresh 115
        , "post"    ∋ Fresh 115 ↦ "eFst"
        , "compose" ∋ Fresh 116 ↦ Fresh 117
        , "eFst"    ∋ Fresh 117 ↦ Fresh 118
        , "eSnd"    ∋ Fresh 117 ↦ Fresh 119
        , "post"    ∋ Fresh 118 ↦ "eSnd"
        , "converse"∋ Fresh 119 ↦ Fresh 120
        , "post"    ∋ Fresh 120 ↦ "eSnd"
        , "rule"    ∋ Fresh 122 ↦ Fresh 123
        , "eFst"    ∋ Fresh 123 ↦ Fresh 124
        , "eSnd"    ∋ Fresh 123 ↦ Fresh 129
        , "compose" ∋ Fresh 124 ↦ Fresh 125
        , "eFst"    ∋ Fresh 125 ↦ Fresh 126
        , "eSnd"    ∋ Fresh 125 ↦ Fresh 127
        , "post"    ∋ Fresh 126 ↦ "conjunct"
        , "converse"∋ Fresh 127 ↦ Fresh 128
        , "post"    ∋ Fresh 128 ↦ "conjunct"
        , "rule"    ∋ Fresh 130 ↦ Fresh 131
        , "eFst"    ∋ Fresh 131 ↦ Fresh 132
        , "eSnd"    ∋ Fresh 131 ↦ Fresh 137
        , "compose" ∋ Fresh 132 ↦ Fresh 133
        , "eFst"    ∋ Fresh 133 ↦ Fresh 134
        , "eSnd"    ∋ Fresh 133 ↦ Fresh 135
        , "post"    ∋ Fresh 134 ↦ "converse"
        , "converse"∋ Fresh 135 ↦ Fresh 136
        , "post"    ∋ Fresh 136 ↦ "converse"
        , "rule"    ∋ Fresh 138 ↦ Fresh 139
        , "eFst"    ∋ Fresh 139 ↦ Fresh 140
        , "eSnd"    ∋ Fresh 139 ↦ Fresh 145
        , "compose" ∋ Fresh 140 ↦ Fresh 141
        , "eFst"    ∋ Fresh 141 ↦ Fresh 142
        , "eSnd"    ∋ Fresh 141 ↦ Fresh 143
        , "post"    ∋ Fresh 142 ↦ "compose"
        , "converse"∋ Fresh 143 ↦ Fresh 144
        , "post"    ∋ Fresh 144 ↦ "compose"
        , "rule"    ∋ Fresh 146 ↦ Fresh 147
        , "eFst"    ∋ Fresh 147 ↦ Fresh 148
        , "eSnd"    ∋ Fresh 147 ↦ Fresh 153
        , "compose" ∋ Fresh 148 ↦ Fresh 149
        , "eFst"    ∋ Fresh 149 ↦ Fresh 150
        , "eSnd"    ∋ Fresh 149 ↦ Fresh 151
        , "post"    ∋ Fresh 150 ↦ "pre"
        , "converse"∋ Fresh 151 ↦ Fresh 152
        , "post"    ∋ Fresh 152 ↦ "pre"
        , "rule"    ∋ Fresh 154 ↦ Fresh 155
        , "eFst"    ∋ Fresh 155 ↦ Fresh 156
        , "eSnd"    ∋ Fresh 155 ↦ Fresh 161
        , "compose" ∋ Fresh 156 ↦ Fresh 157
        , "eFst"    ∋ Fresh 157 ↦ Fresh 158
        , "eSnd"    ∋ Fresh 157 ↦ Fresh 159
        , "post"    ∋ Fresh 158 ↦ "post"
        , "converse"∋ Fresh 159 ↦ Fresh 160
        , "post"    ∋ Fresh 160 ↦ "post"
        , "rule"    ∋ Fresh 162 ↦ Fresh 163
        , "eFst"    ∋ Fresh 163 ↦ Fresh 164
        , "eSnd"    ∋ Fresh 163 ↦ Fresh 169
        , "compose" ∋ Fresh 164 ↦ Fresh 165
        , "eFst"    ∋ Fresh 165 ↦ Fresh 166
        , "eSnd"    ∋ Fresh 165 ↦ Fresh 167
        , "post"    ∋ Fresh 166 ↦ "during"
        , "converse"∋ Fresh 167 ↦ Fresh 168
        , "post"    ∋ Fresh 168 ↦ "during"
        , "rule"    ∋ Fresh 170 ↦ Fresh 171
        , "eFst"    ∋ Fresh 171 ↦ Fresh 172
        , "eSnd"    ∋ Fresh 171 ↦ Fresh 173
        , "pre"     ∋ Fresh 172 ↦ "during"
        , "post"    ∋ Fresh 173 ↦ "during"
        , "rule"    ∋ Fresh 174 ↦ Fresh 175
        , "eFst"    ∋ Fresh 175 ↦ Fresh 176
        , "eSnd"    ∋ Fresh 175 ↦ Fresh 177
        , "pre"     ∋ Fresh 176 ↦ "pre"
        , "post"    ∋ Fresh 177 ↦ "pre"
        , "rule"    ∋ Fresh 178 ↦ Fresh 179
        , "eFst"    ∋ Fresh 179 ↦ Fresh 180
        , "eSnd"    ∋ Fresh 179 ↦ Fresh 181
        , "pre"     ∋ Fresh 180 ↦ "post"
        , "post"    ∋ Fresh 181 ↦ "post"
        , "rule"    ∋ Fresh 182 ↦ Fresh 183
        , "eFst"    ∋ Fresh 183 ↦ Fresh 184
        , "eSnd"    ∋ Fresh 183 ↦ Fresh 185
        , "pre"     ∋ Fresh 184 ↦ "converse"
        , "post"    ∋ Fresh 185 ↦ "converse"
        , "rule"    ∋ Fresh 186 ↦ Fresh 187
        , "eFst"    ∋ Fresh 187 ↦ Fresh 188
        , "eSnd"    ∋ Fresh 187 ↦ Fresh 189
        , "pre"     ∋ Fresh 188 ↦ "conjunct"
        , "post"    ∋ Fresh 189 ↦ "conjunct"
        , "rule"    ∋ Fresh 190 ↦ Fresh 191
        , "eFst"    ∋ Fresh 191 ↦ Fresh 192
        , "eSnd"    ∋ Fresh 191 ↦ Fresh 193
        , "pre"     ∋ Fresh 192 ↦ "eFst"
        , "post"    ∋ Fresh 193 ↦ "eFst"
        , "rule"    ∋ Fresh 194 ↦ Fresh 195
        , "eFst"    ∋ Fresh 195 ↦ Fresh 196
        , "eSnd"    ∋ Fresh 195 ↦ Fresh 197
        , "pre"     ∋ Fresh 196 ↦ "eSnd"
        , "post"    ∋ Fresh 197 ↦ "eSnd"
        , "rule"    ∋ Fresh 198 ↦ Fresh 199
        , "eFst"    ∋ Fresh 199 ↦ Fresh 200
        , "eSnd"    ∋ Fresh 199 ↦ Fresh 201
        , "pre"     ∋ Fresh 200 ↦ "compose"
        , "post"    ∋ Fresh 201 ↦ "compose"
        , "rule"    ∋ Fresh 202 ↦ Fresh 203
        , "eFst"    ∋ Fresh 203 ↦ Fresh 204
        , "eSnd"    ∋ Fresh 203 ↦ Fresh 205
        , "pre"     ∋ Fresh 204 ↦ "rule"
        , "post"    ∋ Fresh 205 ↦ "rule"
        , "rule"    ∋ Fresh 206 ↦ Fresh 207
        , "eFst"    ∋ Fresh 207 ↦ Fresh 208
        , "eSnd"    ∋ Fresh 207 ↦ Fresh 209
        , "pre"     ∋ Fresh 208 ↦ "pair1"
        , "post"    ∋ Fresh 209 ↦ "pair1"
        , "rule"    ∋ Fresh 210 ↦ Fresh 211
        , "eFst"    ∋ Fresh 211 ↦ Fresh 212
        , "eSnd"    ∋ Fresh 211 ↦ Fresh 213
        , "pre"     ∋ Fresh 212 ↦ "pair2"
        , "post"    ∋ Fresh 213 ↦ "pair2"
        , "rule"    ∋ Fresh 214 ↦ Fresh 215
        , "eFst"    ∋ Fresh 215 ↦ Fresh 216
        , "eSnd"    ∋ Fresh 215 ↦ Fresh 217
        , "pre"     ∋ Fresh 216 ↦ "declaration"
        , "post"    ∋ Fresh 217 ↦ "rule"
        , "rule"    ∋ Fresh 218 ↦ Fresh 219
        , "eFst"    ∋ Fresh 219 ↦ Fresh 220
        , "eSnd"    ∋ Fresh 219 ↦ Fresh 224
        , "compose" ∋ Fresh 220 ↦ Fresh 221
        , "eFst"    ∋ Fresh 221 ↦ Fresh 222
        , "eSnd"    ∋ Fresh 221 ↦ Fresh 223
        , "pre"     ∋ Fresh 222 ↦ "relation"
        , "pre"     ∋ Fresh 223 ↦ "string"
        , "compose" ∋ Fresh 224 ↦ Fresh 225
        , "eFst"    ∋ Fresh 225 ↦ Fresh 226
        , "eSnd"    ∋ Fresh 225 ↦ Fresh 227
        , "post"    ∋ Fresh 226 ↦ "eFst"
        , "post"    ∋ Fresh 227 ↦ "pre"
        , "rule"    ∋ Fresh 228 ↦ Fresh 229
        , "eFst"    ∋ Fresh 229 ↦ Fresh 230
        , "eSnd"    ∋ Fresh 229 ↦ Fresh 234
        , "compose" ∋ Fresh 230 ↦ Fresh 231
        , "eFst"    ∋ Fresh 231 ↦ Fresh 232
        , "eSnd"    ∋ Fresh 231 ↦ Fresh 233
        , "pre"     ∋ Fresh 232 ↦ "relation"
        , "pre"     ∋ Fresh 233 ↦ "string"
        , "compose" ∋ Fresh 234 ↦ Fresh 235
        , "eFst"    ∋ Fresh 235 ↦ Fresh 236
        , "eSnd"    ∋ Fresh 235 ↦ Fresh 237
        , "post"    ∋ Fresh 236 ↦ "eSnd"
        , "post"    ∋ Fresh 237 ↦ "post"
        , "rule"    ∋ Fresh 238 ↦ Fresh 239
        , "eFst"    ∋ Fresh 239 ↦ Fresh 240
        , "eSnd"    ∋ Fresh 239 ↦ Fresh 241
        , "pair1"   ∋ Fresh 240 ↦ "r1"
        , "pair2"   ∋ Fresh 240 ↦ "r1"
        , "post"    ∋ Fresh 241 ↦ "rule"
        , "rule"    ∋ Fresh 242 ↦ Fresh 243
        , "eFst"    ∋ Fresh 243 ↦ Fresh 244
        , "eSnd"    ∋ Fresh 243 ↦ Fresh 245
        , "pair1"   ∋ Fresh 244 ↦ "r2"
        , "pair2"   ∋ Fresh 244 ↦ "r2"
        , "post"    ∋ Fresh 245 ↦ "rule"
        , "rule"    ∋ Fresh 246 ↦ Fresh 247
        , "eFst"    ∋ Fresh 247 ↦ Fresh 248
        , "eSnd"    ∋ Fresh 247 ↦ Fresh 249
        , "pair1"   ∋ Fresh 248 ↦ "r1"
        , "pair2"   ∋ Fresh 248 ↦ "string"
        , "compose" ∋ Fresh 249 ↦ Fresh 250
        , "eFst"    ∋ Fresh 250 ↦ Fresh 251
        , "eSnd"    ∋ Fresh 250 ↦ Fresh 252
        , "post"    ∋ Fresh 251 ↦ "eFst"
        , "post"    ∋ Fresh 252 ↦ "pre"
        , "rule"    ∋ Fresh 253 ↦ Fresh 254
        , "eFst"    ∋ Fresh 254 ↦ Fresh 255
        , "eSnd"    ∋ Fresh 254 ↦ Fresh 256
        , "pair1"   ∋ Fresh 255 ↦ "r1"
        , "pair2"   ∋ Fresh 255 ↦ "string"
        , "compose" ∋ Fresh 256 ↦ Fresh 257
        , "eFst"    ∋ Fresh 257 ↦ Fresh 258
        , "eSnd"    ∋ Fresh 257 ↦ Fresh 259
        , "post"    ∋ Fresh 258 ↦ "eSnd"
        , "post"    ∋ Fresh 259 ↦ "post"
        , "rule"    ∋ Fresh 260 ↦ Fresh 261
        , "eFst"    ∋ Fresh 261 ↦ Fresh 262
        , "eSnd"    ∋ Fresh 261 ↦ Fresh 263
        , "pair1"   ∋ Fresh 262 ↦ "r2"
        , "pair2"   ∋ Fresh 262 ↦ "origin"
        , "compose" ∋ Fresh 263 ↦ Fresh 264
        , "eFst"    ∋ Fresh 264 ↦ Fresh 265
        , "eSnd"    ∋ Fresh 264 ↦ Fresh 266
        , "post"    ∋ Fresh 265 ↦ "eFst"
        , "post"    ∋ Fresh 266 ↦ "pre"
        , "rule"    ∋ Fresh 267 ↦ Fresh 268
        , "eFst"    ∋ Fresh 268 ↦ Fresh 269
        , "eSnd"    ∋ Fresh 268 ↦ Fresh 270
        , "pair1"   ∋ Fresh 269 ↦ "r2"
        , "pair2"   ∋ Fresh 269 ↦ "origin"
        , "compose" ∋ Fresh 270 ↦ Fresh 271
        , "eFst"    ∋ Fresh 271 ↦ Fresh 272
        , "eSnd"    ∋ Fresh 271 ↦ Fresh 273
        , "post"    ∋ Fresh 272 ↦ "eSnd"
        , "post"    ∋ Fresh 273 ↦ "post"
        ]
      )
    ];}