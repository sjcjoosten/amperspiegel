{-# OPTIONS_GHC -Wall -O0 #-} {-# LANGUAGE OverloadedStrings #-}
module BaseState (baseState) where{
import Helpers;import TokenAwareParser;
baseState :: [(Text,[Triple (Atom Text) (Atom Text)])];
baseState =
  [ ( "asParser"
    , [ "rule" ∋ Fresh 0 ↦ Fresh 1
      , "eFst" ∋ Fresh 1 ↦ Fresh 2
      , "eSnd" ∋ Fresh 1 ↦ Fresh 3
      , "pre" ∋ Fresh 2 ↦ "conceptList"
      , "during" ∋ Fresh 3 ↦ "conceptLists"
      , "rule" ∋ Fresh 4 ↦ Fresh 5
      , "eFst" ∋ Fresh 5 ↦ Fresh 6
      , "eSnd" ∋ Fresh 5 ↦ Fresh 10
      , "compose" ∋ Fresh 6 ↦ Fresh 7
      , "eFst" ∋ Fresh 7 ↦ Fresh 8
      , "eSnd" ∋ Fresh 7 ↦ Fresh 9
      , "during" ∋ Fresh 8 ↦ "conceptLists"
      , "pre" ∋ Fresh 9 ↦ "tail1"
      , "during" ∋ Fresh 10 ↦ "conceptLists"
      , "rule" ∋ Fresh 11 ↦ Fresh 12
      , "eFst" ∋ Fresh 12 ↦ Fresh 13
      , "eSnd" ∋ Fresh 12 ↦ Fresh 21
      , "compose" ∋ Fresh 13 ↦ Fresh 14
      , "eFst" ∋ Fresh 14 ↦ Fresh 15
      , "eSnd" ∋ Fresh 14 ↦ Fresh 20
      , "compose" ∋ Fresh 15 ↦ Fresh 16
      , "eFst" ∋ Fresh 16 ↦ Fresh 17
      , "eSnd" ∋ Fresh 16 ↦ Fresh 19
      , "converse" ∋ Fresh 17 ↦ Fresh 18
      , "pre" ∋ Fresh 18 ↦ "mainConcept"
      , "during" ∋ Fresh 19 ↦ "conceptLists"
      , "pre" ∋ Fresh 20 ↦ "head1"
      , "during" ∋ Fresh 21 ↦ "subConcepts"
      , "rule" ∋ Fresh 22 ↦ Fresh 23
      , "eFst" ∋ Fresh 23 ↦ Fresh 24
      , "eSnd" ∋ Fresh 23 ↦ Fresh 28
      , "compose" ∋ Fresh 24 ↦ Fresh 25
      , "eFst" ∋ Fresh 25 ↦ Fresh 26
      , "eSnd" ∋ Fresh 25 ↦ Fresh 27
      , "during" ∋ Fresh 26 ↦ "subConcepts"
      , "during" ∋ Fresh 27 ↦ "subConcepts"
      , "during" ∋ Fresh 28 ↦ "subConcepts"
      , "rule" ∋ Fresh 29 ↦ Fresh 30
      , "eFst" ∋ Fresh 30 ↦ Fresh 31
      , "eSnd" ∋ Fresh 30 ↦ Fresh 39
      , "conjunct" ∋ Fresh 31 ↦ Fresh 32
      , "eFst" ∋ Fresh 32 ↦ Fresh 33
      , "eSnd" ∋ Fresh 32 ↦ Fresh 38
      , "compose" ∋ Fresh 33 ↦ Fresh 34
      , "eFst" ∋ Fresh 34 ↦ Fresh 35
      , "eSnd" ∋ Fresh 34 ↦ Fresh 37
      , "converse" ∋ Fresh 35 ↦ Fresh 36
      , "pre" ∋ Fresh 36 ↦ "mainConcept"
      , "pre" ∋ Fresh 37 ↦ "mainConcept"
      , "during" ∋ Fresh 39 ↦ "subConcepts"
      , "rule" ∋ Fresh 40 ↦ Fresh 41
      , "eFst" ∋ Fresh 41 ↦ Fresh 42
      , "eSnd" ∋ Fresh 41 ↦ Fresh 50
      , "conjunct" ∋ Fresh 42 ↦ Fresh 43
      , "eFst" ∋ Fresh 43 ↦ Fresh 44
      , "eSnd" ∋ Fresh 43 ↦ Fresh 49
      , "compose" ∋ Fresh 44 ↦ Fresh 45
      , "eFst" ∋ Fresh 45 ↦ Fresh 46
      , "eSnd" ∋ Fresh 45 ↦ Fresh 48
      , "converse" ∋ Fresh 46 ↦ Fresh 47
      , "pre" ∋ Fresh 47 ↦ "concept"
      , "pre" ∋ Fresh 48 ↦ "concept"
      , "during" ∋ Fresh 50 ↦ "subConcepts"
      , "rule" ∋ Fresh 51 ↦ Fresh 52
      , "eFst" ∋ Fresh 52 ↦ Fresh 53
      , "eSnd" ∋ Fresh 52 ↦ Fresh 54
      , "pre" ∋ Fresh 53 ↦ "qstring"
      , "rule" ∋ Fresh 55 ↦ Fresh 56
      , "eFst" ∋ Fresh 56 ↦ Fresh 57
      , "eSnd" ∋ Fresh 56 ↦ Fresh 58
      , "pre" ∋ Fresh 57 ↦ "relationName"
      , "rule" ∋ Fresh 59 ↦ Fresh 60
      , "eFst" ∋ Fresh 60 ↦ Fresh 61
      , "eSnd" ∋ Fresh 60 ↦ Fresh 66
      , "compose" ∋ Fresh 61 ↦ Fresh 62
      , "eFst" ∋ Fresh 62 ↦ Fresh 63
      , "eSnd" ∋ Fresh 62 ↦ Fresh 64
      , "pre" ∋ Fresh 63 ↦ "string"
      , "converse" ∋ Fresh 64 ↦ Fresh 65
      , "pre" ∋ Fresh 65 ↦ "string"
      , "rule" ∋ Fresh 67 ↦ Fresh 68
      , "eFst" ∋ Fresh 68 ↦ Fresh 69
      , "eSnd" ∋ Fresh 68 ↦ Fresh 76
      , "compose" ∋ Fresh 69 ↦ Fresh 70
      , "eFst" ∋ Fresh 70 ↦ Fresh 71
      , "eSnd" ∋ Fresh 70 ↦ Fresh 75
      , "compose" ∋ Fresh 71 ↦ Fresh 72
      , "eFst" ∋ Fresh 72 ↦ Fresh 73
      , "eSnd" ∋ Fresh 72 ↦ Fresh 74
      , "pre" ∋ Fresh 73 ↦ "declaration"
      , "pre" ∋ Fresh 74 ↦ "relation"
      , "pre" ∋ Fresh 75 ↦ "string"
      , "pre" ∋ Fresh 76 ↦ "relationName"
      , "rule" ∋ Fresh 77 ↦ Fresh 78
      , "eFst" ∋ Fresh 78 ↦ Fresh 79
      , "eSnd" ∋ Fresh 78 ↦ Fresh 86
      , "compose" ∋ Fresh 79 ↦ Fresh 80
      , "eFst" ∋ Fresh 80 ↦ Fresh 81
      , "eSnd" ∋ Fresh 80 ↦ Fresh 85
      , "compose" ∋ Fresh 81 ↦ Fresh 82
      , "eFst" ∋ Fresh 82 ↦ Fresh 83
      , "eSnd" ∋ Fresh 82 ↦ Fresh 84
      , "pre" ∋ Fresh 83 ↦ "declaration"
      , "pre" ∋ Fresh 84 ↦ "concepts"
      , "pre" ∋ Fresh 85 ↦ "snd"
      , "post" ∋ Fresh 86 ↦ "nonTerminal"
      , "rule" ∋ Fresh 87 ↦ Fresh 88
      , "eFst" ∋ Fresh 88 ↦ Fresh 89
      , "eSnd" ∋ Fresh 88 ↦ Fresh 98
      , "compose" ∋ Fresh 89 ↦ Fresh 90
      , "eFst" ∋ Fresh 90 ↦ Fresh 91
      , "eSnd" ∋ Fresh 90 ↦ Fresh 97
      , "compose" ∋ Fresh 91 ↦ Fresh 92
      , "eFst" ∋ Fresh 92 ↦ Fresh 93
      , "eSnd" ∋ Fresh 92 ↦ Fresh 95
      , "converse" ∋ Fresh 93 ↦ Fresh 94
      , "during" ∋ Fresh 94 ↦ "subConcepts"
      , "converse" ∋ Fresh 95 ↦ Fresh 96
      , "pre" ∋ Fresh 96 ↦ "concept"
      , "pre" ∋ Fresh 97 ↦ "syntaxList"
      , "post" ∋ Fresh 98 ↦ "choice"
      , "rule" ∋ Fresh 99 ↦ Fresh 100
      , "eFst" ∋ Fresh 100 ↦ Fresh 101
      , "eSnd" ∋ Fresh 100 ↦ Fresh 102
      , "pre" ∋ Fresh 101 ↦ "head2"
      , "post" ∋ Fresh 102 ↦ "recogniser"
      , "rule" ∋ Fresh 103 ↦ Fresh 104
      , "eFst" ∋ Fresh 104 ↦ Fresh 105
      , "eSnd" ∋ Fresh 104 ↦ Fresh 106
      , "pre" ∋ Fresh 105 ↦ "tail2"
      , "post" ∋ Fresh 106 ↦ "continuation"
      , "rule" ∋ Fresh 107 ↦ Fresh 108
      , "eFst" ∋ Fresh 108 ↦ Fresh 109
      , "eSnd" ∋ Fresh 108 ↦ Fresh 121
      , "conjunct" ∋ Fresh 109 ↦ Fresh 110
      , "eFst" ∋ Fresh 110 ↦ Fresh 111
      , "eSnd" ∋ Fresh 110 ↦ Fresh 116
      , "compose" ∋ Fresh 111 ↦ Fresh 112
      , "eFst" ∋ Fresh 112 ↦ Fresh 113
      , "eSnd" ∋ Fresh 112 ↦ Fresh 114
      , "post" ∋ Fresh 113 ↦ "eFst"
      , "converse" ∋ Fresh 114 ↦ Fresh 115
      , "post" ∋ Fresh 115 ↦ "eFst"
      , "compose" ∋ Fresh 116 ↦ Fresh 117
      , "eFst" ∋ Fresh 117 ↦ Fresh 118
      , "eSnd" ∋ Fresh 117 ↦ Fresh 119
      , "post" ∋ Fresh 118 ↦ "eSnd"
      , "converse" ∋ Fresh 119 ↦ Fresh 120
      , "post" ∋ Fresh 120 ↦ "eSnd"
      , "rule" ∋ Fresh 122 ↦ Fresh 123
      , "eFst" ∋ Fresh 123 ↦ Fresh 124
      , "eSnd" ∋ Fresh 123 ↦ Fresh 129
      , "compose" ∋ Fresh 124 ↦ Fresh 125
      , "eFst" ∋ Fresh 125 ↦ Fresh 126
      , "eSnd" ∋ Fresh 125 ↦ Fresh 127
      , "post" ∋ Fresh 126 ↦ "conjunct"
      , "converse" ∋ Fresh 127 ↦ Fresh 128
      , "post" ∋ Fresh 128 ↦ "conjunct"
      , "rule" ∋ Fresh 130 ↦ Fresh 131
      , "eFst" ∋ Fresh 131 ↦ Fresh 132
      , "eSnd" ∋ Fresh 131 ↦ Fresh 137
      , "compose" ∋ Fresh 132 ↦ Fresh 133
      , "eFst" ∋ Fresh 133 ↦ Fresh 134
      , "eSnd" ∋ Fresh 133 ↦ Fresh 135
      , "post" ∋ Fresh 134 ↦ "converse"
      , "converse" ∋ Fresh 135 ↦ Fresh 136
      , "post" ∋ Fresh 136 ↦ "converse"
      , "rule" ∋ Fresh 138 ↦ Fresh 139
      , "eFst" ∋ Fresh 139 ↦ Fresh 140
      , "eSnd" ∋ Fresh 139 ↦ Fresh 145
      , "compose" ∋ Fresh 140 ↦ Fresh 141
      , "eFst" ∋ Fresh 141 ↦ Fresh 142
      , "eSnd" ∋ Fresh 141 ↦ Fresh 143
      , "post" ∋ Fresh 142 ↦ "compose"
      , "converse" ∋ Fresh 143 ↦ Fresh 144
      , "post" ∋ Fresh 144 ↦ "compose"
      , "rule" ∋ Fresh 146 ↦ Fresh 147
      , "eFst" ∋ Fresh 147 ↦ Fresh 148
      , "eSnd" ∋ Fresh 147 ↦ Fresh 153
      , "compose" ∋ Fresh 148 ↦ Fresh 149
      , "eFst" ∋ Fresh 149 ↦ Fresh 150
      , "eSnd" ∋ Fresh 149 ↦ Fresh 151
      , "post" ∋ Fresh 150 ↦ "pre"
      , "converse" ∋ Fresh 151 ↦ Fresh 152
      , "post" ∋ Fresh 152 ↦ "pre"
      , "rule" ∋ Fresh 154 ↦ Fresh 155
      , "eFst" ∋ Fresh 155 ↦ Fresh 156
      , "eSnd" ∋ Fresh 155 ↦ Fresh 161
      , "compose" ∋ Fresh 156 ↦ Fresh 157
      , "eFst" ∋ Fresh 157 ↦ Fresh 158
      , "eSnd" ∋ Fresh 157 ↦ Fresh 159
      , "post" ∋ Fresh 158 ↦ "post"
      , "converse" ∋ Fresh 159 ↦ Fresh 160
      , "post" ∋ Fresh 160 ↦ "post"
      , "rule" ∋ Fresh 162 ↦ Fresh 163
      , "eFst" ∋ Fresh 163 ↦ Fresh 164
      , "eSnd" ∋ Fresh 163 ↦ Fresh 169
      , "compose" ∋ Fresh 164 ↦ Fresh 165
      , "eFst" ∋ Fresh 165 ↦ Fresh 166
      , "eSnd" ∋ Fresh 165 ↦ Fresh 167
      , "post" ∋ Fresh 166 ↦ "during"
      , "converse" ∋ Fresh 167 ↦ Fresh 168
      , "post" ∋ Fresh 168 ↦ "during"
      , "rule" ∋ Fresh 170 ↦ Fresh 171
      , "eFst" ∋ Fresh 171 ↦ Fresh 172
      , "eSnd" ∋ Fresh 171 ↦ Fresh 173
      , "pre" ∋ Fresh 172 ↦ "during"
      , "post" ∋ Fresh 173 ↦ "during"
      , "rule" ∋ Fresh 174 ↦ Fresh 175
      , "eFst" ∋ Fresh 175 ↦ Fresh 176
      , "eSnd" ∋ Fresh 175 ↦ Fresh 177
      , "pre" ∋ Fresh 176 ↦ "pre"
      , "post" ∋ Fresh 177 ↦ "pre"
      , "rule" ∋ Fresh 178 ↦ Fresh 179
      , "eFst" ∋ Fresh 179 ↦ Fresh 180
      , "eSnd" ∋ Fresh 179 ↦ Fresh 181
      , "pre" ∋ Fresh 180 ↦ "post"
      , "post" ∋ Fresh 181 ↦ "post"
      , "rule" ∋ Fresh 182 ↦ Fresh 183
      , "eFst" ∋ Fresh 183 ↦ Fresh 184
      , "eSnd" ∋ Fresh 183 ↦ Fresh 185
      , "pre" ∋ Fresh 184 ↦ "converse"
      , "post" ∋ Fresh 185 ↦ "converse"
      , "rule" ∋ Fresh 186 ↦ Fresh 187
      , "eFst" ∋ Fresh 187 ↦ Fresh 188
      , "eSnd" ∋ Fresh 187 ↦ Fresh 189
      , "pre" ∋ Fresh 188 ↦ "conjunct"
      , "post" ∋ Fresh 189 ↦ "conjunct"
      , "rule" ∋ Fresh 190 ↦ Fresh 191
      , "eFst" ∋ Fresh 191 ↦ Fresh 192
      , "eSnd" ∋ Fresh 191 ↦ Fresh 193
      , "pre" ∋ Fresh 192 ↦ "eFst"
      , "post" ∋ Fresh 193 ↦ "eFst"
      , "rule" ∋ Fresh 194 ↦ Fresh 195
      , "eFst" ∋ Fresh 195 ↦ Fresh 196
      , "eSnd" ∋ Fresh 195 ↦ Fresh 197
      , "pre" ∋ Fresh 196 ↦ "eSnd"
      , "post" ∋ Fresh 197 ↦ "eSnd"
      , "rule" ∋ Fresh 198 ↦ Fresh 199
      , "eFst" ∋ Fresh 199 ↦ Fresh 200
      , "eSnd" ∋ Fresh 199 ↦ Fresh 201
      , "pre" ∋ Fresh 200 ↦ "compose"
      , "post" ∋ Fresh 201 ↦ "compose"
      , "rule" ∋ Fresh 202 ↦ Fresh 203
      , "eFst" ∋ Fresh 203 ↦ Fresh 204
      , "eSnd" ∋ Fresh 203 ↦ Fresh 205
      , "pre" ∋ Fresh 204 ↦ "rule"
      , "post" ∋ Fresh 205 ↦ "rule"
      , "rule" ∋ Fresh 206 ↦ Fresh 207
      , "eFst" ∋ Fresh 207 ↦ Fresh 208
      , "eSnd" ∋ Fresh 207 ↦ Fresh 209
      , "pre" ∋ Fresh 208 ↦ "pair1"
      , "post" ∋ Fresh 209 ↦ "pair1"
      , "rule" ∋ Fresh 210 ↦ Fresh 211
      , "eFst" ∋ Fresh 211 ↦ Fresh 212
      , "eSnd" ∋ Fresh 211 ↦ Fresh 213
      , "pre" ∋ Fresh 212 ↦ "pair2"
      , "post" ∋ Fresh 213 ↦ "pair2"
      , "rule" ∋ Fresh 214 ↦ Fresh 215
      , "eFst" ∋ Fresh 215 ↦ Fresh 216
      , "eSnd" ∋ Fresh 215 ↦ Fresh 217
      , "pre" ∋ Fresh 216 ↦ "declaration"
      , "post" ∋ Fresh 217 ↦ "rule"
      , "rule" ∋ Fresh 218 ↦ Fresh 219
      , "eFst" ∋ Fresh 219 ↦ Fresh 220
      , "eSnd" ∋ Fresh 219 ↦ Fresh 224
      , "compose" ∋ Fresh 220 ↦ Fresh 221
      , "eFst" ∋ Fresh 221 ↦ Fresh 222
      , "eSnd" ∋ Fresh 221 ↦ Fresh 223
      , "pre" ∋ Fresh 222 ↦ "relation"
      , "pre" ∋ Fresh 223 ↦ "string"
      , "compose" ∋ Fresh 224 ↦ Fresh 225
      , "eFst" ∋ Fresh 225 ↦ Fresh 226
      , "eSnd" ∋ Fresh 225 ↦ Fresh 227
      , "post" ∋ Fresh 226 ↦ "eFst"
      , "post" ∋ Fresh 227 ↦ "pre"
      , "rule" ∋ Fresh 228 ↦ Fresh 229
      , "eFst" ∋ Fresh 229 ↦ Fresh 230
      , "eSnd" ∋ Fresh 229 ↦ Fresh 234
      , "compose" ∋ Fresh 230 ↦ Fresh 231
      , "eFst" ∋ Fresh 231 ↦ Fresh 232
      , "eSnd" ∋ Fresh 231 ↦ Fresh 233
      , "pre" ∋ Fresh 232 ↦ "relation"
      , "pre" ∋ Fresh 233 ↦ "string"
      , "compose" ∋ Fresh 234 ↦ Fresh 235
      , "eFst" ∋ Fresh 235 ↦ Fresh 236
      , "eSnd" ∋ Fresh 235 ↦ Fresh 237
      , "post" ∋ Fresh 236 ↦ "eSnd"
      , "post" ∋ Fresh 237 ↦ "post"
      , "rule" ∋ Fresh 238 ↦ Fresh 239
      , "eFst" ∋ Fresh 239 ↦ Fresh 240
      , "eSnd" ∋ Fresh 239 ↦ Fresh 241
      , "pair1" ∋ Fresh 240 ↦ "r1"
      , "pair2" ∋ Fresh 240 ↦ "r1"
      , "post" ∋ Fresh 241 ↦ "rule"
      , "rule" ∋ Fresh 242 ↦ Fresh 243
      , "eFst" ∋ Fresh 243 ↦ Fresh 244
      , "eSnd" ∋ Fresh 243 ↦ Fresh 245
      , "pair1" ∋ Fresh 244 ↦ "r2"
      , "pair2" ∋ Fresh 244 ↦ "r2"
      , "post" ∋ Fresh 245 ↦ "rule"
      , "rule" ∋ Fresh 246 ↦ Fresh 247
      , "eFst" ∋ Fresh 247 ↦ Fresh 248
      , "eSnd" ∋ Fresh 247 ↦ Fresh 249
      , "pair1" ∋ Fresh 248 ↦ "r1"
      , "pair2" ∋ Fresh 248 ↦ "string"
      , "compose" ∋ Fresh 249 ↦ Fresh 250
      , "eFst" ∋ Fresh 250 ↦ Fresh 251
      , "eSnd" ∋ Fresh 250 ↦ Fresh 252
      , "post" ∋ Fresh 251 ↦ "eFst"
      , "post" ∋ Fresh 252 ↦ "pre"
      , "rule" ∋ Fresh 253 ↦ Fresh 254
      , "eFst" ∋ Fresh 254 ↦ Fresh 255
      , "eSnd" ∋ Fresh 254 ↦ Fresh 256
      , "pair1" ∋ Fresh 255 ↦ "r1"
      , "pair2" ∋ Fresh 255 ↦ "string"
      , "compose" ∋ Fresh 256 ↦ Fresh 257
      , "eFst" ∋ Fresh 257 ↦ Fresh 258
      , "eSnd" ∋ Fresh 257 ↦ Fresh 259
      , "post" ∋ Fresh 258 ↦ "eSnd"
      , "post" ∋ Fresh 259 ↦ "post"
      , "rule" ∋ Fresh 260 ↦ Fresh 261
      , "eFst" ∋ Fresh 261 ↦ Fresh 262
      , "eSnd" ∋ Fresh 261 ↦ Fresh 263
      , "pair1" ∋ Fresh 262 ↦ "r2"
      , "pair2" ∋ Fresh 262 ↦ "origin"
      , "compose" ∋ Fresh 263 ↦ Fresh 264
      , "eFst" ∋ Fresh 264 ↦ Fresh 265
      , "eSnd" ∋ Fresh 264 ↦ Fresh 266
      , "post" ∋ Fresh 265 ↦ "eFst"
      , "post" ∋ Fresh 266 ↦ "pre"
      , "rule" ∋ Fresh 267 ↦ Fresh 268
      , "eFst" ∋ Fresh 268 ↦ Fresh 269
      , "eSnd" ∋ Fresh 268 ↦ Fresh 270
      , "pair1" ∋ Fresh 269 ↦ "r2"
      , "pair2" ∋ Fresh 269 ↦ "origin"
      , "compose" ∋ Fresh 270 ↦ Fresh 271
      , "eFst" ∋ Fresh 271 ↦ Fresh 272
      , "eSnd" ∋ Fresh 271 ↦ Fresh 273
      , "post" ∋ Fresh 272 ↦ "eSnd"
      , "post" ∋ Fresh 273 ↦ "post"
      ])
  , ( "parser"
    , [ "choice" ∋ "Classification" ↦ Fresh 635
      , "choice" ∋ "ClassificationStatement" ↦ Fresh 632
      , "choice" ∋ "ConceptList" ↦ Fresh 639
      , "choice" ∋ "ConceptList" ↦ Fresh 642
      , "choice" ∋ "ConsConceptList" ↦ Fresh 639
      , "choice" ∋ "ConsSyntaxList" ↦ Fresh 655
      , "choice" ∋ "Declaration" ↦ Fresh 646
      , "choice" ∋ "DeclarationStatement" ↦ Fresh 633
      , "choice" ∋ "DeclarationType" ↦ Fresh 643
      , "choice" ∋ "QuotedStringElement" ↦ Fresh 659
      , "choice" ∋ "RelationElement" ↦ Fresh 660
      , "choice" ∋ "Statement" ↦ Fresh 632
      , "choice" ∋ "Statement" ↦ Fresh 633
      , "choice" ∋ "Statement" ↦ Fresh 634
      , "choice" ∋ "Syntax" ↦ Fresh 649
      , "choice" ∋ "SyntaxElement" ↦ Fresh 659
      , "choice" ∋ "SyntaxElement" ↦ Fresh 660
      , "choice" ∋ "SyntaxList" ↦ Fresh 655
      , "choice" ∋ "SyntaxList" ↦ Fresh 658
      , "choice" ∋ "SyntaxStatement" ↦ Fresh 634
      , "nonTerminal" ∋ "classification" ↦ "Classification"
      , "rule" ∋ "classification" ↦ Fresh 615
      , "nonTerminal" ∋ "concept" ↦ "String"
      , "rule" ∋ "concept" ↦ Fresh 626
      , "nonTerminal" ∋ "conceptList" ↦ "ConceptList"
      , "rule" ∋ "conceptList" ↦ Fresh 617
      , "nonTerminal" ∋ "concepts" ↦ "DeclarationType"
      , "rule" ∋ "concepts" ↦ Fresh 622
      , "nonTerminal" ∋ "declaration" ↦ "Declaration"
      , "rule" ∋ "declaration" ↦ Fresh 620
      , "nonTerminal" ∋ "fst" ↦ "String"
      , "rule" ∋ "fst" ↦ Fresh 623
      , "nonTerminal" ∋ "head1" ↦ "String"
      , "rule" ∋ "head1" ↦ Fresh 618
      , "nonTerminal" ∋ "head2" ↦ "SyntaxElement"
      , "rule" ∋ "head2" ↦ Fresh 629
      , "nonTerminal" ∋ "mainConcept" ↦ "String"
      , "rule" ∋ "mainConcept" ↦ Fresh 616
      , "nonTerminal" ∋ "qstring" ↦ "QuotedString"
      , "rule" ∋ "qstring" ↦ Fresh 631
      , "eFst" ∋ "r1" ↦ Fresh 664
      , "eSnd" ∋ "r1" ↦ Fresh 663
      , "rule" ∋ "r1" ↦ "r1"
      , "eFst" ∋ "r2" ↦ Fresh 662
      , "eSnd" ∋ "r2" ↦ Fresh 661
      , "rule" ∋ "r2" ↦ "r2"
      , "nonTerminal" ∋ "relation" ↦ "StringAndOrigin"
      , "rule" ∋ "relation" ↦ Fresh 621
      , "nonTerminal" ∋ "relationName" ↦ "UnquotedString"
      , "rule" ∋ "relationName" ↦ Fresh 627
      , "nonTerminal" ∋ "snd" ↦ "String"
      , "rule" ∋ "snd" ↦ Fresh 624
      , "nonTerminal" ∋ "syntax" ↦ "Syntax"
      , "rule" ∋ "syntax" ↦ Fresh 625
      , "nonTerminal" ∋ "syntaxList" ↦ "SyntaxList"
      , "rule" ∋ "syntaxList" ↦ Fresh 628
      , "nonTerminal" ∋ "tail1" ↦ "ConceptList"
      , "rule" ∋ "tail1" ↦ Fresh 619
      , "nonTerminal" ∋ "tail2" ↦ "SyntaxList"
      , "rule" ∋ "tail2" ↦ Fresh 630
      , "eFst" ∋ Fresh 615 ↦ Fresh 665
      , "eSnd" ∋ Fresh 615 ↦ Fresh 666
      , "eFst" ∋ Fresh 616 ↦ Fresh 667
      , "eSnd" ∋ Fresh 616 ↦ Fresh 668
      , "eFst" ∋ Fresh 617 ↦ Fresh 669
      , "eSnd" ∋ Fresh 617 ↦ Fresh 670
      , "eFst" ∋ Fresh 618 ↦ Fresh 671
      , "eSnd" ∋ Fresh 618 ↦ Fresh 672
      , "eFst" ∋ Fresh 619 ↦ Fresh 673
      , "eSnd" ∋ Fresh 619 ↦ Fresh 674
      , "eFst" ∋ Fresh 620 ↦ Fresh 675
      , "eSnd" ∋ Fresh 620 ↦ Fresh 676
      , "eFst" ∋ Fresh 621 ↦ Fresh 677
      , "eSnd" ∋ Fresh 621 ↦ Fresh 678
      , "eFst" ∋ Fresh 622 ↦ Fresh 679
      , "eSnd" ∋ Fresh 622 ↦ Fresh 680
      , "eFst" ∋ Fresh 623 ↦ Fresh 681
      , "eSnd" ∋ Fresh 623 ↦ Fresh 682
      , "eFst" ∋ Fresh 624 ↦ Fresh 683
      , "eSnd" ∋ Fresh 624 ↦ Fresh 684
      , "eFst" ∋ Fresh 625 ↦ Fresh 685
      , "eSnd" ∋ Fresh 625 ↦ Fresh 686
      , "eFst" ∋ Fresh 626 ↦ Fresh 687
      , "eSnd" ∋ Fresh 626 ↦ Fresh 688
      , "eFst" ∋ Fresh 627 ↦ Fresh 689
      , "eSnd" ∋ Fresh 627 ↦ Fresh 690
      , "eFst" ∋ Fresh 628 ↦ Fresh 691
      , "eSnd" ∋ Fresh 628 ↦ Fresh 692
      , "eFst" ∋ Fresh 629 ↦ Fresh 693
      , "eSnd" ∋ Fresh 629 ↦ Fresh 694
      , "eFst" ∋ Fresh 630 ↦ Fresh 695
      , "eSnd" ∋ Fresh 630 ↦ Fresh 696
      , "eFst" ∋ Fresh 631 ↦ Fresh 697
      , "eSnd" ∋ Fresh 631 ↦ Fresh 698
      , "recogniser" ∋ Fresh 632 ↦ "classification"
      , "recogniser" ∋ Fresh 633 ↦ "declaration"
      , "recogniser" ∋ Fresh 634 ↦ "syntax"
      , "continuation" ∋ Fresh 635 ↦ Fresh 636
      , "recogniser" ∋ Fresh 635 ↦ "\"CLASSIFY\""
      , "continuation" ∋ Fresh 636 ↦ Fresh 637
      , "recogniser" ∋ Fresh 636 ↦ "mainConcept"
      , "continuation" ∋ Fresh 637 ↦ Fresh 638
      , "recogniser" ∋ Fresh 637 ↦ "\"IS\""
      , "recogniser" ∋ Fresh 638 ↦ "conceptList"
      , "continuation" ∋ Fresh 639 ↦ Fresh 640
      , "recogniser" ∋ Fresh 639 ↦ "head1"
      , "continuation" ∋ Fresh 640 ↦ Fresh 641
      , "recogniser" ∋ Fresh 640 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 641 ↦ "tail1"
      , "recogniser" ∋ Fresh 642 ↦ "head1"
      , "continuation" ∋ Fresh 643 ↦ Fresh 644
      , "recogniser" ∋ Fresh 643 ↦ "fst"
      , "continuation" ∋ Fresh 644 ↦ Fresh 645
      , "recogniser" ∋ Fresh 644 ↦ "\"*\""
      , "recogniser" ∋ Fresh 645 ↦ "snd"
      , "continuation" ∋ Fresh 646 ↦ Fresh 647
      , "recogniser" ∋ Fresh 646 ↦ "relation"
      , "continuation" ∋ Fresh 647 ↦ Fresh 648
      , "recogniser" ∋ Fresh 647 ↦ "\"::\""
      , "recogniser" ∋ Fresh 648 ↦ "concepts"
      , "continuation" ∋ Fresh 649 ↦ Fresh 650
      , "recogniser" ∋ Fresh 649 ↦ "\"VIEW\""
      , "continuation" ∋ Fresh 650 ↦ Fresh 651
      , "recogniser" ∋ Fresh 650 ↦ "concept"
      , "continuation" ∋ Fresh 651 ↦ Fresh 652
      , "recogniser" ∋ Fresh 651 ↦ "\"=\""
      , "continuation" ∋ Fresh 652 ↦ Fresh 653
      , "recogniser" ∋ Fresh 652 ↦ "\"[\""
      , "continuation" ∋ Fresh 653 ↦ Fresh 654
      , "recogniser" ∋ Fresh 653 ↦ "syntaxList"
      , "recogniser" ∋ Fresh 654 ↦ "\"]\""
      , "continuation" ∋ Fresh 655 ↦ Fresh 656
      , "recogniser" ∋ Fresh 655 ↦ "head2"
      , "continuation" ∋ Fresh 656 ↦ Fresh 657
      , "recogniser" ∋ Fresh 656 ↦ "\",\""
      , "recogniser" ∋ Fresh 657 ↦ "tail2"
      , "recogniser" ∋ Fresh 658 ↦ "head2"
      , "recogniser" ∋ Fresh 659 ↦ "qstring"
      , "recogniser" ∋ Fresh 660 ↦ "relationName"
      , "post" ∋ Fresh 661 ↦ "origin"
      , "pre" ∋ Fresh 662 ↦ "origin"
      , "post" ∋ Fresh 663 ↦ "string"
      , "pre" ∋ Fresh 664 ↦ "string"
      , "pre" ∋ Fresh 665 ↦ "classification"
      , "post" ∋ Fresh 666 ↦ "classification"
      , "pre" ∋ Fresh 667 ↦ "mainConcept"
      , "post" ∋ Fresh 668 ↦ "mainConcept"
      , "pre" ∋ Fresh 669 ↦ "conceptList"
      , "post" ∋ Fresh 670 ↦ "conceptList"
      , "pre" ∋ Fresh 671 ↦ "head1"
      , "post" ∋ Fresh 672 ↦ "head1"
      , "pre" ∋ Fresh 673 ↦ "tail1"
      , "post" ∋ Fresh 674 ↦ "tail1"
      , "pre" ∋ Fresh 675 ↦ "declaration"
      , "post" ∋ Fresh 676 ↦ "declaration"
      , "pre" ∋ Fresh 677 ↦ "relation"
      , "post" ∋ Fresh 678 ↦ "relation"
      , "pre" ∋ Fresh 679 ↦ "concepts"
      , "post" ∋ Fresh 680 ↦ "concepts"
      , "pre" ∋ Fresh 681 ↦ "fst"
      , "post" ∋ Fresh 682 ↦ "fst"
      , "pre" ∋ Fresh 683 ↦ "snd"
      , "post" ∋ Fresh 684 ↦ "snd"
      , "pre" ∋ Fresh 685 ↦ "syntax"
      , "post" ∋ Fresh 686 ↦ "syntax"
      , "pre" ∋ Fresh 687 ↦ "concept"
      , "post" ∋ Fresh 688 ↦ "concept"
      , "pre" ∋ Fresh 689 ↦ "relationName"
      , "post" ∋ Fresh 690 ↦ "relationName"
      , "pre" ∋ Fresh 691 ↦ "syntaxList"
      , "post" ∋ Fresh 692 ↦ "syntaxList"
      , "pre" ∋ Fresh 693 ↦ "head2"
      , "post" ∋ Fresh 694 ↦ "head2"
      , "pre" ∋ Fresh 695 ↦ "tail2"
      , "post" ∋ Fresh 696 ↦ "tail2"
      , "pre" ∋ Fresh 697 ↦ "qstring"
      , "post" ∋ Fresh 698 ↦ "qstring"
      ])
  ];}
