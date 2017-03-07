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
      , "eSnd" ∋ Fresh 88 ↦ Fresh 95
      , "compose" ∋ Fresh 89 ↦ Fresh 90
      , "eFst" ∋ Fresh 90 ↦ Fresh 91
      , "eSnd" ∋ Fresh 90 ↦ Fresh 93
      , "converse" ∋ Fresh 91 ↦ Fresh 92
      , "during" ∋ Fresh 92 ↦ "subConcepts"
      , "converse" ∋ Fresh 93 ↦ Fresh 94
      , "pre" ∋ Fresh 94 ↦ "concept"
      , "post" ∋ Fresh 95 ↦ "choice"
      , "rule" ∋ Fresh 96 ↦ Fresh 97
      , "eFst" ∋ Fresh 97 ↦ Fresh 98
      , "eSnd" ∋ Fresh 97 ↦ Fresh 99
      , "pre" ∋ Fresh 98 ↦ "syntaxList"
      , "rule" ∋ Fresh 100 ↦ Fresh 101
      , "eFst" ∋ Fresh 101 ↦ Fresh 102
      , "eSnd" ∋ Fresh 101 ↦ Fresh 103
      , "pre" ∋ Fresh 102 ↦ "head2"
      , "post" ∋ Fresh 103 ↦ "recogniser"
      , "rule" ∋ Fresh 104 ↦ Fresh 105
      , "eFst" ∋ Fresh 105 ↦ Fresh 106
      , "eSnd" ∋ Fresh 105 ↦ Fresh 107
      , "pre" ∋ Fresh 106 ↦ "tail2"
      , "post" ∋ Fresh 107 ↦ "continuation"
      , "rule" ∋ Fresh 108 ↦ Fresh 109
      , "eFst" ∋ Fresh 109 ↦ Fresh 110
      , "eSnd" ∋ Fresh 109 ↦ Fresh 122
      , "conjunct" ∋ Fresh 110 ↦ Fresh 111
      , "eFst" ∋ Fresh 111 ↦ Fresh 112
      , "eSnd" ∋ Fresh 111 ↦ Fresh 117
      , "compose" ∋ Fresh 112 ↦ Fresh 113
      , "eFst" ∋ Fresh 113 ↦ Fresh 114
      , "eSnd" ∋ Fresh 113 ↦ Fresh 115
      , "post" ∋ Fresh 114 ↦ "eFst"
      , "converse" ∋ Fresh 115 ↦ Fresh 116
      , "post" ∋ Fresh 116 ↦ "eFst"
      , "compose" ∋ Fresh 117 ↦ Fresh 118
      , "eFst" ∋ Fresh 118 ↦ Fresh 119
      , "eSnd" ∋ Fresh 118 ↦ Fresh 120
      , "post" ∋ Fresh 119 ↦ "eSnd"
      , "converse" ∋ Fresh 120 ↦ Fresh 121
      , "post" ∋ Fresh 121 ↦ "eSnd"
      , "rule" ∋ Fresh 123 ↦ Fresh 124
      , "eFst" ∋ Fresh 124 ↦ Fresh 125
      , "eSnd" ∋ Fresh 124 ↦ Fresh 130
      , "compose" ∋ Fresh 125 ↦ Fresh 126
      , "eFst" ∋ Fresh 126 ↦ Fresh 127
      , "eSnd" ∋ Fresh 126 ↦ Fresh 128
      , "post" ∋ Fresh 127 ↦ "conjunct"
      , "converse" ∋ Fresh 128 ↦ Fresh 129
      , "post" ∋ Fresh 129 ↦ "conjunct"
      , "rule" ∋ Fresh 131 ↦ Fresh 132
      , "eFst" ∋ Fresh 132 ↦ Fresh 133
      , "eSnd" ∋ Fresh 132 ↦ Fresh 138
      , "compose" ∋ Fresh 133 ↦ Fresh 134
      , "eFst" ∋ Fresh 134 ↦ Fresh 135
      , "eSnd" ∋ Fresh 134 ↦ Fresh 136
      , "post" ∋ Fresh 135 ↦ "converse"
      , "converse" ∋ Fresh 136 ↦ Fresh 137
      , "post" ∋ Fresh 137 ↦ "converse"
      , "rule" ∋ Fresh 139 ↦ Fresh 140
      , "eFst" ∋ Fresh 140 ↦ Fresh 141
      , "eSnd" ∋ Fresh 140 ↦ Fresh 146
      , "compose" ∋ Fresh 141 ↦ Fresh 142
      , "eFst" ∋ Fresh 142 ↦ Fresh 143
      , "eSnd" ∋ Fresh 142 ↦ Fresh 144
      , "post" ∋ Fresh 143 ↦ "compose"
      , "converse" ∋ Fresh 144 ↦ Fresh 145
      , "post" ∋ Fresh 145 ↦ "compose"
      , "rule" ∋ Fresh 147 ↦ Fresh 148
      , "eFst" ∋ Fresh 148 ↦ Fresh 149
      , "eSnd" ∋ Fresh 148 ↦ Fresh 154
      , "compose" ∋ Fresh 149 ↦ Fresh 150
      , "eFst" ∋ Fresh 150 ↦ Fresh 151
      , "eSnd" ∋ Fresh 150 ↦ Fresh 152
      , "post" ∋ Fresh 151 ↦ "pre"
      , "converse" ∋ Fresh 152 ↦ Fresh 153
      , "post" ∋ Fresh 153 ↦ "pre"
      , "rule" ∋ Fresh 155 ↦ Fresh 156
      , "eFst" ∋ Fresh 156 ↦ Fresh 157
      , "eSnd" ∋ Fresh 156 ↦ Fresh 162
      , "compose" ∋ Fresh 157 ↦ Fresh 158
      , "eFst" ∋ Fresh 158 ↦ Fresh 159
      , "eSnd" ∋ Fresh 158 ↦ Fresh 160
      , "post" ∋ Fresh 159 ↦ "post"
      , "converse" ∋ Fresh 160 ↦ Fresh 161
      , "post" ∋ Fresh 161 ↦ "post"
      , "rule" ∋ Fresh 163 ↦ Fresh 164
      , "eFst" ∋ Fresh 164 ↦ Fresh 165
      , "eSnd" ∋ Fresh 164 ↦ Fresh 170
      , "compose" ∋ Fresh 165 ↦ Fresh 166
      , "eFst" ∋ Fresh 166 ↦ Fresh 167
      , "eSnd" ∋ Fresh 166 ↦ Fresh 168
      , "post" ∋ Fresh 167 ↦ "during"
      , "converse" ∋ Fresh 168 ↦ Fresh 169
      , "post" ∋ Fresh 169 ↦ "during"
      , "rule" ∋ Fresh 171 ↦ Fresh 172
      , "eFst" ∋ Fresh 172 ↦ Fresh 173
      , "eSnd" ∋ Fresh 172 ↦ Fresh 174
      , "pre" ∋ Fresh 173 ↦ "during"
      , "post" ∋ Fresh 174 ↦ "during"
      , "rule" ∋ Fresh 175 ↦ Fresh 176
      , "eFst" ∋ Fresh 176 ↦ Fresh 177
      , "eSnd" ∋ Fresh 176 ↦ Fresh 178
      , "pre" ∋ Fresh 177 ↦ "pre"
      , "post" ∋ Fresh 178 ↦ "pre"
      , "rule" ∋ Fresh 179 ↦ Fresh 180
      , "eFst" ∋ Fresh 180 ↦ Fresh 181
      , "eSnd" ∋ Fresh 180 ↦ Fresh 182
      , "pre" ∋ Fresh 181 ↦ "post"
      , "post" ∋ Fresh 182 ↦ "post"
      , "rule" ∋ Fresh 183 ↦ Fresh 184
      , "eFst" ∋ Fresh 184 ↦ Fresh 185
      , "eSnd" ∋ Fresh 184 ↦ Fresh 186
      , "pre" ∋ Fresh 185 ↦ "converse"
      , "post" ∋ Fresh 186 ↦ "converse"
      , "rule" ∋ Fresh 187 ↦ Fresh 188
      , "eFst" ∋ Fresh 188 ↦ Fresh 189
      , "eSnd" ∋ Fresh 188 ↦ Fresh 190
      , "pre" ∋ Fresh 189 ↦ "conjunct"
      , "post" ∋ Fresh 190 ↦ "conjunct"
      , "rule" ∋ Fresh 191 ↦ Fresh 192
      , "eFst" ∋ Fresh 192 ↦ Fresh 193
      , "eSnd" ∋ Fresh 192 ↦ Fresh 194
      , "pre" ∋ Fresh 193 ↦ "eFst"
      , "post" ∋ Fresh 194 ↦ "eFst"
      , "rule" ∋ Fresh 195 ↦ Fresh 196
      , "eFst" ∋ Fresh 196 ↦ Fresh 197
      , "eSnd" ∋ Fresh 196 ↦ Fresh 198
      , "pre" ∋ Fresh 197 ↦ "eSnd"
      , "post" ∋ Fresh 198 ↦ "eSnd"
      , "rule" ∋ Fresh 199 ↦ Fresh 200
      , "eFst" ∋ Fresh 200 ↦ Fresh 201
      , "eSnd" ∋ Fresh 200 ↦ Fresh 202
      , "pre" ∋ Fresh 201 ↦ "compose"
      , "post" ∋ Fresh 202 ↦ "compose"
      , "rule" ∋ Fresh 203 ↦ Fresh 204
      , "eFst" ∋ Fresh 204 ↦ Fresh 205
      , "eSnd" ∋ Fresh 204 ↦ Fresh 206
      , "pre" ∋ Fresh 205 ↦ "rule"
      , "post" ∋ Fresh 206 ↦ "rule"
      , "rule" ∋ Fresh 207 ↦ Fresh 208
      , "eFst" ∋ Fresh 208 ↦ Fresh 209
      , "eSnd" ∋ Fresh 208 ↦ Fresh 210
      , "pre" ∋ Fresh 209 ↦ "pair1"
      , "post" ∋ Fresh 210 ↦ "pair1"
      , "rule" ∋ Fresh 211 ↦ Fresh 212
      , "eFst" ∋ Fresh 212 ↦ Fresh 213
      , "eSnd" ∋ Fresh 212 ↦ Fresh 214
      , "pre" ∋ Fresh 213 ↦ "pair2"
      , "post" ∋ Fresh 214 ↦ "pair2"
      , "rule" ∋ Fresh 215 ↦ Fresh 216
      , "eFst" ∋ Fresh 216 ↦ Fresh 217
      , "eSnd" ∋ Fresh 216 ↦ Fresh 218
      , "pre" ∋ Fresh 217 ↦ "declaration"
      , "post" ∋ Fresh 218 ↦ "rule"
      , "rule" ∋ Fresh 219 ↦ Fresh 220
      , "eFst" ∋ Fresh 220 ↦ Fresh 221
      , "eSnd" ∋ Fresh 220 ↦ Fresh 225
      , "compose" ∋ Fresh 221 ↦ Fresh 222
      , "eFst" ∋ Fresh 222 ↦ Fresh 223
      , "eSnd" ∋ Fresh 222 ↦ Fresh 224
      , "pre" ∋ Fresh 223 ↦ "relation"
      , "pre" ∋ Fresh 224 ↦ "string"
      , "compose" ∋ Fresh 225 ↦ Fresh 226
      , "eFst" ∋ Fresh 226 ↦ Fresh 227
      , "eSnd" ∋ Fresh 226 ↦ Fresh 228
      , "post" ∋ Fresh 227 ↦ "eFst"
      , "post" ∋ Fresh 228 ↦ "pre"
      , "rule" ∋ Fresh 229 ↦ Fresh 230
      , "eFst" ∋ Fresh 230 ↦ Fresh 231
      , "eSnd" ∋ Fresh 230 ↦ Fresh 235
      , "compose" ∋ Fresh 231 ↦ Fresh 232
      , "eFst" ∋ Fresh 232 ↦ Fresh 233
      , "eSnd" ∋ Fresh 232 ↦ Fresh 234
      , "pre" ∋ Fresh 233 ↦ "relation"
      , "pre" ∋ Fresh 234 ↦ "string"
      , "compose" ∋ Fresh 235 ↦ Fresh 236
      , "eFst" ∋ Fresh 236 ↦ Fresh 237
      , "eSnd" ∋ Fresh 236 ↦ Fresh 238
      , "post" ∋ Fresh 237 ↦ "eSnd"
      , "post" ∋ Fresh 238 ↦ "post"
      , "rule" ∋ Fresh 239 ↦ Fresh 240
      , "eFst" ∋ Fresh 240 ↦ Fresh 241
      , "eSnd" ∋ Fresh 240 ↦ Fresh 242
      , "pair1" ∋ Fresh 241 ↦ "keepString"
      , "pair2" ∋ Fresh 241 ↦ "keepString"
      , "post" ∋ Fresh 242 ↦ "rule"
      , "rule" ∋ Fresh 243 ↦ Fresh 244
      , "eFst" ∋ Fresh 244 ↦ Fresh 245
      , "eSnd" ∋ Fresh 244 ↦ Fresh 246
      , "pair1" ∋ Fresh 245 ↦ "keepOrigin"
      , "pair2" ∋ Fresh 245 ↦ "keepOrigin"
      , "post" ∋ Fresh 246 ↦ "rule"
      , "rule" ∋ Fresh 247 ↦ Fresh 248
      , "eFst" ∋ Fresh 248 ↦ Fresh 249
      , "eSnd" ∋ Fresh 248 ↦ Fresh 250
      , "pair1" ∋ Fresh 249 ↦ "keepString"
      , "pair2" ∋ Fresh 249 ↦ "string"
      , "compose" ∋ Fresh 250 ↦ Fresh 251
      , "eFst" ∋ Fresh 251 ↦ Fresh 252
      , "eSnd" ∋ Fresh 251 ↦ Fresh 253
      , "post" ∋ Fresh 252 ↦ "eFst"
      , "post" ∋ Fresh 253 ↦ "pre"
      , "rule" ∋ Fresh 254 ↦ Fresh 255
      , "eFst" ∋ Fresh 255 ↦ Fresh 256
      , "eSnd" ∋ Fresh 255 ↦ Fresh 257
      , "pair1" ∋ Fresh 256 ↦ "keepString"
      , "pair2" ∋ Fresh 256 ↦ "string"
      , "compose" ∋ Fresh 257 ↦ Fresh 258
      , "eFst" ∋ Fresh 258 ↦ Fresh 259
      , "eSnd" ∋ Fresh 258 ↦ Fresh 260
      , "post" ∋ Fresh 259 ↦ "eSnd"
      , "post" ∋ Fresh 260 ↦ "post"
      , "rule" ∋ Fresh 261 ↦ Fresh 262
      , "eFst" ∋ Fresh 262 ↦ Fresh 263
      , "eSnd" ∋ Fresh 262 ↦ Fresh 264
      , "pair1" ∋ Fresh 263 ↦ "keepOrigin"
      , "pair2" ∋ Fresh 263 ↦ "origin"
      , "compose" ∋ Fresh 264 ↦ Fresh 265
      , "eFst" ∋ Fresh 265 ↦ Fresh 266
      , "eSnd" ∋ Fresh 265 ↦ Fresh 267
      , "post" ∋ Fresh 266 ↦ "eFst"
      , "post" ∋ Fresh 267 ↦ "pre"
      , "rule" ∋ Fresh 268 ↦ Fresh 269
      , "eFst" ∋ Fresh 269 ↦ Fresh 270
      , "eSnd" ∋ Fresh 269 ↦ Fresh 271
      , "pair1" ∋ Fresh 270 ↦ "keepOrigin"
      , "pair2" ∋ Fresh 270 ↦ "origin"
      , "compose" ∋ Fresh 271 ↦ Fresh 272
      , "eFst" ∋ Fresh 272 ↦ Fresh 273
      , "eSnd" ∋ Fresh 272 ↦ Fresh 274
      , "post" ∋ Fresh 273 ↦ "eSnd"
      , "post" ∋ Fresh 274 ↦ "post"
      , "rule" ∋ Fresh 275 ↦ Fresh 276
      , "eFst" ∋ Fresh 276 ↦ Fresh 277
      , "eSnd" ∋ Fresh 276 ↦ Fresh 278
      , "pair1" ∋ Fresh 277 ↦ "Start"
      , "pair2" ∋ Fresh 277 ↦ "endOfFile"
      , "post" ∋ Fresh 278 ↦ "choice"
      , "rule" ∋ Fresh 279 ↦ Fresh 280
      , "eFst" ∋ Fresh 280 ↦ Fresh 281
      , "eSnd" ∋ Fresh 280 ↦ Fresh 282
      , "pair1" ∋ Fresh 281 ↦ "Start"
      , "pair2" ∋ Fresh 281 ↦ "NextStatement"
      , "post" ∋ Fresh 282 ↦ "choice"
      , "rule" ∋ Fresh 283 ↦ Fresh 284
      , "eFst" ∋ Fresh 284 ↦ Fresh 285
      , "eSnd" ∋ Fresh 284 ↦ Fresh 286
      , "pair1" ∋ Fresh 285 ↦ "NextStatement"
      , "pair2" ∋ Fresh 285 ↦ "Statement"
      , "post" ∋ Fresh 286 ↦ "recogniser"
      , "rule" ∋ Fresh 287 ↦ Fresh 288
      , "eFst" ∋ Fresh 288 ↦ Fresh 289
      , "eSnd" ∋ Fresh 288 ↦ Fresh 290
      , "pair1" ∋ Fresh 289 ↦ "NextStatement"
      , "pair2" ∋ Fresh 289 ↦ "gotoStart"
      , "post" ∋ Fresh 290 ↦ "continuation"
      , "rule" ∋ Fresh 291 ↦ Fresh 292
      , "eFst" ∋ Fresh 292 ↦ Fresh 293
      , "eSnd" ∋ Fresh 292 ↦ Fresh 294
      , "pair1" ∋ Fresh 293 ↦ "gotoStart"
      , "pair2" ∋ Fresh 293 ↦ "Start"
      , "post" ∋ Fresh 294 ↦ "recogniser"
      , "rule" ∋ Fresh 295 ↦ Fresh 296
      , "eFst" ∋ Fresh 296 ↦ Fresh 297
      , "eSnd" ∋ Fresh 296 ↦ Fresh 298
      , "pair1" ∋ Fresh 297 ↦ "Start"
      , "pair2" ∋ Fresh 297 ↦ "Start"
      , "post" ∋ Fresh 298 ↦ "nonTerminal"
      , "rule" ∋ Fresh 299 ↦ Fresh 300
      , "eFst" ∋ Fresh 300 ↦ Fresh 301
      , "eSnd" ∋ Fresh 300 ↦ Fresh 302
      , "pair1" ∋ Fresh 301 ↦ "Statement"
      , "pair2" ∋ Fresh 301 ↦ "Statement"
      , "post" ∋ Fresh 302 ↦ "nonTerminal"
      ])
  , ( "cfg"
    , [ "choice" ∋ "Choice" ↦ Fresh 698
      , "choice" ∋ "Compose" ↦ Fresh 879
      , "choice" ∋ "Conjunct" ↦ Fresh 876
      , "choice" ∋ "Continuation" ↦ Fresh 701
      , "choice" ∋ "Continuation" ↦ Fresh 703
      , "choice" ∋ "Expression" ↦ Fresh 849
      , "choice" ∋ "Expression" ↦ Fresh 852
      , "choice" ∋ "Expression" ↦ Fresh 853
      , "choice" ∋ "Expression" ↦ Fresh 854
      , "choice" ∋ "Expression" ↦ Fresh 856
      , "choice" ∋ "Expression" ↦ Fresh 858
      , "choice" ∋ "Expression" ↦ Fresh 860
      , "choice" ∋ "Expression" ↦ Fresh 862
      , "choice" ∋ "Expression" ↦ Fresh 867
      , "choice" ∋ "Expression" ↦ Fresh 872
      , "choice" ∋ "Expression" ↦ Fresh 875
      , "nonTerminal" ∋ "I" ↦ "Expression"
      , "rule" ∋ "I" ↦ Fresh 735
      , "choice" ∋ "KeepStatement" ↦ Fresh 882
      , "continuation" ∋ "NextStatement" ↦ "gotoStart"
      , "recogniser" ∋ "NextStatement" ↦ "Statement"
      , "choice" ∋ "PreExpression" ↦ Fresh 849
      , "choice" ∋ "PreExpression" ↦ Fresh 856
      , "choice" ∋ "PreExpression" ↦ Fresh 858
      , "choice" ∋ "PreExpression" ↦ Fresh 860
      , "choice" ∋ "PreExpression" ↦ Fresh 862
      , "nonTerminal" ∋ "QuotedString" ↦ "QuotedString"
      , "rule" ∋ "QuotedString" ↦ Fresh 694
      , "choice" ∋ "Recogniser" ↦ Fresh 704
      , "choice" ∋ "Recogniser" ↦ Fresh 705
      , "choice" ∋ "Recogniser" ↦ Fresh 706
      , "choice" ∋ "Recogniser" ↦ Fresh 710
      , "choice" ∋ "RuleStatement" ↦ Fresh 844
      , "choice" ∋ "RuleSubset" ↦ Fresh 846
      , "choice" ∋ "Start" ↦ "NextStatement"
      , "choice" ∋ "Start" ↦ "endOfFile"
      , "nonTerminal" ∋ "Start" ↦ "Start"
      , "choice" ∋ "Statement" ↦ Fresh 697
      , "choice" ∋ "Statement" ↦ Fresh 844
      , "choice" ∋ "Statement" ↦ Fresh 882
      , "nonTerminal" ∋ "Statement" ↦ "Statement"
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 846
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 876
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 879
      , "choice" ∋ "UnaryExpression" ↦ Fresh 849
      , "choice" ∋ "UnaryExpression" ↦ Fresh 854
      , "choice" ∋ "UnaryExpression" ↦ Fresh 856
      , "choice" ∋ "UnaryExpression" ↦ Fresh 858
      , "choice" ∋ "UnaryExpression" ↦ Fresh 860
      , "choice" ∋ "UnaryExpression" ↦ Fresh 862
      , "choice" ∋ "UnaryExpression" ↦ Fresh 867
      , "choice" ∋ "UnaryExpression" ↦ Fresh 872
      , "choice" ∋ "UnaryExpression" ↦ Fresh 875
      , "nonTerminal" ∋ "UnquotedString" ↦ "UnquotedString"
      , "rule" ∋ "UnquotedString" ↦ Fresh 693
      , "nonTerminal" ∋ "choice" ↦ "Continuation"
      , "rule" ∋ "choice" ↦ Fresh 688
      , "nonTerminal" ∋ "compose" ↦ "Compose"
      , "rule" ∋ "compose" ↦ Fresh 745
      , "nonTerminal" ∋ "conjunct" ↦ "Conjunct"
      , "rule" ∋ "conjunct" ↦ Fresh 743
      , "nonTerminal" ∋ "continuation" ↦ "Continuation"
      , "rule" ∋ "continuation" ↦ Fresh 689
      , "nonTerminal" ∋ "converse" ↦ "PreExpression"
      , "rule" ∋ "converse" ↦ Fresh 744
      , "nonTerminal" ∋ "during" ↦ "UnquotedString"
      , "rule" ∋ "during" ↦ Fresh 748
      , "nonTerminal" ∋ "eFst" ↦ "Expression"
      , "rule" ∋ "eFst" ↦ Fresh 741
      , "nonTerminal" ∋ "eSnd" ↦ "UnaryExpression"
      , "rule" ∋ "eSnd" ↦ Fresh 742
      , "recogniser" ∋ "gotoStart" ↦ "Start"
      , "nonTerminal" ∋ "keep" ↦ "UnquotedString"
      , "rule" ∋ "keep" ↦ Fresh 751
      , "eFst" ∋ "keepOrigin" ↦ Fresh 885
      , "eSnd" ∋ "keepOrigin" ↦ Fresh 884
      , "rule" ∋ "keepOrigin" ↦ "keepOrigin"
      , "eFst" ∋ "keepString" ↦ Fresh 887
      , "eSnd" ∋ "keepString" ↦ Fresh 886
      , "rule" ∋ "keepString" ↦ "keepString"
      , "nonTerminal" ∋ "mapsTo" ↦ "Expression"
      , "rule" ∋ "mapsTo" ↦ Fresh 754
      , "nonTerminal" ∋ "more" ↦ "Start"
      , "rule" ∋ "more" ↦ Fresh 687
      , "nonTerminal" ∋ "nonTerminal" ↦ "UnquotedString"
      , "rule" ∋ "nonTerminal" ↦ Fresh 691
      , "nonTerminal" ∋ "pair" ↦ "String"
      , "rule" ∋ "pair" ↦ Fresh 752
      , "nonTerminal" ∋ "pair1" ↦ "String"
      , "rule" ∋ "pair1" ↦ Fresh 749
      , "nonTerminal" ∋ "pair2" ↦ "String"
      , "rule" ∋ "pair2" ↦ Fresh 750
      , "nonTerminal" ∋ "post" ↦ "UnquotedString"
      , "rule" ∋ "post" ↦ Fresh 747
      , "nonTerminal" ∋ "pre" ↦ "UnquotedString"
      , "rule" ∋ "pre" ↦ Fresh 746
      , "nonTerminal" ∋ "recRelation" ↦ "UnquotedString"
      , "rule" ∋ "recRelation" ↦ Fresh 695
      , "nonTerminal" ∋ "recogniser" ↦ "Recogniser"
      , "rule" ∋ "recogniser" ↦ Fresh 690
      , "nonTerminal" ∋ "relaxSnd" ↦ "Expression"
      , "rule" ∋ "relaxSnd" ↦ Fresh 755
      , "nonTerminal" ∋ "rule" ↦ "RuleSubset"
      , "rule" ∋ "rule" ↦ Fresh 740
      , "nonTerminal" ∋ "sameTerminal" ↦ "UnquotedString"
      , "rule" ∋ "sameTerminal" ↦ Fresh 692
      , "nonTerminal" ∋ "separator" ↦ "QuotedString"
      , "rule" ∋ "separator" ↦ Fresh 696
      , "nonTerminal" ∋ "start" ↦ "Choice"
      , "rule" ∋ "start" ↦ Fresh 686
      , "nonTerminal" ∋ "toPair" ↦ "String"
      , "rule" ∋ "toPair" ↦ Fresh 753
      , "eFst" ∋ Fresh 686 ↦ Fresh 888
      , "eSnd" ∋ Fresh 686 ↦ Fresh 889
      , "eFst" ∋ Fresh 687 ↦ Fresh 890
      , "eSnd" ∋ Fresh 687 ↦ Fresh 891
      , "eFst" ∋ Fresh 688 ↦ Fresh 892
      , "eSnd" ∋ Fresh 688 ↦ Fresh 893
      , "eFst" ∋ Fresh 689 ↦ Fresh 894
      , "eSnd" ∋ Fresh 689 ↦ Fresh 895
      , "eFst" ∋ Fresh 690 ↦ Fresh 896
      , "eSnd" ∋ Fresh 690 ↦ Fresh 897
      , "eFst" ∋ Fresh 691 ↦ Fresh 734
      , "eSnd" ∋ Fresh 691 ↦ Fresh 898
      , "eFst" ∋ Fresh 692 ↦ Fresh 726
      , "eSnd" ∋ Fresh 692 ↦ Fresh 899
      , "eFst" ∋ Fresh 693 ↦ Fresh 718
      , "eSnd" ∋ Fresh 693 ↦ Fresh 900
      , "eFst" ∋ Fresh 694 ↦ Fresh 722
      , "eSnd" ∋ Fresh 694 ↦ Fresh 901
      , "eFst" ∋ Fresh 695 ↦ Fresh 730
      , "eSnd" ∋ Fresh 695 ↦ Fresh 902
      , "eFst" ∋ Fresh 696 ↦ Fresh 903
      , "eSnd" ∋ Fresh 696 ↦ Fresh 904
      , "recogniser" ∋ Fresh 697 ↦ "start"
      , "continuation" ∋ Fresh 698 ↦ Fresh 699
      , "recogniser" ∋ Fresh 698 ↦ "UnquotedString"
      , "continuation" ∋ Fresh 699 ↦ Fresh 700
      , "recogniser" ∋ Fresh 699 ↦ "\">\""
      , "recogniser" ∋ Fresh 700 ↦ "choice"
      , "continuation" ∋ Fresh 701 ↦ Fresh 702
      , "recogniser" ∋ Fresh 701 ↦ "recogniser"
      , "recogniser" ∋ Fresh 702 ↦ "continuation"
      , "recogniser" ∋ Fresh 703 ↦ "\".\""
      , "recogniser" ∋ Fresh 704 ↦ "QuotedString"
      , "recogniser" ∋ Fresh 705 ↦ "sameTerminal"
      , "continuation" ∋ Fresh 706 ↦ Fresh 707
      , "recogniser" ∋ Fresh 706 ↦ "\"[\""
      , "continuation" ∋ Fresh 707 ↦ Fresh 708
      , "recogniser" ∋ Fresh 707 ↦ "recRelation"
      , "continuation" ∋ Fresh 708 ↦ Fresh 709
      , "recogniser" ∋ Fresh 708 ↦ "\"]\""
      , "recogniser" ∋ Fresh 709 ↦ "nonTerminal"
      , "continuation" ∋ Fresh 710 ↦ Fresh 711
      , "recogniser" ∋ Fresh 710 ↦ "\"[\""
      , "continuation" ∋ Fresh 711 ↦ Fresh 712
      , "recogniser" ∋ Fresh 711 ↦ "recRelation"
      , "continuation" ∋ Fresh 712 ↦ Fresh 713
      , "recogniser" ∋ Fresh 712 ↦ "\"SEPBY\""
      , "continuation" ∋ Fresh 713 ↦ Fresh 714
      , "recogniser" ∋ Fresh 713 ↦ "separator"
      , "continuation" ∋ Fresh 714 ↦ Fresh 715
      , "recogniser" ∋ Fresh 714 ↦ "\"]\""
      , "recogniser" ∋ Fresh 715 ↦ "nonTerminal"
      , "rule" ∋ Fresh 716 ↦ Fresh 717
      , "eFst" ∋ Fresh 717 ↦ Fresh 718
      , "eSnd" ∋ Fresh 717 ↦ Fresh 719
      , "pre" ∋ Fresh 718 ↦ "UnquotedString"
      , "rule" ∋ Fresh 720 ↦ Fresh 721
      , "eFst" ∋ Fresh 721 ↦ Fresh 722
      , "eSnd" ∋ Fresh 721 ↦ Fresh 723
      , "pre" ∋ Fresh 722 ↦ "QuotedString"
      , "rule" ∋ Fresh 724 ↦ Fresh 725
      , "eFst" ∋ Fresh 725 ↦ Fresh 726
      , "eSnd" ∋ Fresh 725 ↦ Fresh 727
      , "pre" ∋ Fresh 726 ↦ "sameTerminal"
      , "rule" ∋ Fresh 728 ↦ Fresh 729
      , "eFst" ∋ Fresh 729 ↦ Fresh 730
      , "eSnd" ∋ Fresh 729 ↦ Fresh 731
      , "pre" ∋ Fresh 730 ↦ "recRelation"
      , "rule" ∋ Fresh 732 ↦ Fresh 733
      , "eFst" ∋ Fresh 733 ↦ Fresh 726
      , "eSnd" ∋ Fresh 733 ↦ Fresh 734
      , "pre" ∋ Fresh 734 ↦ "nonTerminal"
      , "eFst" ∋ Fresh 735 ↦ Fresh 738
      , "eSnd" ∋ Fresh 735 ↦ Fresh 905
      , "rule" ∋ Fresh 736 ↦ Fresh 737
      , "eFst" ∋ Fresh 737 ↦ Fresh 738
      , "eSnd" ∋ Fresh 737 ↦ Fresh 739
      , "pre" ∋ Fresh 738 ↦ "I"
      , "eFst" ∋ Fresh 740 ↦ Fresh 906
      , "eSnd" ∋ Fresh 740 ↦ Fresh 835
      , "eFst" ∋ Fresh 741 ↦ Fresh 907
      , "eSnd" ∋ Fresh 741 ↦ Fresh 764
      , "eFst" ∋ Fresh 742 ↦ Fresh 829
      , "eSnd" ∋ Fresh 742 ↦ Fresh 774
      , "eFst" ∋ Fresh 743 ↦ Fresh 908
      , "eSnd" ∋ Fresh 743 ↦ Fresh 761
      , "eFst" ∋ Fresh 744 ↦ Fresh 909
      , "eSnd" ∋ Fresh 744 ↦ Fresh 777
      , "eFst" ∋ Fresh 745 ↦ Fresh 910
      , "eSnd" ∋ Fresh 745 ↦ Fresh 767
      , "eFst" ∋ Fresh 746 ↦ Fresh 911
      , "eSnd" ∋ Fresh 746 ↦ Fresh 840
      , "eFst" ∋ Fresh 747 ↦ Fresh 912
      , "eSnd" ∋ Fresh 747 ↦ Fresh 843
      , "eFst" ∋ Fresh 748 ↦ Fresh 913
      , "eSnd" ∋ Fresh 748 ↦ Fresh 914
      , "eFst" ∋ Fresh 749 ↦ Fresh 915
      , "eSnd" ∋ Fresh 749 ↦ Fresh 824
      , "eFst" ∋ Fresh 750 ↦ Fresh 916
      , "eSnd" ∋ Fresh 750 ↦ Fresh 825
      , "eFst" ∋ Fresh 751 ↦ Fresh 832
      , "eSnd" ∋ Fresh 751 ↦ Fresh 917
      , "eFst" ∋ Fresh 752 ↦ Fresh 795
      , "eSnd" ∋ Fresh 752 ↦ Fresh 918
      , "eFst" ∋ Fresh 753 ↦ Fresh 780
      , "eSnd" ∋ Fresh 753 ↦ Fresh 919
      , "eFst" ∋ Fresh 754 ↦ Fresh 758
      , "eSnd" ∋ Fresh 754 ↦ Fresh 920
      , "eFst" ∋ Fresh 755 ↦ Fresh 828
      , "eSnd" ∋ Fresh 755 ↦ Fresh 921
      , "rule" ∋ Fresh 756 ↦ Fresh 757
      , "eFst" ∋ Fresh 757 ↦ Fresh 758
      , "eSnd" ∋ Fresh 757 ↦ Fresh 759
      , "pre" ∋ Fresh 758 ↦ "mapsTo"
      , "compose" ∋ Fresh 759 ↦ Fresh 760
      , "eFst" ∋ Fresh 760 ↦ Fresh 761
      , "eSnd" ∋ Fresh 760 ↦ Fresh 762
      , "post" ∋ Fresh 761 ↦ "conjunct"
      , "compose" ∋ Fresh 762 ↦ Fresh 763
      , "eFst" ∋ Fresh 763 ↦ Fresh 764
      , "eSnd" ∋ Fresh 763 ↦ Fresh 765
      , "post" ∋ Fresh 764 ↦ "eFst"
      , "compose" ∋ Fresh 765 ↦ Fresh 766
      , "eFst" ∋ Fresh 766 ↦ Fresh 767
      , "eSnd" ∋ Fresh 766 ↦ Fresh 768
      , "post" ∋ Fresh 767 ↦ "compose"
      , "conjunct" ∋ Fresh 768 ↦ Fresh 769
      , "eFst" ∋ Fresh 769 ↦ Fresh 764
      , "eSnd" ∋ Fresh 769 ↦ Fresh 770
      , "compose" ∋ Fresh 770 ↦ Fresh 771
      , "eFst" ∋ Fresh 771 ↦ Fresh 772
      , "eSnd" ∋ Fresh 771 ↦ Fresh 775
      , "compose" ∋ Fresh 772 ↦ Fresh 773
      , "eFst" ∋ Fresh 773 ↦ Fresh 774
      , "eSnd" ∋ Fresh 773 ↦ Fresh 767
      , "post" ∋ Fresh 774 ↦ "eSnd"
      , "compose" ∋ Fresh 775 ↦ Fresh 776
      , "eFst" ∋ Fresh 776 ↦ Fresh 774
      , "eSnd" ∋ Fresh 776 ↦ Fresh 777
      , "post" ∋ Fresh 777 ↦ "converse"
      , "rule" ∋ Fresh 778 ↦ Fresh 779
      , "eFst" ∋ Fresh 779 ↦ Fresh 780
      , "eSnd" ∋ Fresh 779 ↦ Fresh 781
      , "pre" ∋ Fresh 780 ↦ "toPair"
      , "compose" ∋ Fresh 781 ↦ Fresh 782
      , "eFst" ∋ Fresh 782 ↦ Fresh 761
      , "eSnd" ∋ Fresh 782 ↦ Fresh 783
      , "conjunct" ∋ Fresh 783 ↦ Fresh 784
      , "eFst" ∋ Fresh 784 ↦ Fresh 785
      , "eSnd" ∋ Fresh 784 ↦ Fresh 774
      , "compose" ∋ Fresh 785 ↦ Fresh 786
      , "eFst" ∋ Fresh 786 ↦ Fresh 764
      , "eSnd" ∋ Fresh 786 ↦ Fresh 787
      , "compose" ∋ Fresh 787 ↦ Fresh 788
      , "eFst" ∋ Fresh 788 ↦ Fresh 789
      , "eSnd" ∋ Fresh 788 ↦ Fresh 795
      , "compose" ∋ Fresh 789 ↦ Fresh 790
      , "eFst" ∋ Fresh 790 ↦ Fresh 791
      , "eSnd" ∋ Fresh 790 ↦ Fresh 764
      , "compose" ∋ Fresh 791 ↦ Fresh 792
      , "eFst" ∋ Fresh 792 ↦ Fresh 793
      , "eSnd" ∋ Fresh 792 ↦ Fresh 767
      , "compose" ∋ Fresh 793 ↦ Fresh 794
      , "eFst" ∋ Fresh 794 ↦ Fresh 767
      , "eSnd" ∋ Fresh 794 ↦ Fresh 774
      , "pre" ∋ Fresh 795 ↦ "pair"
      , "rule" ∋ Fresh 796 ↦ Fresh 797
      , "eFst" ∋ Fresh 797 ↦ Fresh 798
      , "eSnd" ∋ Fresh 797 ↦ Fresh 801
      , "compose" ∋ Fresh 798 ↦ Fresh 799
      , "eFst" ∋ Fresh 799 ↦ Fresh 800
      , "eSnd" ∋ Fresh 799 ↦ Fresh 767
      , "converse" ∋ Fresh 800 ↦ Fresh 767
      , "rule" ∋ Fresh 802 ↦ Fresh 803
      , "eFst" ∋ Fresh 803 ↦ Fresh 804
      , "eSnd" ∋ Fresh 803 ↦ Fresh 807
      , "compose" ∋ Fresh 804 ↦ Fresh 805
      , "eFst" ∋ Fresh 805 ↦ Fresh 806
      , "eSnd" ∋ Fresh 805 ↦ Fresh 761
      , "converse" ∋ Fresh 806 ↦ Fresh 761
      , "rule" ∋ Fresh 808 ↦ Fresh 809
      , "eFst" ∋ Fresh 809 ↦ Fresh 810
      , "eSnd" ∋ Fresh 809 ↦ Fresh 813
      , "compose" ∋ Fresh 810 ↦ Fresh 811
      , "eFst" ∋ Fresh 811 ↦ Fresh 812
      , "eSnd" ∋ Fresh 811 ↦ Fresh 764
      , "converse" ∋ Fresh 812 ↦ Fresh 764
      , "rule" ∋ Fresh 814 ↦ Fresh 815
      , "eFst" ∋ Fresh 815 ↦ Fresh 816
      , "eSnd" ∋ Fresh 815 ↦ Fresh 819
      , "compose" ∋ Fresh 816 ↦ Fresh 817
      , "eFst" ∋ Fresh 817 ↦ Fresh 818
      , "eSnd" ∋ Fresh 817 ↦ Fresh 774
      , "converse" ∋ Fresh 818 ↦ Fresh 774
      , "rule" ∋ Fresh 820 ↦ Fresh 821
      , "eFst" ∋ Fresh 821 ↦ Fresh 795
      , "eSnd" ∋ Fresh 821 ↦ Fresh 822
      , "conjunct" ∋ Fresh 822 ↦ Fresh 823
      , "eFst" ∋ Fresh 823 ↦ Fresh 824
      , "eSnd" ∋ Fresh 823 ↦ Fresh 825
      , "post" ∋ Fresh 824 ↦ "pair1"
      , "post" ∋ Fresh 825 ↦ "pair2"
      , "rule" ∋ Fresh 826 ↦ Fresh 827
      , "eFst" ∋ Fresh 827 ↦ Fresh 828
      , "eSnd" ∋ Fresh 827 ↦ Fresh 829
      , "pre" ∋ Fresh 828 ↦ "relaxSnd"
      , "pre" ∋ Fresh 829 ↦ "eSnd"
      , "rule" ∋ Fresh 830 ↦ Fresh 831
      , "eFst" ∋ Fresh 831 ↦ Fresh 832
      , "eSnd" ∋ Fresh 831 ↦ Fresh 833
      , "pre" ∋ Fresh 832 ↦ "keep"
      , "compose" ∋ Fresh 833 ↦ Fresh 834
      , "eFst" ∋ Fresh 834 ↦ Fresh 835
      , "eSnd" ∋ Fresh 834 ↦ Fresh 836
      , "post" ∋ Fresh 835 ↦ "rule"
      , "conjunct" ∋ Fresh 836 ↦ Fresh 837
      , "eFst" ∋ Fresh 837 ↦ Fresh 838
      , "eSnd" ∋ Fresh 837 ↦ Fresh 841
      , "compose" ∋ Fresh 838 ↦ Fresh 839
      , "eFst" ∋ Fresh 839 ↦ Fresh 764
      , "eSnd" ∋ Fresh 839 ↦ Fresh 840
      , "post" ∋ Fresh 840 ↦ "pre"
      , "compose" ∋ Fresh 841 ↦ Fresh 842
      , "eFst" ∋ Fresh 842 ↦ Fresh 774
      , "eSnd" ∋ Fresh 842 ↦ Fresh 843
      , "post" ∋ Fresh 843 ↦ "post"
      , "continuation" ∋ Fresh 844 ↦ Fresh 845
      , "recogniser" ∋ Fresh 844 ↦ "\"RULE\""
      , "recogniser" ∋ Fresh 845 ↦ "rule"
      , "continuation" ∋ Fresh 846 ↦ Fresh 847
      , "recogniser" ∋ Fresh 846 ↦ "eFst"
      , "continuation" ∋ Fresh 847 ↦ Fresh 848
      , "recogniser" ∋ Fresh 847 ↦ "\"|-\""
      , "recogniser" ∋ Fresh 848 ↦ "relaxSnd"
      , "continuation" ∋ Fresh 849 ↦ Fresh 850
      , "recogniser" ∋ Fresh 849 ↦ "\"(\""
      , "continuation" ∋ Fresh 850 ↦ Fresh 851
      , "recogniser" ∋ Fresh 850 ↦ "I"
      , "recogniser" ∋ Fresh 851 ↦ "\")\""
      , "recogniser" ∋ Fresh 852 ↦ "conjunct"
      , "recogniser" ∋ Fresh 853 ↦ "compose"
      , "continuation" ∋ Fresh 854 ↦ Fresh 855
      , "recogniser" ∋ Fresh 854 ↦ "converse"
      , "recogniser" ∋ Fresh 855 ↦ "\"~\""
      , "continuation" ∋ Fresh 856 ↦ Fresh 857
      , "recogniser" ∋ Fresh 856 ↦ "\"pre\""
      , "recogniser" ∋ Fresh 857 ↦ "pre"
      , "continuation" ∋ Fresh 858 ↦ Fresh 859
      , "recogniser" ∋ Fresh 858 ↦ "\"post\""
      , "recogniser" ∋ Fresh 859 ↦ "post"
      , "continuation" ∋ Fresh 860 ↦ Fresh 861
      , "recogniser" ∋ Fresh 860 ↦ "\"during\""
      , "recogniser" ∋ Fresh 861 ↦ "during"
      , "continuation" ∋ Fresh 862 ↦ Fresh 863
      , "recogniser" ∋ Fresh 862 ↦ "\"[\""
      , "continuation" ∋ Fresh 863 ↦ Fresh 864
      , "recogniser" ∋ Fresh 863 ↦ "mapsTo"
      , "continuation" ∋ Fresh 864 ↦ Fresh 865
      , "recogniser" ∋ Fresh 864 ↦ "\"->\""
      , "continuation" ∋ Fresh 865 ↦ Fresh 866
      , "recogniser" ∋ Fresh 865 ↦ "toPair"
      , "recogniser" ∋ Fresh 866 ↦ "\"]\""
      , "continuation" ∋ Fresh 867 ↦ Fresh 868
      , "recogniser" ∋ Fresh 867 ↦ "\"<\""
      , "continuation" ∋ Fresh 868 ↦ Fresh 869
      , "recogniser" ∋ Fresh 868 ↦ "pair1"
      , "continuation" ∋ Fresh 869 ↦ Fresh 870
      , "recogniser" ∋ Fresh 869 ↦ "\",\""
      , "continuation" ∋ Fresh 870 ↦ Fresh 871
      , "recogniser" ∋ Fresh 870 ↦ "pair2"
      , "recogniser" ∋ Fresh 871 ↦ "\">\""
      , "continuation" ∋ Fresh 872 ↦ Fresh 873
      , "recogniser" ∋ Fresh 872 ↦ "\"<\""
      , "continuation" ∋ Fresh 873 ↦ Fresh 874
      , "recogniser" ∋ Fresh 873 ↦ "pair"
      , "recogniser" ∋ Fresh 874 ↦ "\">\""
      , "recogniser" ∋ Fresh 875 ↦ "\"I\""
      , "continuation" ∋ Fresh 876 ↦ Fresh 877
      , "recogniser" ∋ Fresh 876 ↦ "eFst"
      , "continuation" ∋ Fresh 877 ↦ Fresh 878
      , "recogniser" ∋ Fresh 877 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 878 ↦ "eSnd"
      , "continuation" ∋ Fresh 879 ↦ Fresh 880
      , "recogniser" ∋ Fresh 879 ↦ "eFst"
      , "continuation" ∋ Fresh 880 ↦ Fresh 881
      , "recogniser" ∋ Fresh 880 ↦ "\";\""
      , "recogniser" ∋ Fresh 881 ↦ "eSnd"
      , "continuation" ∋ Fresh 882 ↦ Fresh 883
      , "recogniser" ∋ Fresh 882 ↦ "\"KEEP\""
      , "recogniser" ∋ Fresh 883 ↦ "keep"
      , "post" ∋ Fresh 884 ↦ "origin"
      , "pre" ∋ Fresh 885 ↦ "origin"
      , "post" ∋ Fresh 886 ↦ "string"
      , "pre" ∋ Fresh 887 ↦ "string"
      , "pre" ∋ Fresh 888 ↦ "start"
      , "post" ∋ Fresh 889 ↦ "start"
      , "pre" ∋ Fresh 890 ↦ "more"
      , "post" ∋ Fresh 891 ↦ "more"
      , "pre" ∋ Fresh 892 ↦ "choice"
      , "post" ∋ Fresh 893 ↦ "choice"
      , "pre" ∋ Fresh 894 ↦ "continuation"
      , "post" ∋ Fresh 895 ↦ "continuation"
      , "pre" ∋ Fresh 896 ↦ "recogniser"
      , "post" ∋ Fresh 897 ↦ "recogniser"
      , "post" ∋ Fresh 898 ↦ "nonTerminal"
      , "post" ∋ Fresh 899 ↦ "sameTerminal"
      , "post" ∋ Fresh 900 ↦ "UnquotedString"
      , "post" ∋ Fresh 901 ↦ "QuotedString"
      , "post" ∋ Fresh 902 ↦ "recRelation"
      , "pre" ∋ Fresh 903 ↦ "separator"
      , "post" ∋ Fresh 904 ↦ "separator"
      , "post" ∋ Fresh 905 ↦ "I"
      , "pre" ∋ Fresh 906 ↦ "rule"
      , "pre" ∋ Fresh 907 ↦ "eFst"
      , "pre" ∋ Fresh 908 ↦ "conjunct"
      , "pre" ∋ Fresh 909 ↦ "converse"
      , "pre" ∋ Fresh 910 ↦ "compose"
      , "pre" ∋ Fresh 911 ↦ "pre"
      , "pre" ∋ Fresh 912 ↦ "post"
      , "pre" ∋ Fresh 913 ↦ "during"
      , "post" ∋ Fresh 914 ↦ "during"
      , "pre" ∋ Fresh 915 ↦ "pair1"
      , "pre" ∋ Fresh 916 ↦ "pair2"
      , "post" ∋ Fresh 917 ↦ "keep"
      , "post" ∋ Fresh 918 ↦ "pair"
      , "post" ∋ Fresh 919 ↦ "toPair"
      , "post" ∋ Fresh 920 ↦ "mapsTo"
      , "post" ∋ Fresh 921 ↦ "relaxSnd"
      ])
  , ( "cfg2"
    , [ "nonTerminal" ∋ "QuotedString" ↦ "QuotedString"
      , "choice" ∋ "Start" ↦ Fresh 1362
      , "choice" ∋ "Start" ↦ Fresh 1368
      , "nonTerminal" ∋ "Start" ↦ "Start"
      , "nonTerminal" ∋ "UnquotedString" ↦ "UnquotedString"
      , "choice" ∋ "choice" ↦ Fresh 1370
      , "nonTerminal" ∋ "choice" ↦ "choice"
      , "choice" ∋ "continuation" ↦ Fresh 1373
      , "choice" ∋ "continuation" ↦ Fresh 1377
      , "nonTerminal" ∋ "continuation" ↦ "continuation"
      , "choice" ∋ "nonTerminal" ↦ Fresh 1386
      , "nonTerminal" ∋ "nonTerminal" ↦ "nonTerminal"
      , "choice" ∋ "recogniser" ↦ Fresh 1380
      , "choice" ∋ "recogniser" ↦ Fresh 1383
      , "nonTerminal" ∋ "recogniser" ↦ "recogniser"
      , "continuation" ∋ Fresh 1362 ↦ Fresh 1363
      , "continuation" ∋ Fresh 1363 ↦ Fresh 1364
      , "recogniser" ∋ Fresh 1363 ↦ "UnquotedString"
      , "continuation" ∋ Fresh 1364 ↦ Fresh 1365
      , "recogniser" ∋ Fresh 1364 ↦ "\">\""
      , "continuation" ∋ Fresh 1365 ↦ Fresh 1366
      , "recogniser" ∋ Fresh 1365 ↦ "choice"
      , "continuation" ∋ Fresh 1366 ↦ Fresh 1367
      , "recogniser" ∋ Fresh 1366 ↦ "Start"
      , "continuation" ∋ Fresh 1368 ↦ Fresh 1369
      , "continuation" ∋ Fresh 1370 ↦ Fresh 1371
      , "continuation" ∋ Fresh 1371 ↦ Fresh 1372
      , "recogniser" ∋ Fresh 1371 ↦ "continuation"
      , "continuation" ∋ Fresh 1373 ↦ Fresh 1374
      , "continuation" ∋ Fresh 1374 ↦ Fresh 1375
      , "recogniser" ∋ Fresh 1374 ↦ "recogniser"
      , "continuation" ∋ Fresh 1375 ↦ Fresh 1376
      , "recogniser" ∋ Fresh 1375 ↦ "continuation"
      , "continuation" ∋ Fresh 1377 ↦ Fresh 1378
      , "continuation" ∋ Fresh 1378 ↦ Fresh 1379
      , "recogniser" ∋ Fresh 1378 ↦ "\".\""
      , "continuation" ∋ Fresh 1380 ↦ Fresh 1381
      , "continuation" ∋ Fresh 1381 ↦ Fresh 1382
      , "recogniser" ∋ Fresh 1381 ↦ "QuotedString"
      , "continuation" ∋ Fresh 1383 ↦ Fresh 1384
      , "continuation" ∋ Fresh 1384 ↦ Fresh 1385
      , "recogniser" ∋ Fresh 1384 ↦ "nonTerminal"
      , "continuation" ∋ Fresh 1386 ↦ Fresh 1387
      , "continuation" ∋ Fresh 1387 ↦ Fresh 1388
      , "recogniser" ∋ Fresh 1387 ↦ "UnquotedString"
      ])
  , ( "parser"
    , [ "choice" ∋ "Classification" ↦ Fresh 1454
      , "choice" ∋ "ClassificationStatement" ↦ Fresh 1451
      , "choice" ∋ "Compose" ↦ Fresh 1524
      , "choice" ∋ "ConceptList" ↦ Fresh 1458
      , "choice" ∋ "ConceptList" ↦ Fresh 1461
      , "choice" ∋ "Conjunct" ↦ Fresh 1521
      , "choice" ∋ "ConsConceptList" ↦ Fresh 1458
      , "choice" ∋ "ConsSyntaxList" ↦ Fresh 1479
      , "choice" ∋ "Declaration" ↦ Fresh 1465
      , "choice" ∋ "DeclarationStatement" ↦ Fresh 1452
      , "choice" ∋ "DeclarationType" ↦ Fresh 1462
      , "choice" ∋ "EmptySyntax" ↦ Fresh 1474
      , "choice" ∋ "Expression" ↦ Fresh 1501
      , "choice" ∋ "Expression" ↦ Fresh 1504
      , "choice" ∋ "Expression" ↦ Fresh 1507
      , "choice" ∋ "Expression" ↦ Fresh 1509
      , "choice" ∋ "Expression" ↦ Fresh 1511
      , "choice" ∋ "Expression" ↦ Fresh 1513
      , "choice" ∋ "Expression" ↦ Fresh 1515
      , "choice" ∋ "Expression" ↦ Fresh 1520
      , "continuation" ∋ "NextStatement" ↦ "gotoStart"
      , "recogniser" ∋ "NextStatement" ↦ "Statement"
      , "choice" ∋ "QuotedStringElement" ↦ Fresh 1483
      , "choice" ∋ "RelationElement" ↦ Fresh 1484
      , "choice" ∋ "RuleStatement" ↦ Fresh 1496
      , "choice" ∋ "RuleSubset" ↦ Fresh 1498
      , "choice" ∋ "Start" ↦ "NextStatement"
      , "choice" ∋ "Start" ↦ "endOfFile"
      , "nonTerminal" ∋ "Start" ↦ "Start"
      , "choice" ∋ "Statement" ↦ Fresh 1451
      , "choice" ∋ "Statement" ↦ Fresh 1452
      , "choice" ∋ "Statement" ↦ Fresh 1453
      , "choice" ∋ "Statement" ↦ Fresh 1496
      , "nonTerminal" ∋ "Statement" ↦ "Statement"
      , "choice" ∋ "Syntax" ↦ Fresh 1468
      , "choice" ∋ "Syntax" ↦ Fresh 1474
      , "choice" ∋ "SyntaxElement" ↦ Fresh 1483
      , "choice" ∋ "SyntaxElement" ↦ Fresh 1484
      , "choice" ∋ "SyntaxList" ↦ Fresh 1479
      , "choice" ∋ "SyntaxList" ↦ Fresh 1482
      , "choice" ∋ "SyntaxStatement" ↦ Fresh 1453
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 1498
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 1521
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 1524
      , "nonTerminal" ∋ "classification" ↦ "Classification"
      , "rule" ∋ "classification" ↦ Fresh 1434
      , "nonTerminal" ∋ "compose" ↦ "Compose"
      , "rule" ∋ "compose" ↦ Fresh 1490
      , "nonTerminal" ∋ "concept" ↦ "String"
      , "rule" ∋ "concept" ↦ Fresh 1445
      , "nonTerminal" ∋ "conceptList" ↦ "ConceptList"
      , "rule" ∋ "conceptList" ↦ Fresh 1436
      , "nonTerminal" ∋ "concepts" ↦ "DeclarationType"
      , "rule" ∋ "concepts" ↦ Fresh 1441
      , "nonTerminal" ∋ "conjunct" ↦ "Conjunct"
      , "rule" ∋ "conjunct" ↦ Fresh 1488
      , "nonTerminal" ∋ "converse" ↦ "Expression"
      , "rule" ∋ "converse" ↦ Fresh 1489
      , "nonTerminal" ∋ "declaration" ↦ "Declaration"
      , "rule" ∋ "declaration" ↦ Fresh 1439
      , "nonTerminal" ∋ "during" ↦ "UnquotedString"
      , "rule" ∋ "during" ↦ Fresh 1493
      , "nonTerminal" ∋ "eFst" ↦ "Expression"
      , "rule" ∋ "eFst" ↦ Fresh 1486
      , "nonTerminal" ∋ "eSnd" ↦ "Expression"
      , "rule" ∋ "eSnd" ↦ Fresh 1487
      , "nonTerminal" ∋ "fst" ↦ "String"
      , "rule" ∋ "fst" ↦ Fresh 1442
      , "recogniser" ∋ "gotoStart" ↦ "Start"
      , "nonTerminal" ∋ "head1" ↦ "String"
      , "rule" ∋ "head1" ↦ Fresh 1437
      , "nonTerminal" ∋ "head2" ↦ "SyntaxElement"
      , "rule" ∋ "head2" ↦ Fresh 1448
      , "eFst" ∋ "keepOrigin" ↦ Fresh 1528
      , "eSnd" ∋ "keepOrigin" ↦ Fresh 1527
      , "rule" ∋ "keepOrigin" ↦ "keepOrigin"
      , "eFst" ∋ "keepString" ↦ Fresh 1530
      , "eSnd" ∋ "keepString" ↦ Fresh 1529
      , "rule" ∋ "keepString" ↦ "keepString"
      , "nonTerminal" ∋ "mainConcept" ↦ "String"
      , "rule" ∋ "mainConcept" ↦ Fresh 1435
      , "nonTerminal" ∋ "pair1" ↦ "String"
      , "rule" ∋ "pair1" ↦ Fresh 1494
      , "nonTerminal" ∋ "pair2" ↦ "String"
      , "rule" ∋ "pair2" ↦ Fresh 1495
      , "nonTerminal" ∋ "post" ↦ "UnquotedString"
      , "rule" ∋ "post" ↦ Fresh 1492
      , "nonTerminal" ∋ "pre" ↦ "UnquotedString"
      , "rule" ∋ "pre" ↦ Fresh 1491
      , "nonTerminal" ∋ "qstring" ↦ "QuotedString"
      , "rule" ∋ "qstring" ↦ Fresh 1450
      , "nonTerminal" ∋ "relation" ↦ "StringAndOrigin"
      , "rule" ∋ "relation" ↦ Fresh 1440
      , "nonTerminal" ∋ "relationName" ↦ "UnquotedString"
      , "rule" ∋ "relationName" ↦ Fresh 1446
      , "nonTerminal" ∋ "rule" ↦ "RuleSubset"
      , "rule" ∋ "rule" ↦ Fresh 1485
      , "nonTerminal" ∋ "snd" ↦ "String"
      , "rule" ∋ "snd" ↦ Fresh 1443
      , "nonTerminal" ∋ "syntax" ↦ "Syntax"
      , "rule" ∋ "syntax" ↦ Fresh 1444
      , "nonTerminal" ∋ "syntaxList" ↦ "SyntaxList"
      , "rule" ∋ "syntaxList" ↦ Fresh 1447
      , "nonTerminal" ∋ "tail1" ↦ "ConceptList"
      , "rule" ∋ "tail1" ↦ Fresh 1438
      , "nonTerminal" ∋ "tail2" ↦ "SyntaxList"
      , "rule" ∋ "tail2" ↦ Fresh 1449
      , "eFst" ∋ Fresh 1434 ↦ Fresh 1531
      , "eSnd" ∋ Fresh 1434 ↦ Fresh 1532
      , "eFst" ∋ Fresh 1435 ↦ Fresh 1533
      , "eSnd" ∋ Fresh 1435 ↦ Fresh 1534
      , "eFst" ∋ Fresh 1436 ↦ Fresh 1535
      , "eSnd" ∋ Fresh 1436 ↦ Fresh 1536
      , "eFst" ∋ Fresh 1437 ↦ Fresh 1537
      , "eSnd" ∋ Fresh 1437 ↦ Fresh 1538
      , "eFst" ∋ Fresh 1438 ↦ Fresh 1539
      , "eSnd" ∋ Fresh 1438 ↦ Fresh 1540
      , "eFst" ∋ Fresh 1439 ↦ Fresh 1541
      , "eSnd" ∋ Fresh 1439 ↦ Fresh 1542
      , "eFst" ∋ Fresh 1440 ↦ Fresh 1543
      , "eSnd" ∋ Fresh 1440 ↦ Fresh 1544
      , "eFst" ∋ Fresh 1441 ↦ Fresh 1545
      , "eSnd" ∋ Fresh 1441 ↦ Fresh 1546
      , "eFst" ∋ Fresh 1442 ↦ Fresh 1547
      , "eSnd" ∋ Fresh 1442 ↦ Fresh 1548
      , "eFst" ∋ Fresh 1443 ↦ Fresh 1549
      , "eSnd" ∋ Fresh 1443 ↦ Fresh 1550
      , "eFst" ∋ Fresh 1444 ↦ Fresh 1551
      , "eSnd" ∋ Fresh 1444 ↦ Fresh 1552
      , "eFst" ∋ Fresh 1445 ↦ Fresh 1553
      , "eSnd" ∋ Fresh 1445 ↦ Fresh 1554
      , "eFst" ∋ Fresh 1446 ↦ Fresh 1555
      , "eSnd" ∋ Fresh 1446 ↦ Fresh 1556
      , "eFst" ∋ Fresh 1447 ↦ Fresh 1557
      , "eSnd" ∋ Fresh 1447 ↦ Fresh 1558
      , "eFst" ∋ Fresh 1448 ↦ Fresh 1559
      , "eSnd" ∋ Fresh 1448 ↦ Fresh 1560
      , "eFst" ∋ Fresh 1449 ↦ Fresh 1561
      , "eSnd" ∋ Fresh 1449 ↦ Fresh 1562
      , "eFst" ∋ Fresh 1450 ↦ Fresh 1563
      , "eSnd" ∋ Fresh 1450 ↦ Fresh 1564
      , "recogniser" ∋ Fresh 1451 ↦ "classification"
      , "recogniser" ∋ Fresh 1452 ↦ "declaration"
      , "recogniser" ∋ Fresh 1453 ↦ "syntax"
      , "continuation" ∋ Fresh 1454 ↦ Fresh 1455
      , "recogniser" ∋ Fresh 1454 ↦ "\"CLASSIFY\""
      , "continuation" ∋ Fresh 1455 ↦ Fresh 1456
      , "recogniser" ∋ Fresh 1455 ↦ "mainConcept"
      , "continuation" ∋ Fresh 1456 ↦ Fresh 1457
      , "recogniser" ∋ Fresh 1456 ↦ "\"IS\""
      , "recogniser" ∋ Fresh 1457 ↦ "conceptList"
      , "continuation" ∋ Fresh 1458 ↦ Fresh 1459
      , "recogniser" ∋ Fresh 1458 ↦ "head1"
      , "continuation" ∋ Fresh 1459 ↦ Fresh 1460
      , "recogniser" ∋ Fresh 1459 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 1460 ↦ "tail1"
      , "recogniser" ∋ Fresh 1461 ↦ "head1"
      , "continuation" ∋ Fresh 1462 ↦ Fresh 1463
      , "recogniser" ∋ Fresh 1462 ↦ "fst"
      , "continuation" ∋ Fresh 1463 ↦ Fresh 1464
      , "recogniser" ∋ Fresh 1463 ↦ "\"*\""
      , "recogniser" ∋ Fresh 1464 ↦ "snd"
      , "continuation" ∋ Fresh 1465 ↦ Fresh 1466
      , "recogniser" ∋ Fresh 1465 ↦ "relation"
      , "continuation" ∋ Fresh 1466 ↦ Fresh 1467
      , "recogniser" ∋ Fresh 1466 ↦ "\"::\""
      , "recogniser" ∋ Fresh 1467 ↦ "concepts"
      , "continuation" ∋ Fresh 1468 ↦ Fresh 1469
      , "recogniser" ∋ Fresh 1468 ↦ "\"VIEW\""
      , "continuation" ∋ Fresh 1469 ↦ Fresh 1470
      , "recogniser" ∋ Fresh 1469 ↦ "concept"
      , "continuation" ∋ Fresh 1470 ↦ Fresh 1471
      , "recogniser" ∋ Fresh 1470 ↦ "\"=\""
      , "continuation" ∋ Fresh 1471 ↦ Fresh 1472
      , "recogniser" ∋ Fresh 1471 ↦ "\"[\""
      , "continuation" ∋ Fresh 1472 ↦ Fresh 1473
      , "recogniser" ∋ Fresh 1472 ↦ "syntaxList"
      , "recogniser" ∋ Fresh 1473 ↦ "\"]\""
      , "continuation" ∋ Fresh 1474 ↦ Fresh 1475
      , "recogniser" ∋ Fresh 1474 ↦ "\"VIEW\""
      , "continuation" ∋ Fresh 1475 ↦ Fresh 1476
      , "recogniser" ∋ Fresh 1475 ↦ "concept"
      , "continuation" ∋ Fresh 1476 ↦ Fresh 1477
      , "recogniser" ∋ Fresh 1476 ↦ "\"=\""
      , "continuation" ∋ Fresh 1477 ↦ Fresh 1478
      , "recogniser" ∋ Fresh 1477 ↦ "\"[\""
      , "recogniser" ∋ Fresh 1478 ↦ "\"]\""
      , "continuation" ∋ Fresh 1479 ↦ Fresh 1480
      , "recogniser" ∋ Fresh 1479 ↦ "head2"
      , "continuation" ∋ Fresh 1480 ↦ Fresh 1481
      , "recogniser" ∋ Fresh 1480 ↦ "\",\""
      , "recogniser" ∋ Fresh 1481 ↦ "tail2"
      , "recogniser" ∋ Fresh 1482 ↦ "head2"
      , "recogniser" ∋ Fresh 1483 ↦ "qstring"
      , "recogniser" ∋ Fresh 1484 ↦ "relationName"
      , "eFst" ∋ Fresh 1485 ↦ Fresh 1565
      , "eSnd" ∋ Fresh 1485 ↦ Fresh 1566
      , "eFst" ∋ Fresh 1486 ↦ Fresh 1567
      , "eSnd" ∋ Fresh 1486 ↦ Fresh 1568
      , "eFst" ∋ Fresh 1487 ↦ Fresh 1569
      , "eSnd" ∋ Fresh 1487 ↦ Fresh 1570
      , "eFst" ∋ Fresh 1488 ↦ Fresh 1571
      , "eSnd" ∋ Fresh 1488 ↦ Fresh 1572
      , "eFst" ∋ Fresh 1489 ↦ Fresh 1573
      , "eSnd" ∋ Fresh 1489 ↦ Fresh 1574
      , "eFst" ∋ Fresh 1490 ↦ Fresh 1575
      , "eSnd" ∋ Fresh 1490 ↦ Fresh 1576
      , "eFst" ∋ Fresh 1491 ↦ Fresh 1577
      , "eSnd" ∋ Fresh 1491 ↦ Fresh 1578
      , "eFst" ∋ Fresh 1492 ↦ Fresh 1579
      , "eSnd" ∋ Fresh 1492 ↦ Fresh 1580
      , "eFst" ∋ Fresh 1493 ↦ Fresh 1581
      , "eSnd" ∋ Fresh 1493 ↦ Fresh 1582
      , "eFst" ∋ Fresh 1494 ↦ Fresh 1583
      , "eSnd" ∋ Fresh 1494 ↦ Fresh 1584
      , "eFst" ∋ Fresh 1495 ↦ Fresh 1585
      , "eSnd" ∋ Fresh 1495 ↦ Fresh 1586
      , "continuation" ∋ Fresh 1496 ↦ Fresh 1497
      , "recogniser" ∋ Fresh 1496 ↦ "\"RULE\""
      , "recogniser" ∋ Fresh 1497 ↦ "rule"
      , "continuation" ∋ Fresh 1498 ↦ Fresh 1499
      , "recogniser" ∋ Fresh 1498 ↦ "eFst"
      , "continuation" ∋ Fresh 1499 ↦ Fresh 1500
      , "recogniser" ∋ Fresh 1499 ↦ "\"|-\""
      , "recogniser" ∋ Fresh 1500 ↦ "eSnd"
      , "continuation" ∋ Fresh 1501 ↦ Fresh 1502
      , "recogniser" ∋ Fresh 1501 ↦ "\"(\""
      , "continuation" ∋ Fresh 1502 ↦ Fresh 1503
      , "recogniser" ∋ Fresh 1502 ↦ "conjunct"
      , "recogniser" ∋ Fresh 1503 ↦ "\")\""
      , "continuation" ∋ Fresh 1504 ↦ Fresh 1505
      , "recogniser" ∋ Fresh 1504 ↦ "\"(\""
      , "continuation" ∋ Fresh 1505 ↦ Fresh 1506
      , "recogniser" ∋ Fresh 1505 ↦ "compose"
      , "recogniser" ∋ Fresh 1506 ↦ "\")\""
      , "continuation" ∋ Fresh 1507 ↦ Fresh 1508
      , "recogniser" ∋ Fresh 1507 ↦ "converse"
      , "recogniser" ∋ Fresh 1508 ↦ "\"~\""
      , "continuation" ∋ Fresh 1509 ↦ Fresh 1510
      , "recogniser" ∋ Fresh 1509 ↦ "\"pre\""
      , "recogniser" ∋ Fresh 1510 ↦ "pre"
      , "continuation" ∋ Fresh 1511 ↦ Fresh 1512
      , "recogniser" ∋ Fresh 1511 ↦ "\"post\""
      , "recogniser" ∋ Fresh 1512 ↦ "post"
      , "continuation" ∋ Fresh 1513 ↦ Fresh 1514
      , "recogniser" ∋ Fresh 1513 ↦ "\"during\""
      , "recogniser" ∋ Fresh 1514 ↦ "during"
      , "continuation" ∋ Fresh 1515 ↦ Fresh 1516
      , "recogniser" ∋ Fresh 1515 ↦ "\"<\""
      , "continuation" ∋ Fresh 1516 ↦ Fresh 1517
      , "recogniser" ∋ Fresh 1516 ↦ "pair1"
      , "continuation" ∋ Fresh 1517 ↦ Fresh 1518
      , "recogniser" ∋ Fresh 1517 ↦ "\",\""
      , "continuation" ∋ Fresh 1518 ↦ Fresh 1519
      , "recogniser" ∋ Fresh 1518 ↦ "pair2"
      , "recogniser" ∋ Fresh 1519 ↦ "\">\""
      , "recogniser" ∋ Fresh 1520 ↦ "\"I\""
      , "continuation" ∋ Fresh 1521 ↦ Fresh 1522
      , "recogniser" ∋ Fresh 1521 ↦ "eFst"
      , "continuation" ∋ Fresh 1522 ↦ Fresh 1523
      , "recogniser" ∋ Fresh 1522 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 1523 ↦ "eSnd"
      , "continuation" ∋ Fresh 1524 ↦ Fresh 1525
      , "recogniser" ∋ Fresh 1524 ↦ "eFst"
      , "continuation" ∋ Fresh 1525 ↦ Fresh 1526
      , "recogniser" ∋ Fresh 1525 ↦ "\";\""
      , "recogniser" ∋ Fresh 1526 ↦ "eSnd"
      , "post" ∋ Fresh 1527 ↦ "origin"
      , "pre" ∋ Fresh 1528 ↦ "origin"
      , "post" ∋ Fresh 1529 ↦ "string"
      , "pre" ∋ Fresh 1530 ↦ "string"
      , "pre" ∋ Fresh 1531 ↦ "classification"
      , "post" ∋ Fresh 1532 ↦ "classification"
      , "pre" ∋ Fresh 1533 ↦ "mainConcept"
      , "post" ∋ Fresh 1534 ↦ "mainConcept"
      , "pre" ∋ Fresh 1535 ↦ "conceptList"
      , "post" ∋ Fresh 1536 ↦ "conceptList"
      , "pre" ∋ Fresh 1537 ↦ "head1"
      , "post" ∋ Fresh 1538 ↦ "head1"
      , "pre" ∋ Fresh 1539 ↦ "tail1"
      , "post" ∋ Fresh 1540 ↦ "tail1"
      , "pre" ∋ Fresh 1541 ↦ "declaration"
      , "post" ∋ Fresh 1542 ↦ "declaration"
      , "pre" ∋ Fresh 1543 ↦ "relation"
      , "post" ∋ Fresh 1544 ↦ "relation"
      , "pre" ∋ Fresh 1545 ↦ "concepts"
      , "post" ∋ Fresh 1546 ↦ "concepts"
      , "pre" ∋ Fresh 1547 ↦ "fst"
      , "post" ∋ Fresh 1548 ↦ "fst"
      , "pre" ∋ Fresh 1549 ↦ "snd"
      , "post" ∋ Fresh 1550 ↦ "snd"
      , "pre" ∋ Fresh 1551 ↦ "syntax"
      , "post" ∋ Fresh 1552 ↦ "syntax"
      , "pre" ∋ Fresh 1553 ↦ "concept"
      , "post" ∋ Fresh 1554 ↦ "concept"
      , "pre" ∋ Fresh 1555 ↦ "relationName"
      , "post" ∋ Fresh 1556 ↦ "relationName"
      , "pre" ∋ Fresh 1557 ↦ "syntaxList"
      , "post" ∋ Fresh 1558 ↦ "syntaxList"
      , "pre" ∋ Fresh 1559 ↦ "head2"
      , "post" ∋ Fresh 1560 ↦ "head2"
      , "pre" ∋ Fresh 1561 ↦ "tail2"
      , "post" ∋ Fresh 1562 ↦ "tail2"
      , "pre" ∋ Fresh 1563 ↦ "qstring"
      , "post" ∋ Fresh 1564 ↦ "qstring"
      , "pre" ∋ Fresh 1565 ↦ "rule"
      , "post" ∋ Fresh 1566 ↦ "rule"
      , "pre" ∋ Fresh 1567 ↦ "eFst"
      , "post" ∋ Fresh 1568 ↦ "eFst"
      , "pre" ∋ Fresh 1569 ↦ "eSnd"
      , "post" ∋ Fresh 1570 ↦ "eSnd"
      , "pre" ∋ Fresh 1571 ↦ "conjunct"
      , "post" ∋ Fresh 1572 ↦ "conjunct"
      , "pre" ∋ Fresh 1573 ↦ "converse"
      , "post" ∋ Fresh 1574 ↦ "converse"
      , "pre" ∋ Fresh 1575 ↦ "compose"
      , "post" ∋ Fresh 1576 ↦ "compose"
      , "pre" ∋ Fresh 1577 ↦ "pre"
      , "post" ∋ Fresh 1578 ↦ "pre"
      , "pre" ∋ Fresh 1579 ↦ "post"
      , "post" ∋ Fresh 1580 ↦ "post"
      , "pre" ∋ Fresh 1581 ↦ "during"
      , "post" ∋ Fresh 1582 ↦ "during"
      , "pre" ∋ Fresh 1583 ↦ "pair1"
      , "post" ∋ Fresh 1584 ↦ "pair1"
      , "pre" ∋ Fresh 1585 ↦ "pair2"
      , "post" ∋ Fresh 1586 ↦ "pair2"
      ])
  , ( "rules"
    , [ "rule" ∋ Fresh 1914 ↦ Fresh 1915
      , "eFst" ∋ Fresh 1915 ↦ Fresh 1916
      , "eSnd" ∋ Fresh 1915 ↦ Fresh 1917
      , "relaxSnd" ∋ Fresh 1915 ↦ Fresh 1917
      , "pre" ∋ Fresh 1916 ↦ "UnquotedString"
      , "rule" ∋ Fresh 1918 ↦ Fresh 1919
      , "eFst" ∋ Fresh 1919 ↦ Fresh 1920
      , "eSnd" ∋ Fresh 1919 ↦ Fresh 1921
      , "relaxSnd" ∋ Fresh 1919 ↦ Fresh 1921
      , "pre" ∋ Fresh 1920 ↦ "QuotedString"
      , "rule" ∋ Fresh 1922 ↦ Fresh 1923
      , "eFst" ∋ Fresh 1923 ↦ Fresh 1924
      , "eSnd" ∋ Fresh 1923 ↦ Fresh 1925
      , "relaxSnd" ∋ Fresh 1923 ↦ Fresh 1925
      , "pre" ∋ Fresh 1924 ↦ "nonTerminal"
      , "keep" ∋ Fresh 1926 ↦ "choice"
      , "rule" ∋ Fresh 1926 ↦ Fresh 1930
      , "keep" ∋ Fresh 1927 ↦ "continuation"
      , "rule" ∋ Fresh 1927 ↦ Fresh 1933
      , "keep" ∋ Fresh 1928 ↦ "recogniser"
      , "rule" ∋ Fresh 1928 ↦ Fresh 1936
      , "keep" ∋ Fresh 1929 ↦ "nonTerminal"
      , "rule" ∋ Fresh 1929 ↦ Fresh 1939
      , "eFst" ∋ Fresh 1930 ↦ Fresh 1932
      , "eSnd" ∋ Fresh 1930 ↦ Fresh 1931
      , "post" ∋ Fresh 1931 ↦ "choice"
      , "pre" ∋ Fresh 1932 ↦ "choice"
      , "eFst" ∋ Fresh 1933 ↦ Fresh 1935
      , "eSnd" ∋ Fresh 1933 ↦ Fresh 1934
      , "post" ∋ Fresh 1934 ↦ "continuation"
      , "pre" ∋ Fresh 1935 ↦ "continuation"
      , "eFst" ∋ Fresh 1936 ↦ Fresh 1938
      , "eSnd" ∋ Fresh 1936 ↦ Fresh 1937
      , "post" ∋ Fresh 1937 ↦ "recogniser"
      , "pre" ∋ Fresh 1938 ↦ "recogniser"
      , "eFst" ∋ Fresh 1939 ↦ Fresh 1941
      , "eSnd" ∋ Fresh 1939 ↦ Fresh 1940
      , "post" ∋ Fresh 1940 ↦ "nonTerminal"
      , "pre" ∋ Fresh 1941 ↦ "nonTerminal"
      ])
  , ( "switches"
    , [ "cur" ∋ Fresh 1981 ↦ Fresh 1981
      , "first" ∋ Fresh 1981 ↦ Fresh 1991
      , "next" ∋ Fresh 1981 ↦ Fresh 1982
      , "string" ∋ Fresh 1981 ↦ "\"i\""
      , "next" ∋ Fresh 1982 ↦ Fresh 1983
      , "string" ∋ Fresh 1982 ↦ "\"asParser\""
      , "first" ∋ Fresh 1983 ↦ Fresh 1992
      , "next" ∋ Fresh 1983 ↦ Fresh 1984
      , "string" ∋ Fresh 1983 ↦ "\"i\""
      , "first" ∋ Fresh 1984 ↦ Fresh 1993
      , "next" ∋ Fresh 1984 ↦ Fresh 1985
      , "string" ∋ Fresh 1984 ↦ "\"apply\""
      , "first" ∋ Fresh 1985 ↦ Fresh 1996
      , "next" ∋ Fresh 1985 ↦ Fresh 1986
      , "string" ∋ Fresh 1985 ↦ "\"i\""
      , "first" ∋ Fresh 1986 ↦ Fresh 1997
      , "next" ∋ Fresh 1986 ↦ Fresh 1987
      , "string" ∋ Fresh 1986 ↦ "\"apply\""
      , "first" ∋ Fresh 1987 ↦ Fresh 2000
      , "next" ∋ Fresh 1987 ↦ Fresh 1988
      , "string" ∋ Fresh 1987 ↦ "\"apply\""
      , "first" ∋ Fresh 1988 ↦ Fresh 2002
      , "next" ∋ Fresh 1988 ↦ Fresh 1989
      , "string" ∋ Fresh 1988 ↦ "\"apply\""
      , "first" ∋ Fresh 1989 ↦ Fresh 2004
      , "next" ∋ Fresh 1989 ↦ Fresh 1990
      , "string" ∋ Fresh 1989 ↦ "\"collect\""
      , "first" ∋ Fresh 1990 ↦ Fresh 2005
      , "string" ∋ Fresh 1990 ↦ "\"showTS\""
      , "string" ∋ Fresh 1991 ↦ "\"boot.ASL\""
      , "string" ∋ Fresh 1992 ↦ "\"asParser.ASL\""
      , "next" ∋ Fresh 1993 ↦ Fresh 1994
      , "string" ∋ Fresh 1993 ↦ "\"parser\""
      , "next" ∋ Fresh 1994 ↦ Fresh 1995
      , "string" ∋ Fresh 1994 ↦ "\"population\""
      , "string" ∋ Fresh 1995 ↦ "\"asParser\""
      , "string" ∋ Fresh 1996 ↦ "\"cfg.ASL\""
      , "next" ∋ Fresh 1997 ↦ Fresh 1998
      , "string" ∋ Fresh 1997 ↦ "\"asParser\""
      , "next" ∋ Fresh 1998 ↦ Fresh 1999
      , "string" ∋ Fresh 1998 ↦ "\"population\""
      , "string" ∋ Fresh 1999 ↦ "\"cfg\""
      , "next" ∋ Fresh 2000 ↦ Fresh 2001
      , "string" ∋ Fresh 2000 ↦ "\"del\""
      , "string" ∋ Fresh 2001 ↦ "\"switches\""
      , "next" ∋ Fresh 2002 ↦ Fresh 2003
      , "string" ∋ Fresh 2002 ↦ "\"del\""
      , "string" ∋ Fresh 2003 ↦ "\"population\""
      , "string" ∋ Fresh 2004 ↦ "\"state\""
      , "string" ∋ Fresh 2005 ↦ "\"state\""
      ])
  ];}
