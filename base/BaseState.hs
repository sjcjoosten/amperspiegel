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
    , [ "choice" ∋ "Choice" ↦ Fresh 695
      , "choice" ∋ "Compose" ↦ Fresh 859
      , "choice" ∋ "Conjunct" ↦ Fresh 856
      , "choice" ∋ "Continuation" ↦ Fresh 698
      , "choice" ∋ "Continuation" ↦ Fresh 700
      , "choice" ∋ "Expression" ↦ Fresh 829
      , "choice" ∋ "Expression" ↦ Fresh 832
      , "choice" ∋ "Expression" ↦ Fresh 833
      , "choice" ∋ "Expression" ↦ Fresh 834
      , "choice" ∋ "Expression" ↦ Fresh 836
      , "choice" ∋ "Expression" ↦ Fresh 838
      , "choice" ∋ "Expression" ↦ Fresh 840
      , "choice" ∋ "Expression" ↦ Fresh 842
      , "choice" ∋ "Expression" ↦ Fresh 847
      , "choice" ∋ "Expression" ↦ Fresh 852
      , "choice" ∋ "Expression" ↦ Fresh 855
      , "nonTerminal" ∋ "I" ↦ "Expression"
      , "rule" ∋ "I" ↦ Fresh 715
      , "choice" ∋ "KeepStatement" ↦ Fresh 862
      , "continuation" ∋ "NextStatement" ↦ "gotoStart"
      , "recogniser" ∋ "NextStatement" ↦ "Statement"
      , "choice" ∋ "PreExpression" ↦ Fresh 829
      , "choice" ∋ "PreExpression" ↦ Fresh 836
      , "choice" ∋ "PreExpression" ↦ Fresh 838
      , "choice" ∋ "PreExpression" ↦ Fresh 840
      , "choice" ∋ "PreExpression" ↦ Fresh 842
      , "nonTerminal" ∋ "QuotedString" ↦ "QuotedString"
      , "rule" ∋ "QuotedString" ↦ Fresh 693
      , "choice" ∋ "Recogniser" ↦ Fresh 701
      , "choice" ∋ "Recogniser" ↦ Fresh 702
      , "choice" ∋ "RuleStatement" ↦ Fresh 824
      , "choice" ∋ "RuleSubset" ↦ Fresh 826
      , "choice" ∋ "Start" ↦ "NextStatement"
      , "choice" ∋ "Start" ↦ "endOfFile"
      , "nonTerminal" ∋ "Start" ↦ "Start"
      , "choice" ∋ "Statement" ↦ Fresh 694
      , "choice" ∋ "Statement" ↦ Fresh 824
      , "choice" ∋ "Statement" ↦ Fresh 862
      , "nonTerminal" ∋ "Statement" ↦ "Statement"
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 826
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 856
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 859
      , "choice" ∋ "UnaryExpression" ↦ Fresh 829
      , "choice" ∋ "UnaryExpression" ↦ Fresh 834
      , "choice" ∋ "UnaryExpression" ↦ Fresh 836
      , "choice" ∋ "UnaryExpression" ↦ Fresh 838
      , "choice" ∋ "UnaryExpression" ↦ Fresh 840
      , "choice" ∋ "UnaryExpression" ↦ Fresh 842
      , "choice" ∋ "UnaryExpression" ↦ Fresh 847
      , "choice" ∋ "UnaryExpression" ↦ Fresh 852
      , "choice" ∋ "UnaryExpression" ↦ Fresh 855
      , "nonTerminal" ∋ "UnquotedString" ↦ "UnquotedString"
      , "rule" ∋ "UnquotedString" ↦ Fresh 692
      , "nonTerminal" ∋ "choice" ↦ "Continuation"
      , "rule" ∋ "choice" ↦ Fresh 688
      , "nonTerminal" ∋ "compose" ↦ "Compose"
      , "rule" ∋ "compose" ↦ Fresh 725
      , "nonTerminal" ∋ "conjunct" ↦ "Conjunct"
      , "rule" ∋ "conjunct" ↦ Fresh 723
      , "nonTerminal" ∋ "continuation" ↦ "Continuation"
      , "rule" ∋ "continuation" ↦ Fresh 689
      , "nonTerminal" ∋ "converse" ↦ "PreExpression"
      , "rule" ∋ "converse" ↦ Fresh 724
      , "nonTerminal" ∋ "during" ↦ "UnquotedString"
      , "rule" ∋ "during" ↦ Fresh 728
      , "nonTerminal" ∋ "eFst" ↦ "Expression"
      , "rule" ∋ "eFst" ↦ Fresh 721
      , "nonTerminal" ∋ "eSnd" ↦ "UnaryExpression"
      , "rule" ∋ "eSnd" ↦ Fresh 722
      , "recogniser" ∋ "gotoStart" ↦ "Start"
      , "nonTerminal" ∋ "keep" ↦ "UnquotedString"
      , "rule" ∋ "keep" ↦ Fresh 731
      , "eFst" ∋ "keepOrigin" ↦ Fresh 865
      , "eSnd" ∋ "keepOrigin" ↦ Fresh 864
      , "rule" ∋ "keepOrigin" ↦ "keepOrigin"
      , "eFst" ∋ "keepString" ↦ Fresh 867
      , "eSnd" ∋ "keepString" ↦ Fresh 866
      , "rule" ∋ "keepString" ↦ "keepString"
      , "nonTerminal" ∋ "mapsTo" ↦ "Expression"
      , "rule" ∋ "mapsTo" ↦ Fresh 734
      , "nonTerminal" ∋ "more" ↦ "Start"
      , "rule" ∋ "more" ↦ Fresh 687
      , "nonTerminal" ∋ "nonTerminal" ↦ "UnquotedString"
      , "rule" ∋ "nonTerminal" ↦ Fresh 691
      , "nonTerminal" ∋ "pair" ↦ "String"
      , "rule" ∋ "pair" ↦ Fresh 732
      , "nonTerminal" ∋ "pair1" ↦ "String"
      , "rule" ∋ "pair1" ↦ Fresh 729
      , "nonTerminal" ∋ "pair2" ↦ "String"
      , "rule" ∋ "pair2" ↦ Fresh 730
      , "nonTerminal" ∋ "post" ↦ "UnquotedString"
      , "rule" ∋ "post" ↦ Fresh 727
      , "nonTerminal" ∋ "pre" ↦ "UnquotedString"
      , "rule" ∋ "pre" ↦ Fresh 726
      , "nonTerminal" ∋ "recogniser" ↦ "Recogniser"
      , "rule" ∋ "recogniser" ↦ Fresh 690
      , "nonTerminal" ∋ "relaxSnd" ↦ "Expression"
      , "rule" ∋ "relaxSnd" ↦ Fresh 735
      , "nonTerminal" ∋ "rule" ↦ "RuleSubset"
      , "rule" ∋ "rule" ↦ Fresh 720
      , "nonTerminal" ∋ "start" ↦ "Choice"
      , "rule" ∋ "start" ↦ Fresh 686
      , "nonTerminal" ∋ "toPair" ↦ "String"
      , "rule" ∋ "toPair" ↦ Fresh 733
      , "eFst" ∋ Fresh 686 ↦ Fresh 868
      , "eSnd" ∋ Fresh 686 ↦ Fresh 869
      , "eFst" ∋ Fresh 687 ↦ Fresh 870
      , "eSnd" ∋ Fresh 687 ↦ Fresh 871
      , "eFst" ∋ Fresh 688 ↦ Fresh 872
      , "eSnd" ∋ Fresh 688 ↦ Fresh 873
      , "eFst" ∋ Fresh 689 ↦ Fresh 874
      , "eSnd" ∋ Fresh 689 ↦ Fresh 875
      , "eFst" ∋ Fresh 690 ↦ Fresh 876
      , "eSnd" ∋ Fresh 690 ↦ Fresh 877
      , "eFst" ∋ Fresh 691 ↦ Fresh 713
      , "eSnd" ∋ Fresh 691 ↦ Fresh 878
      , "eFst" ∋ Fresh 692 ↦ Fresh 705
      , "eSnd" ∋ Fresh 692 ↦ Fresh 879
      , "eFst" ∋ Fresh 693 ↦ Fresh 709
      , "eSnd" ∋ Fresh 693 ↦ Fresh 880
      , "recogniser" ∋ Fresh 694 ↦ "start"
      , "continuation" ∋ Fresh 695 ↦ Fresh 696
      , "recogniser" ∋ Fresh 695 ↦ "UnquotedString"
      , "continuation" ∋ Fresh 696 ↦ Fresh 697
      , "recogniser" ∋ Fresh 696 ↦ "\">\""
      , "recogniser" ∋ Fresh 697 ↦ "choice"
      , "continuation" ∋ Fresh 698 ↦ Fresh 699
      , "recogniser" ∋ Fresh 698 ↦ "recogniser"
      , "recogniser" ∋ Fresh 699 ↦ "continuation"
      , "recogniser" ∋ Fresh 700 ↦ "\".\""
      , "recogniser" ∋ Fresh 701 ↦ "QuotedString"
      , "recogniser" ∋ Fresh 702 ↦ "nonTerminal"
      , "rule" ∋ Fresh 703 ↦ Fresh 704
      , "eFst" ∋ Fresh 704 ↦ Fresh 705
      , "eSnd" ∋ Fresh 704 ↦ Fresh 706
      , "pre" ∋ Fresh 705 ↦ "UnquotedString"
      , "rule" ∋ Fresh 707 ↦ Fresh 708
      , "eFst" ∋ Fresh 708 ↦ Fresh 709
      , "eSnd" ∋ Fresh 708 ↦ Fresh 710
      , "pre" ∋ Fresh 709 ↦ "QuotedString"
      , "rule" ∋ Fresh 711 ↦ Fresh 712
      , "eFst" ∋ Fresh 712 ↦ Fresh 713
      , "eSnd" ∋ Fresh 712 ↦ Fresh 714
      , "pre" ∋ Fresh 713 ↦ "nonTerminal"
      , "eFst" ∋ Fresh 715 ↦ Fresh 718
      , "eSnd" ∋ Fresh 715 ↦ Fresh 881
      , "rule" ∋ Fresh 716 ↦ Fresh 717
      , "eFst" ∋ Fresh 717 ↦ Fresh 718
      , "eSnd" ∋ Fresh 717 ↦ Fresh 719
      , "pre" ∋ Fresh 718 ↦ "I"
      , "eFst" ∋ Fresh 720 ↦ Fresh 882
      , "eSnd" ∋ Fresh 720 ↦ Fresh 815
      , "eFst" ∋ Fresh 721 ↦ Fresh 883
      , "eSnd" ∋ Fresh 721 ↦ Fresh 744
      , "eFst" ∋ Fresh 722 ↦ Fresh 809
      , "eSnd" ∋ Fresh 722 ↦ Fresh 754
      , "eFst" ∋ Fresh 723 ↦ Fresh 884
      , "eSnd" ∋ Fresh 723 ↦ Fresh 741
      , "eFst" ∋ Fresh 724 ↦ Fresh 885
      , "eSnd" ∋ Fresh 724 ↦ Fresh 757
      , "eFst" ∋ Fresh 725 ↦ Fresh 886
      , "eSnd" ∋ Fresh 725 ↦ Fresh 747
      , "eFst" ∋ Fresh 726 ↦ Fresh 887
      , "eSnd" ∋ Fresh 726 ↦ Fresh 820
      , "eFst" ∋ Fresh 727 ↦ Fresh 888
      , "eSnd" ∋ Fresh 727 ↦ Fresh 823
      , "eFst" ∋ Fresh 728 ↦ Fresh 889
      , "eSnd" ∋ Fresh 728 ↦ Fresh 890
      , "eFst" ∋ Fresh 729 ↦ Fresh 891
      , "eSnd" ∋ Fresh 729 ↦ Fresh 804
      , "eFst" ∋ Fresh 730 ↦ Fresh 892
      , "eSnd" ∋ Fresh 730 ↦ Fresh 805
      , "eFst" ∋ Fresh 731 ↦ Fresh 812
      , "eSnd" ∋ Fresh 731 ↦ Fresh 893
      , "eFst" ∋ Fresh 732 ↦ Fresh 775
      , "eSnd" ∋ Fresh 732 ↦ Fresh 894
      , "eFst" ∋ Fresh 733 ↦ Fresh 760
      , "eSnd" ∋ Fresh 733 ↦ Fresh 895
      , "eFst" ∋ Fresh 734 ↦ Fresh 738
      , "eSnd" ∋ Fresh 734 ↦ Fresh 896
      , "eFst" ∋ Fresh 735 ↦ Fresh 808
      , "eSnd" ∋ Fresh 735 ↦ Fresh 897
      , "rule" ∋ Fresh 736 ↦ Fresh 737
      , "eFst" ∋ Fresh 737 ↦ Fresh 738
      , "eSnd" ∋ Fresh 737 ↦ Fresh 739
      , "pre" ∋ Fresh 738 ↦ "mapsTo"
      , "compose" ∋ Fresh 739 ↦ Fresh 740
      , "eFst" ∋ Fresh 740 ↦ Fresh 741
      , "eSnd" ∋ Fresh 740 ↦ Fresh 742
      , "post" ∋ Fresh 741 ↦ "conjunct"
      , "compose" ∋ Fresh 742 ↦ Fresh 743
      , "eFst" ∋ Fresh 743 ↦ Fresh 744
      , "eSnd" ∋ Fresh 743 ↦ Fresh 745
      , "post" ∋ Fresh 744 ↦ "eFst"
      , "compose" ∋ Fresh 745 ↦ Fresh 746
      , "eFst" ∋ Fresh 746 ↦ Fresh 747
      , "eSnd" ∋ Fresh 746 ↦ Fresh 748
      , "post" ∋ Fresh 747 ↦ "compose"
      , "conjunct" ∋ Fresh 748 ↦ Fresh 749
      , "eFst" ∋ Fresh 749 ↦ Fresh 744
      , "eSnd" ∋ Fresh 749 ↦ Fresh 750
      , "compose" ∋ Fresh 750 ↦ Fresh 751
      , "eFst" ∋ Fresh 751 ↦ Fresh 752
      , "eSnd" ∋ Fresh 751 ↦ Fresh 755
      , "compose" ∋ Fresh 752 ↦ Fresh 753
      , "eFst" ∋ Fresh 753 ↦ Fresh 754
      , "eSnd" ∋ Fresh 753 ↦ Fresh 747
      , "post" ∋ Fresh 754 ↦ "eSnd"
      , "compose" ∋ Fresh 755 ↦ Fresh 756
      , "eFst" ∋ Fresh 756 ↦ Fresh 754
      , "eSnd" ∋ Fresh 756 ↦ Fresh 757
      , "post" ∋ Fresh 757 ↦ "converse"
      , "rule" ∋ Fresh 758 ↦ Fresh 759
      , "eFst" ∋ Fresh 759 ↦ Fresh 760
      , "eSnd" ∋ Fresh 759 ↦ Fresh 761
      , "pre" ∋ Fresh 760 ↦ "toPair"
      , "compose" ∋ Fresh 761 ↦ Fresh 762
      , "eFst" ∋ Fresh 762 ↦ Fresh 741
      , "eSnd" ∋ Fresh 762 ↦ Fresh 763
      , "conjunct" ∋ Fresh 763 ↦ Fresh 764
      , "eFst" ∋ Fresh 764 ↦ Fresh 765
      , "eSnd" ∋ Fresh 764 ↦ Fresh 754
      , "compose" ∋ Fresh 765 ↦ Fresh 766
      , "eFst" ∋ Fresh 766 ↦ Fresh 744
      , "eSnd" ∋ Fresh 766 ↦ Fresh 767
      , "compose" ∋ Fresh 767 ↦ Fresh 768
      , "eFst" ∋ Fresh 768 ↦ Fresh 769
      , "eSnd" ∋ Fresh 768 ↦ Fresh 775
      , "compose" ∋ Fresh 769 ↦ Fresh 770
      , "eFst" ∋ Fresh 770 ↦ Fresh 771
      , "eSnd" ∋ Fresh 770 ↦ Fresh 744
      , "compose" ∋ Fresh 771 ↦ Fresh 772
      , "eFst" ∋ Fresh 772 ↦ Fresh 773
      , "eSnd" ∋ Fresh 772 ↦ Fresh 747
      , "compose" ∋ Fresh 773 ↦ Fresh 774
      , "eFst" ∋ Fresh 774 ↦ Fresh 747
      , "eSnd" ∋ Fresh 774 ↦ Fresh 754
      , "pre" ∋ Fresh 775 ↦ "pair"
      , "rule" ∋ Fresh 776 ↦ Fresh 777
      , "eFst" ∋ Fresh 777 ↦ Fresh 778
      , "eSnd" ∋ Fresh 777 ↦ Fresh 781
      , "compose" ∋ Fresh 778 ↦ Fresh 779
      , "eFst" ∋ Fresh 779 ↦ Fresh 780
      , "eSnd" ∋ Fresh 779 ↦ Fresh 747
      , "converse" ∋ Fresh 780 ↦ Fresh 747
      , "rule" ∋ Fresh 782 ↦ Fresh 783
      , "eFst" ∋ Fresh 783 ↦ Fresh 784
      , "eSnd" ∋ Fresh 783 ↦ Fresh 787
      , "compose" ∋ Fresh 784 ↦ Fresh 785
      , "eFst" ∋ Fresh 785 ↦ Fresh 786
      , "eSnd" ∋ Fresh 785 ↦ Fresh 741
      , "converse" ∋ Fresh 786 ↦ Fresh 741
      , "rule" ∋ Fresh 788 ↦ Fresh 789
      , "eFst" ∋ Fresh 789 ↦ Fresh 790
      , "eSnd" ∋ Fresh 789 ↦ Fresh 793
      , "compose" ∋ Fresh 790 ↦ Fresh 791
      , "eFst" ∋ Fresh 791 ↦ Fresh 792
      , "eSnd" ∋ Fresh 791 ↦ Fresh 744
      , "converse" ∋ Fresh 792 ↦ Fresh 744
      , "rule" ∋ Fresh 794 ↦ Fresh 795
      , "eFst" ∋ Fresh 795 ↦ Fresh 796
      , "eSnd" ∋ Fresh 795 ↦ Fresh 799
      , "compose" ∋ Fresh 796 ↦ Fresh 797
      , "eFst" ∋ Fresh 797 ↦ Fresh 798
      , "eSnd" ∋ Fresh 797 ↦ Fresh 754
      , "converse" ∋ Fresh 798 ↦ Fresh 754
      , "rule" ∋ Fresh 800 ↦ Fresh 801
      , "eFst" ∋ Fresh 801 ↦ Fresh 775
      , "eSnd" ∋ Fresh 801 ↦ Fresh 802
      , "conjunct" ∋ Fresh 802 ↦ Fresh 803
      , "eFst" ∋ Fresh 803 ↦ Fresh 804
      , "eSnd" ∋ Fresh 803 ↦ Fresh 805
      , "post" ∋ Fresh 804 ↦ "pair1"
      , "post" ∋ Fresh 805 ↦ "pair2"
      , "rule" ∋ Fresh 806 ↦ Fresh 807
      , "eFst" ∋ Fresh 807 ↦ Fresh 808
      , "eSnd" ∋ Fresh 807 ↦ Fresh 809
      , "pre" ∋ Fresh 808 ↦ "relaxSnd"
      , "pre" ∋ Fresh 809 ↦ "eSnd"
      , "rule" ∋ Fresh 810 ↦ Fresh 811
      , "eFst" ∋ Fresh 811 ↦ Fresh 812
      , "eSnd" ∋ Fresh 811 ↦ Fresh 813
      , "pre" ∋ Fresh 812 ↦ "keep"
      , "compose" ∋ Fresh 813 ↦ Fresh 814
      , "eFst" ∋ Fresh 814 ↦ Fresh 815
      , "eSnd" ∋ Fresh 814 ↦ Fresh 816
      , "post" ∋ Fresh 815 ↦ "rule"
      , "conjunct" ∋ Fresh 816 ↦ Fresh 817
      , "eFst" ∋ Fresh 817 ↦ Fresh 818
      , "eSnd" ∋ Fresh 817 ↦ Fresh 821
      , "compose" ∋ Fresh 818 ↦ Fresh 819
      , "eFst" ∋ Fresh 819 ↦ Fresh 744
      , "eSnd" ∋ Fresh 819 ↦ Fresh 820
      , "post" ∋ Fresh 820 ↦ "pre"
      , "compose" ∋ Fresh 821 ↦ Fresh 822
      , "eFst" ∋ Fresh 822 ↦ Fresh 754
      , "eSnd" ∋ Fresh 822 ↦ Fresh 823
      , "post" ∋ Fresh 823 ↦ "post"
      , "continuation" ∋ Fresh 824 ↦ Fresh 825
      , "recogniser" ∋ Fresh 824 ↦ "\"RULE\""
      , "recogniser" ∋ Fresh 825 ↦ "rule"
      , "continuation" ∋ Fresh 826 ↦ Fresh 827
      , "recogniser" ∋ Fresh 826 ↦ "eFst"
      , "continuation" ∋ Fresh 827 ↦ Fresh 828
      , "recogniser" ∋ Fresh 827 ↦ "\"|-\""
      , "recogniser" ∋ Fresh 828 ↦ "relaxSnd"
      , "continuation" ∋ Fresh 829 ↦ Fresh 830
      , "recogniser" ∋ Fresh 829 ↦ "\"(\""
      , "continuation" ∋ Fresh 830 ↦ Fresh 831
      , "recogniser" ∋ Fresh 830 ↦ "I"
      , "recogniser" ∋ Fresh 831 ↦ "\")\""
      , "recogniser" ∋ Fresh 832 ↦ "conjunct"
      , "recogniser" ∋ Fresh 833 ↦ "compose"
      , "continuation" ∋ Fresh 834 ↦ Fresh 835
      , "recogniser" ∋ Fresh 834 ↦ "converse"
      , "recogniser" ∋ Fresh 835 ↦ "\"~\""
      , "continuation" ∋ Fresh 836 ↦ Fresh 837
      , "recogniser" ∋ Fresh 836 ↦ "\"pre\""
      , "recogniser" ∋ Fresh 837 ↦ "pre"
      , "continuation" ∋ Fresh 838 ↦ Fresh 839
      , "recogniser" ∋ Fresh 838 ↦ "\"post\""
      , "recogniser" ∋ Fresh 839 ↦ "post"
      , "continuation" ∋ Fresh 840 ↦ Fresh 841
      , "recogniser" ∋ Fresh 840 ↦ "\"during\""
      , "recogniser" ∋ Fresh 841 ↦ "during"
      , "continuation" ∋ Fresh 842 ↦ Fresh 843
      , "recogniser" ∋ Fresh 842 ↦ "\"[\""
      , "continuation" ∋ Fresh 843 ↦ Fresh 844
      , "recogniser" ∋ Fresh 843 ↦ "mapsTo"
      , "continuation" ∋ Fresh 844 ↦ Fresh 845
      , "recogniser" ∋ Fresh 844 ↦ "\"->\""
      , "continuation" ∋ Fresh 845 ↦ Fresh 846
      , "recogniser" ∋ Fresh 845 ↦ "toPair"
      , "recogniser" ∋ Fresh 846 ↦ "\"]\""
      , "continuation" ∋ Fresh 847 ↦ Fresh 848
      , "recogniser" ∋ Fresh 847 ↦ "\"<\""
      , "continuation" ∋ Fresh 848 ↦ Fresh 849
      , "recogniser" ∋ Fresh 848 ↦ "pair1"
      , "continuation" ∋ Fresh 849 ↦ Fresh 850
      , "recogniser" ∋ Fresh 849 ↦ "\",\""
      , "continuation" ∋ Fresh 850 ↦ Fresh 851
      , "recogniser" ∋ Fresh 850 ↦ "pair2"
      , "recogniser" ∋ Fresh 851 ↦ "\">\""
      , "continuation" ∋ Fresh 852 ↦ Fresh 853
      , "recogniser" ∋ Fresh 852 ↦ "\"<\""
      , "continuation" ∋ Fresh 853 ↦ Fresh 854
      , "recogniser" ∋ Fresh 853 ↦ "pair"
      , "recogniser" ∋ Fresh 854 ↦ "\">\""
      , "recogniser" ∋ Fresh 855 ↦ "\"I\""
      , "continuation" ∋ Fresh 856 ↦ Fresh 857
      , "recogniser" ∋ Fresh 856 ↦ "eFst"
      , "continuation" ∋ Fresh 857 ↦ Fresh 858
      , "recogniser" ∋ Fresh 857 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 858 ↦ "eSnd"
      , "continuation" ∋ Fresh 859 ↦ Fresh 860
      , "recogniser" ∋ Fresh 859 ↦ "eFst"
      , "continuation" ∋ Fresh 860 ↦ Fresh 861
      , "recogniser" ∋ Fresh 860 ↦ "\";\""
      , "recogniser" ∋ Fresh 861 ↦ "eSnd"
      , "continuation" ∋ Fresh 862 ↦ Fresh 863
      , "recogniser" ∋ Fresh 862 ↦ "\"KEEP\""
      , "recogniser" ∋ Fresh 863 ↦ "keep"
      , "post" ∋ Fresh 864 ↦ "origin"
      , "pre" ∋ Fresh 865 ↦ "origin"
      , "post" ∋ Fresh 866 ↦ "string"
      , "pre" ∋ Fresh 867 ↦ "string"
      , "pre" ∋ Fresh 868 ↦ "start"
      , "post" ∋ Fresh 869 ↦ "start"
      , "pre" ∋ Fresh 870 ↦ "more"
      , "post" ∋ Fresh 871 ↦ "more"
      , "pre" ∋ Fresh 872 ↦ "choice"
      , "post" ∋ Fresh 873 ↦ "choice"
      , "pre" ∋ Fresh 874 ↦ "continuation"
      , "post" ∋ Fresh 875 ↦ "continuation"
      , "pre" ∋ Fresh 876 ↦ "recogniser"
      , "post" ∋ Fresh 877 ↦ "recogniser"
      , "post" ∋ Fresh 878 ↦ "nonTerminal"
      , "post" ∋ Fresh 879 ↦ "UnquotedString"
      , "post" ∋ Fresh 880 ↦ "QuotedString"
      , "post" ∋ Fresh 881 ↦ "I"
      , "pre" ∋ Fresh 882 ↦ "rule"
      , "pre" ∋ Fresh 883 ↦ "eFst"
      , "pre" ∋ Fresh 884 ↦ "conjunct"
      , "pre" ∋ Fresh 885 ↦ "converse"
      , "pre" ∋ Fresh 886 ↦ "compose"
      , "pre" ∋ Fresh 887 ↦ "pre"
      , "pre" ∋ Fresh 888 ↦ "post"
      , "pre" ∋ Fresh 889 ↦ "during"
      , "post" ∋ Fresh 890 ↦ "during"
      , "pre" ∋ Fresh 891 ↦ "pair1"
      , "pre" ∋ Fresh 892 ↦ "pair2"
      , "post" ∋ Fresh 893 ↦ "keep"
      , "post" ∋ Fresh 894 ↦ "pair"
      , "post" ∋ Fresh 895 ↦ "toPair"
      , "post" ∋ Fresh 896 ↦ "mapsTo"
      , "post" ∋ Fresh 897 ↦ "relaxSnd"
      ])
  , ( "parser"
    , [ "choice" ∋ "Classification" ↦ Fresh 1314
      , "choice" ∋ "ClassificationStatement" ↦ Fresh 1311
      , "choice" ∋ "Compose" ↦ Fresh 1384
      , "choice" ∋ "ConceptList" ↦ Fresh 1318
      , "choice" ∋ "ConceptList" ↦ Fresh 1321
      , "choice" ∋ "Conjunct" ↦ Fresh 1381
      , "choice" ∋ "ConsConceptList" ↦ Fresh 1318
      , "choice" ∋ "ConsSyntaxList" ↦ Fresh 1339
      , "choice" ∋ "Declaration" ↦ Fresh 1325
      , "choice" ∋ "DeclarationStatement" ↦ Fresh 1312
      , "choice" ∋ "DeclarationType" ↦ Fresh 1322
      , "choice" ∋ "EmptySyntax" ↦ Fresh 1334
      , "choice" ∋ "Expression" ↦ Fresh 1361
      , "choice" ∋ "Expression" ↦ Fresh 1364
      , "choice" ∋ "Expression" ↦ Fresh 1367
      , "choice" ∋ "Expression" ↦ Fresh 1369
      , "choice" ∋ "Expression" ↦ Fresh 1371
      , "choice" ∋ "Expression" ↦ Fresh 1373
      , "choice" ∋ "Expression" ↦ Fresh 1375
      , "choice" ∋ "Expression" ↦ Fresh 1380
      , "continuation" ∋ "NextStatement" ↦ "gotoStart"
      , "recogniser" ∋ "NextStatement" ↦ "Statement"
      , "choice" ∋ "QuotedStringElement" ↦ Fresh 1343
      , "choice" ∋ "RelationElement" ↦ Fresh 1344
      , "choice" ∋ "RuleStatement" ↦ Fresh 1356
      , "choice" ∋ "RuleSubset" ↦ Fresh 1358
      , "choice" ∋ "Start" ↦ "NextStatement"
      , "choice" ∋ "Start" ↦ "endOfFile"
      , "nonTerminal" ∋ "Start" ↦ "Start"
      , "choice" ∋ "Statement" ↦ Fresh 1311
      , "choice" ∋ "Statement" ↦ Fresh 1312
      , "choice" ∋ "Statement" ↦ Fresh 1313
      , "choice" ∋ "Statement" ↦ Fresh 1356
      , "nonTerminal" ∋ "Statement" ↦ "Statement"
      , "choice" ∋ "Syntax" ↦ Fresh 1328
      , "choice" ∋ "Syntax" ↦ Fresh 1334
      , "choice" ∋ "SyntaxElement" ↦ Fresh 1343
      , "choice" ∋ "SyntaxElement" ↦ Fresh 1344
      , "choice" ∋ "SyntaxList" ↦ Fresh 1339
      , "choice" ∋ "SyntaxList" ↦ Fresh 1342
      , "choice" ∋ "SyntaxStatement" ↦ Fresh 1313
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 1358
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 1381
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 1384
      , "nonTerminal" ∋ "classification" ↦ "Classification"
      , "rule" ∋ "classification" ↦ Fresh 1294
      , "nonTerminal" ∋ "compose" ↦ "Compose"
      , "rule" ∋ "compose" ↦ Fresh 1350
      , "nonTerminal" ∋ "concept" ↦ "String"
      , "rule" ∋ "concept" ↦ Fresh 1305
      , "nonTerminal" ∋ "conceptList" ↦ "ConceptList"
      , "rule" ∋ "conceptList" ↦ Fresh 1296
      , "nonTerminal" ∋ "concepts" ↦ "DeclarationType"
      , "rule" ∋ "concepts" ↦ Fresh 1301
      , "nonTerminal" ∋ "conjunct" ↦ "Conjunct"
      , "rule" ∋ "conjunct" ↦ Fresh 1348
      , "nonTerminal" ∋ "converse" ↦ "Expression"
      , "rule" ∋ "converse" ↦ Fresh 1349
      , "nonTerminal" ∋ "declaration" ↦ "Declaration"
      , "rule" ∋ "declaration" ↦ Fresh 1299
      , "nonTerminal" ∋ "during" ↦ "UnquotedString"
      , "rule" ∋ "during" ↦ Fresh 1353
      , "nonTerminal" ∋ "eFst" ↦ "Expression"
      , "rule" ∋ "eFst" ↦ Fresh 1346
      , "nonTerminal" ∋ "eSnd" ↦ "Expression"
      , "rule" ∋ "eSnd" ↦ Fresh 1347
      , "nonTerminal" ∋ "fst" ↦ "String"
      , "rule" ∋ "fst" ↦ Fresh 1302
      , "recogniser" ∋ "gotoStart" ↦ "Start"
      , "nonTerminal" ∋ "head1" ↦ "String"
      , "rule" ∋ "head1" ↦ Fresh 1297
      , "nonTerminal" ∋ "head2" ↦ "SyntaxElement"
      , "rule" ∋ "head2" ↦ Fresh 1308
      , "eFst" ∋ "keepOrigin" ↦ Fresh 1388
      , "eSnd" ∋ "keepOrigin" ↦ Fresh 1387
      , "rule" ∋ "keepOrigin" ↦ "keepOrigin"
      , "eFst" ∋ "keepString" ↦ Fresh 1390
      , "eSnd" ∋ "keepString" ↦ Fresh 1389
      , "rule" ∋ "keepString" ↦ "keepString"
      , "nonTerminal" ∋ "mainConcept" ↦ "String"
      , "rule" ∋ "mainConcept" ↦ Fresh 1295
      , "nonTerminal" ∋ "pair1" ↦ "String"
      , "rule" ∋ "pair1" ↦ Fresh 1354
      , "nonTerminal" ∋ "pair2" ↦ "String"
      , "rule" ∋ "pair2" ↦ Fresh 1355
      , "nonTerminal" ∋ "post" ↦ "UnquotedString"
      , "rule" ∋ "post" ↦ Fresh 1352
      , "nonTerminal" ∋ "pre" ↦ "UnquotedString"
      , "rule" ∋ "pre" ↦ Fresh 1351
      , "nonTerminal" ∋ "qstring" ↦ "QuotedString"
      , "rule" ∋ "qstring" ↦ Fresh 1310
      , "nonTerminal" ∋ "relation" ↦ "StringAndOrigin"
      , "rule" ∋ "relation" ↦ Fresh 1300
      , "nonTerminal" ∋ "relationName" ↦ "UnquotedString"
      , "rule" ∋ "relationName" ↦ Fresh 1306
      , "nonTerminal" ∋ "rule" ↦ "RuleSubset"
      , "rule" ∋ "rule" ↦ Fresh 1345
      , "nonTerminal" ∋ "snd" ↦ "String"
      , "rule" ∋ "snd" ↦ Fresh 1303
      , "nonTerminal" ∋ "syntax" ↦ "Syntax"
      , "rule" ∋ "syntax" ↦ Fresh 1304
      , "nonTerminal" ∋ "syntaxList" ↦ "SyntaxList"
      , "rule" ∋ "syntaxList" ↦ Fresh 1307
      , "nonTerminal" ∋ "tail1" ↦ "ConceptList"
      , "rule" ∋ "tail1" ↦ Fresh 1298
      , "nonTerminal" ∋ "tail2" ↦ "SyntaxList"
      , "rule" ∋ "tail2" ↦ Fresh 1309
      , "eFst" ∋ Fresh 1294 ↦ Fresh 1391
      , "eSnd" ∋ Fresh 1294 ↦ Fresh 1392
      , "eFst" ∋ Fresh 1295 ↦ Fresh 1393
      , "eSnd" ∋ Fresh 1295 ↦ Fresh 1394
      , "eFst" ∋ Fresh 1296 ↦ Fresh 1395
      , "eSnd" ∋ Fresh 1296 ↦ Fresh 1396
      , "eFst" ∋ Fresh 1297 ↦ Fresh 1397
      , "eSnd" ∋ Fresh 1297 ↦ Fresh 1398
      , "eFst" ∋ Fresh 1298 ↦ Fresh 1399
      , "eSnd" ∋ Fresh 1298 ↦ Fresh 1400
      , "eFst" ∋ Fresh 1299 ↦ Fresh 1401
      , "eSnd" ∋ Fresh 1299 ↦ Fresh 1402
      , "eFst" ∋ Fresh 1300 ↦ Fresh 1403
      , "eSnd" ∋ Fresh 1300 ↦ Fresh 1404
      , "eFst" ∋ Fresh 1301 ↦ Fresh 1405
      , "eSnd" ∋ Fresh 1301 ↦ Fresh 1406
      , "eFst" ∋ Fresh 1302 ↦ Fresh 1407
      , "eSnd" ∋ Fresh 1302 ↦ Fresh 1408
      , "eFst" ∋ Fresh 1303 ↦ Fresh 1409
      , "eSnd" ∋ Fresh 1303 ↦ Fresh 1410
      , "eFst" ∋ Fresh 1304 ↦ Fresh 1411
      , "eSnd" ∋ Fresh 1304 ↦ Fresh 1412
      , "eFst" ∋ Fresh 1305 ↦ Fresh 1413
      , "eSnd" ∋ Fresh 1305 ↦ Fresh 1414
      , "eFst" ∋ Fresh 1306 ↦ Fresh 1415
      , "eSnd" ∋ Fresh 1306 ↦ Fresh 1416
      , "eFst" ∋ Fresh 1307 ↦ Fresh 1417
      , "eSnd" ∋ Fresh 1307 ↦ Fresh 1418
      , "eFst" ∋ Fresh 1308 ↦ Fresh 1419
      , "eSnd" ∋ Fresh 1308 ↦ Fresh 1420
      , "eFst" ∋ Fresh 1309 ↦ Fresh 1421
      , "eSnd" ∋ Fresh 1309 ↦ Fresh 1422
      , "eFst" ∋ Fresh 1310 ↦ Fresh 1423
      , "eSnd" ∋ Fresh 1310 ↦ Fresh 1424
      , "recogniser" ∋ Fresh 1311 ↦ "classification"
      , "recogniser" ∋ Fresh 1312 ↦ "declaration"
      , "recogniser" ∋ Fresh 1313 ↦ "syntax"
      , "continuation" ∋ Fresh 1314 ↦ Fresh 1315
      , "recogniser" ∋ Fresh 1314 ↦ "\"CLASSIFY\""
      , "continuation" ∋ Fresh 1315 ↦ Fresh 1316
      , "recogniser" ∋ Fresh 1315 ↦ "mainConcept"
      , "continuation" ∋ Fresh 1316 ↦ Fresh 1317
      , "recogniser" ∋ Fresh 1316 ↦ "\"IS\""
      , "recogniser" ∋ Fresh 1317 ↦ "conceptList"
      , "continuation" ∋ Fresh 1318 ↦ Fresh 1319
      , "recogniser" ∋ Fresh 1318 ↦ "head1"
      , "continuation" ∋ Fresh 1319 ↦ Fresh 1320
      , "recogniser" ∋ Fresh 1319 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 1320 ↦ "tail1"
      , "recogniser" ∋ Fresh 1321 ↦ "head1"
      , "continuation" ∋ Fresh 1322 ↦ Fresh 1323
      , "recogniser" ∋ Fresh 1322 ↦ "fst"
      , "continuation" ∋ Fresh 1323 ↦ Fresh 1324
      , "recogniser" ∋ Fresh 1323 ↦ "\"*\""
      , "recogniser" ∋ Fresh 1324 ↦ "snd"
      , "continuation" ∋ Fresh 1325 ↦ Fresh 1326
      , "recogniser" ∋ Fresh 1325 ↦ "relation"
      , "continuation" ∋ Fresh 1326 ↦ Fresh 1327
      , "recogniser" ∋ Fresh 1326 ↦ "\"::\""
      , "recogniser" ∋ Fresh 1327 ↦ "concepts"
      , "continuation" ∋ Fresh 1328 ↦ Fresh 1329
      , "recogniser" ∋ Fresh 1328 ↦ "\"VIEW\""
      , "continuation" ∋ Fresh 1329 ↦ Fresh 1330
      , "recogniser" ∋ Fresh 1329 ↦ "concept"
      , "continuation" ∋ Fresh 1330 ↦ Fresh 1331
      , "recogniser" ∋ Fresh 1330 ↦ "\"=\""
      , "continuation" ∋ Fresh 1331 ↦ Fresh 1332
      , "recogniser" ∋ Fresh 1331 ↦ "\"[\""
      , "continuation" ∋ Fresh 1332 ↦ Fresh 1333
      , "recogniser" ∋ Fresh 1332 ↦ "syntaxList"
      , "recogniser" ∋ Fresh 1333 ↦ "\"]\""
      , "continuation" ∋ Fresh 1334 ↦ Fresh 1335
      , "recogniser" ∋ Fresh 1334 ↦ "\"VIEW\""
      , "continuation" ∋ Fresh 1335 ↦ Fresh 1336
      , "recogniser" ∋ Fresh 1335 ↦ "concept"
      , "continuation" ∋ Fresh 1336 ↦ Fresh 1337
      , "recogniser" ∋ Fresh 1336 ↦ "\"=\""
      , "continuation" ∋ Fresh 1337 ↦ Fresh 1338
      , "recogniser" ∋ Fresh 1337 ↦ "\"[\""
      , "recogniser" ∋ Fresh 1338 ↦ "\"]\""
      , "continuation" ∋ Fresh 1339 ↦ Fresh 1340
      , "recogniser" ∋ Fresh 1339 ↦ "head2"
      , "continuation" ∋ Fresh 1340 ↦ Fresh 1341
      , "recogniser" ∋ Fresh 1340 ↦ "\",\""
      , "recogniser" ∋ Fresh 1341 ↦ "tail2"
      , "recogniser" ∋ Fresh 1342 ↦ "head2"
      , "recogniser" ∋ Fresh 1343 ↦ "qstring"
      , "recogniser" ∋ Fresh 1344 ↦ "relationName"
      , "eFst" ∋ Fresh 1345 ↦ Fresh 1425
      , "eSnd" ∋ Fresh 1345 ↦ Fresh 1426
      , "eFst" ∋ Fresh 1346 ↦ Fresh 1427
      , "eSnd" ∋ Fresh 1346 ↦ Fresh 1428
      , "eFst" ∋ Fresh 1347 ↦ Fresh 1429
      , "eSnd" ∋ Fresh 1347 ↦ Fresh 1430
      , "eFst" ∋ Fresh 1348 ↦ Fresh 1431
      , "eSnd" ∋ Fresh 1348 ↦ Fresh 1432
      , "eFst" ∋ Fresh 1349 ↦ Fresh 1433
      , "eSnd" ∋ Fresh 1349 ↦ Fresh 1434
      , "eFst" ∋ Fresh 1350 ↦ Fresh 1435
      , "eSnd" ∋ Fresh 1350 ↦ Fresh 1436
      , "eFst" ∋ Fresh 1351 ↦ Fresh 1437
      , "eSnd" ∋ Fresh 1351 ↦ Fresh 1438
      , "eFst" ∋ Fresh 1352 ↦ Fresh 1439
      , "eSnd" ∋ Fresh 1352 ↦ Fresh 1440
      , "eFst" ∋ Fresh 1353 ↦ Fresh 1441
      , "eSnd" ∋ Fresh 1353 ↦ Fresh 1442
      , "eFst" ∋ Fresh 1354 ↦ Fresh 1443
      , "eSnd" ∋ Fresh 1354 ↦ Fresh 1444
      , "eFst" ∋ Fresh 1355 ↦ Fresh 1445
      , "eSnd" ∋ Fresh 1355 ↦ Fresh 1446
      , "continuation" ∋ Fresh 1356 ↦ Fresh 1357
      , "recogniser" ∋ Fresh 1356 ↦ "\"RULE\""
      , "recogniser" ∋ Fresh 1357 ↦ "rule"
      , "continuation" ∋ Fresh 1358 ↦ Fresh 1359
      , "recogniser" ∋ Fresh 1358 ↦ "eFst"
      , "continuation" ∋ Fresh 1359 ↦ Fresh 1360
      , "recogniser" ∋ Fresh 1359 ↦ "\"|-\""
      , "recogniser" ∋ Fresh 1360 ↦ "eSnd"
      , "continuation" ∋ Fresh 1361 ↦ Fresh 1362
      , "recogniser" ∋ Fresh 1361 ↦ "\"(\""
      , "continuation" ∋ Fresh 1362 ↦ Fresh 1363
      , "recogniser" ∋ Fresh 1362 ↦ "conjunct"
      , "recogniser" ∋ Fresh 1363 ↦ "\")\""
      , "continuation" ∋ Fresh 1364 ↦ Fresh 1365
      , "recogniser" ∋ Fresh 1364 ↦ "\"(\""
      , "continuation" ∋ Fresh 1365 ↦ Fresh 1366
      , "recogniser" ∋ Fresh 1365 ↦ "compose"
      , "recogniser" ∋ Fresh 1366 ↦ "\")\""
      , "continuation" ∋ Fresh 1367 ↦ Fresh 1368
      , "recogniser" ∋ Fresh 1367 ↦ "converse"
      , "recogniser" ∋ Fresh 1368 ↦ "\"~\""
      , "continuation" ∋ Fresh 1369 ↦ Fresh 1370
      , "recogniser" ∋ Fresh 1369 ↦ "\"pre\""
      , "recogniser" ∋ Fresh 1370 ↦ "pre"
      , "continuation" ∋ Fresh 1371 ↦ Fresh 1372
      , "recogniser" ∋ Fresh 1371 ↦ "\"post\""
      , "recogniser" ∋ Fresh 1372 ↦ "post"
      , "continuation" ∋ Fresh 1373 ↦ Fresh 1374
      , "recogniser" ∋ Fresh 1373 ↦ "\"during\""
      , "recogniser" ∋ Fresh 1374 ↦ "during"
      , "continuation" ∋ Fresh 1375 ↦ Fresh 1376
      , "recogniser" ∋ Fresh 1375 ↦ "\"<\""
      , "continuation" ∋ Fresh 1376 ↦ Fresh 1377
      , "recogniser" ∋ Fresh 1376 ↦ "pair1"
      , "continuation" ∋ Fresh 1377 ↦ Fresh 1378
      , "recogniser" ∋ Fresh 1377 ↦ "\",\""
      , "continuation" ∋ Fresh 1378 ↦ Fresh 1379
      , "recogniser" ∋ Fresh 1378 ↦ "pair2"
      , "recogniser" ∋ Fresh 1379 ↦ "\">\""
      , "recogniser" ∋ Fresh 1380 ↦ "\"I\""
      , "continuation" ∋ Fresh 1381 ↦ Fresh 1382
      , "recogniser" ∋ Fresh 1381 ↦ "eFst"
      , "continuation" ∋ Fresh 1382 ↦ Fresh 1383
      , "recogniser" ∋ Fresh 1382 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 1383 ↦ "eSnd"
      , "continuation" ∋ Fresh 1384 ↦ Fresh 1385
      , "recogniser" ∋ Fresh 1384 ↦ "eFst"
      , "continuation" ∋ Fresh 1385 ↦ Fresh 1386
      , "recogniser" ∋ Fresh 1385 ↦ "\";\""
      , "recogniser" ∋ Fresh 1386 ↦ "eSnd"
      , "post" ∋ Fresh 1387 ↦ "origin"
      , "pre" ∋ Fresh 1388 ↦ "origin"
      , "post" ∋ Fresh 1389 ↦ "string"
      , "pre" ∋ Fresh 1390 ↦ "string"
      , "pre" ∋ Fresh 1391 ↦ "classification"
      , "post" ∋ Fresh 1392 ↦ "classification"
      , "pre" ∋ Fresh 1393 ↦ "mainConcept"
      , "post" ∋ Fresh 1394 ↦ "mainConcept"
      , "pre" ∋ Fresh 1395 ↦ "conceptList"
      , "post" ∋ Fresh 1396 ↦ "conceptList"
      , "pre" ∋ Fresh 1397 ↦ "head1"
      , "post" ∋ Fresh 1398 ↦ "head1"
      , "pre" ∋ Fresh 1399 ↦ "tail1"
      , "post" ∋ Fresh 1400 ↦ "tail1"
      , "pre" ∋ Fresh 1401 ↦ "declaration"
      , "post" ∋ Fresh 1402 ↦ "declaration"
      , "pre" ∋ Fresh 1403 ↦ "relation"
      , "post" ∋ Fresh 1404 ↦ "relation"
      , "pre" ∋ Fresh 1405 ↦ "concepts"
      , "post" ∋ Fresh 1406 ↦ "concepts"
      , "pre" ∋ Fresh 1407 ↦ "fst"
      , "post" ∋ Fresh 1408 ↦ "fst"
      , "pre" ∋ Fresh 1409 ↦ "snd"
      , "post" ∋ Fresh 1410 ↦ "snd"
      , "pre" ∋ Fresh 1411 ↦ "syntax"
      , "post" ∋ Fresh 1412 ↦ "syntax"
      , "pre" ∋ Fresh 1413 ↦ "concept"
      , "post" ∋ Fresh 1414 ↦ "concept"
      , "pre" ∋ Fresh 1415 ↦ "relationName"
      , "post" ∋ Fresh 1416 ↦ "relationName"
      , "pre" ∋ Fresh 1417 ↦ "syntaxList"
      , "post" ∋ Fresh 1418 ↦ "syntaxList"
      , "pre" ∋ Fresh 1419 ↦ "head2"
      , "post" ∋ Fresh 1420 ↦ "head2"
      , "pre" ∋ Fresh 1421 ↦ "tail2"
      , "post" ∋ Fresh 1422 ↦ "tail2"
      , "pre" ∋ Fresh 1423 ↦ "qstring"
      , "post" ∋ Fresh 1424 ↦ "qstring"
      , "pre" ∋ Fresh 1425 ↦ "rule"
      , "post" ∋ Fresh 1426 ↦ "rule"
      , "pre" ∋ Fresh 1427 ↦ "eFst"
      , "post" ∋ Fresh 1428 ↦ "eFst"
      , "pre" ∋ Fresh 1429 ↦ "eSnd"
      , "post" ∋ Fresh 1430 ↦ "eSnd"
      , "pre" ∋ Fresh 1431 ↦ "conjunct"
      , "post" ∋ Fresh 1432 ↦ "conjunct"
      , "pre" ∋ Fresh 1433 ↦ "converse"
      , "post" ∋ Fresh 1434 ↦ "converse"
      , "pre" ∋ Fresh 1435 ↦ "compose"
      , "post" ∋ Fresh 1436 ↦ "compose"
      , "pre" ∋ Fresh 1437 ↦ "pre"
      , "post" ∋ Fresh 1438 ↦ "pre"
      , "pre" ∋ Fresh 1439 ↦ "post"
      , "post" ∋ Fresh 1440 ↦ "post"
      , "pre" ∋ Fresh 1441 ↦ "during"
      , "post" ∋ Fresh 1442 ↦ "during"
      , "pre" ∋ Fresh 1443 ↦ "pair1"
      , "post" ∋ Fresh 1444 ↦ "pair1"
      , "pre" ∋ Fresh 1445 ↦ "pair2"
      , "post" ∋ Fresh 1446 ↦ "pair2"
      ])
  , ( "switches"
    , [ "cur" ∋ Fresh 1774 ↦ Fresh 1774
      , "first" ∋ Fresh 1774 ↦ Fresh 1784
      , "next" ∋ Fresh 1774 ↦ Fresh 1775
      , "string" ∋ Fresh 1774 ↦ "\"i\""
      , "next" ∋ Fresh 1775 ↦ Fresh 1776
      , "string" ∋ Fresh 1775 ↦ "\"asParser\""
      , "first" ∋ Fresh 1776 ↦ Fresh 1785
      , "next" ∋ Fresh 1776 ↦ Fresh 1777
      , "string" ∋ Fresh 1776 ↦ "\"i\""
      , "first" ∋ Fresh 1777 ↦ Fresh 1786
      , "next" ∋ Fresh 1777 ↦ Fresh 1778
      , "string" ∋ Fresh 1777 ↦ "\"apply\""
      , "first" ∋ Fresh 1778 ↦ Fresh 1789
      , "next" ∋ Fresh 1778 ↦ Fresh 1779
      , "string" ∋ Fresh 1778 ↦ "\"i\""
      , "first" ∋ Fresh 1779 ↦ Fresh 1790
      , "next" ∋ Fresh 1779 ↦ Fresh 1780
      , "string" ∋ Fresh 1779 ↦ "\"apply\""
      , "first" ∋ Fresh 1780 ↦ Fresh 1793
      , "next" ∋ Fresh 1780 ↦ Fresh 1781
      , "string" ∋ Fresh 1780 ↦ "\"apply\""
      , "first" ∋ Fresh 1781 ↦ Fresh 1795
      , "next" ∋ Fresh 1781 ↦ Fresh 1782
      , "string" ∋ Fresh 1781 ↦ "\"apply\""
      , "first" ∋ Fresh 1782 ↦ Fresh 1797
      , "next" ∋ Fresh 1782 ↦ Fresh 1783
      , "string" ∋ Fresh 1782 ↦ "\"collect\""
      , "first" ∋ Fresh 1783 ↦ Fresh 1798
      , "string" ∋ Fresh 1783 ↦ "\"showTS\""
      , "string" ∋ Fresh 1784 ↦ "\"boot.ASL\""
      , "string" ∋ Fresh 1785 ↦ "\"asParser.ASL\""
      , "next" ∋ Fresh 1786 ↦ Fresh 1787
      , "string" ∋ Fresh 1786 ↦ "\"parser\""
      , "next" ∋ Fresh 1787 ↦ Fresh 1788
      , "string" ∋ Fresh 1787 ↦ "\"population\""
      , "string" ∋ Fresh 1788 ↦ "\"asParser\""
      , "string" ∋ Fresh 1789 ↦ "\"cfg.ASL\""
      , "next" ∋ Fresh 1790 ↦ Fresh 1791
      , "string" ∋ Fresh 1790 ↦ "\"asParser\""
      , "next" ∋ Fresh 1791 ↦ Fresh 1792
      , "string" ∋ Fresh 1791 ↦ "\"population\""
      , "string" ∋ Fresh 1792 ↦ "\"cfg\""
      , "next" ∋ Fresh 1793 ↦ Fresh 1794
      , "string" ∋ Fresh 1793 ↦ "\"del\""
      , "string" ∋ Fresh 1794 ↦ "\"switches\""
      , "next" ∋ Fresh 1795 ↦ Fresh 1796
      , "string" ∋ Fresh 1795 ↦ "\"del\""
      , "string" ∋ Fresh 1796 ↦ "\"population\""
      , "string" ∋ Fresh 1797 ↦ "\"state\""
      , "string" ∋ Fresh 1798 ↦ "\"state\""
      ])
  ];}
