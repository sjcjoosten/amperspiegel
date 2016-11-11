{-# OPTIONS_GHC -Wall -O0 #-} {-# LANGUAGE OverloadedStrings #-}
module BaseState (baseState) where{
import Helpers;import TokenAwareParser;
baseState :: [(Text,[Triple (Atom Text) (Atom Text)])];
baseState =
  [ ( "asParser"
    , [ "Start" ∋ Fresh 0 ↦ Fresh 5
      , "Statement" ∋ Fresh 0 ↦ Fresh 1
      , "rule" ∋ Fresh 1 ↦ Fresh 2
      , "eFst" ∋ Fresh 2 ↦ Fresh 3
      , "eSnd" ∋ Fresh 2 ↦ Fresh 4
      , "pre" ∋ Fresh 3 ↦ "conceptList"
      , "during" ∋ Fresh 4 ↦ "conceptLists"
      , "Start" ∋ Fresh 5 ↦ Fresh 13
      , "Statement" ∋ Fresh 5 ↦ Fresh 6
      , "rule" ∋ Fresh 6 ↦ Fresh 7
      , "eFst" ∋ Fresh 7 ↦ Fresh 8
      , "eSnd" ∋ Fresh 7 ↦ Fresh 12
      , "compose" ∋ Fresh 8 ↦ Fresh 9
      , "eFst" ∋ Fresh 9 ↦ Fresh 10
      , "eSnd" ∋ Fresh 9 ↦ Fresh 11
      , "during" ∋ Fresh 10 ↦ "conceptLists"
      , "pre" ∋ Fresh 11 ↦ "tail1"
      , "during" ∋ Fresh 12 ↦ "conceptLists"
      , "Start" ∋ Fresh 13 ↦ Fresh 25
      , "Statement" ∋ Fresh 13 ↦ Fresh 14
      , "rule" ∋ Fresh 14 ↦ Fresh 15
      , "eFst" ∋ Fresh 15 ↦ Fresh 16
      , "eSnd" ∋ Fresh 15 ↦ Fresh 24
      , "compose" ∋ Fresh 16 ↦ Fresh 17
      , "eFst" ∋ Fresh 17 ↦ Fresh 18
      , "eSnd" ∋ Fresh 17 ↦ Fresh 23
      , "compose" ∋ Fresh 18 ↦ Fresh 19
      , "eFst" ∋ Fresh 19 ↦ Fresh 20
      , "eSnd" ∋ Fresh 19 ↦ Fresh 22
      , "converse" ∋ Fresh 20 ↦ Fresh 21
      , "pre" ∋ Fresh 21 ↦ "mainConcept"
      , "during" ∋ Fresh 22 ↦ "conceptLists"
      , "pre" ∋ Fresh 23 ↦ "head1"
      , "during" ∋ Fresh 24 ↦ "subConcepts"
      , "Start" ∋ Fresh 25 ↦ Fresh 33
      , "Statement" ∋ Fresh 25 ↦ Fresh 26
      , "rule" ∋ Fresh 26 ↦ Fresh 27
      , "eFst" ∋ Fresh 27 ↦ Fresh 28
      , "eSnd" ∋ Fresh 27 ↦ Fresh 32
      , "compose" ∋ Fresh 28 ↦ Fresh 29
      , "eFst" ∋ Fresh 29 ↦ Fresh 30
      , "eSnd" ∋ Fresh 29 ↦ Fresh 31
      , "during" ∋ Fresh 30 ↦ "subConcepts"
      , "during" ∋ Fresh 31 ↦ "subConcepts"
      , "during" ∋ Fresh 32 ↦ "subConcepts"
      , "Start" ∋ Fresh 33 ↦ Fresh 45
      , "Statement" ∋ Fresh 33 ↦ Fresh 34
      , "rule" ∋ Fresh 34 ↦ Fresh 35
      , "eFst" ∋ Fresh 35 ↦ Fresh 36
      , "eSnd" ∋ Fresh 35 ↦ Fresh 44
      , "conjunct" ∋ Fresh 36 ↦ Fresh 37
      , "eFst" ∋ Fresh 37 ↦ Fresh 38
      , "eSnd" ∋ Fresh 37 ↦ Fresh 43
      , "compose" ∋ Fresh 38 ↦ Fresh 39
      , "eFst" ∋ Fresh 39 ↦ Fresh 40
      , "eSnd" ∋ Fresh 39 ↦ Fresh 42
      , "converse" ∋ Fresh 40 ↦ Fresh 41
      , "pre" ∋ Fresh 41 ↦ "mainConcept"
      , "pre" ∋ Fresh 42 ↦ "mainConcept"
      , "during" ∋ Fresh 44 ↦ "subConcepts"
      , "Start" ∋ Fresh 45 ↦ Fresh 57
      , "Statement" ∋ Fresh 45 ↦ Fresh 46
      , "rule" ∋ Fresh 46 ↦ Fresh 47
      , "eFst" ∋ Fresh 47 ↦ Fresh 48
      , "eSnd" ∋ Fresh 47 ↦ Fresh 56
      , "conjunct" ∋ Fresh 48 ↦ Fresh 49
      , "eFst" ∋ Fresh 49 ↦ Fresh 50
      , "eSnd" ∋ Fresh 49 ↦ Fresh 55
      , "compose" ∋ Fresh 50 ↦ Fresh 51
      , "eFst" ∋ Fresh 51 ↦ Fresh 52
      , "eSnd" ∋ Fresh 51 ↦ Fresh 54
      , "converse" ∋ Fresh 52 ↦ Fresh 53
      , "pre" ∋ Fresh 53 ↦ "concept"
      , "pre" ∋ Fresh 54 ↦ "concept"
      , "during" ∋ Fresh 56 ↦ "subConcepts"
      , "Start" ∋ Fresh 57 ↦ Fresh 62
      , "Statement" ∋ Fresh 57 ↦ Fresh 58
      , "rule" ∋ Fresh 58 ↦ Fresh 59
      , "eFst" ∋ Fresh 59 ↦ Fresh 60
      , "eSnd" ∋ Fresh 59 ↦ Fresh 61
      , "pre" ∋ Fresh 60 ↦ "qstring"
      , "Start" ∋ Fresh 62 ↦ Fresh 67
      , "Statement" ∋ Fresh 62 ↦ Fresh 63
      , "rule" ∋ Fresh 63 ↦ Fresh 64
      , "eFst" ∋ Fresh 64 ↦ Fresh 65
      , "eSnd" ∋ Fresh 64 ↦ Fresh 66
      , "pre" ∋ Fresh 65 ↦ "relationName"
      , "Start" ∋ Fresh 67 ↦ Fresh 76
      , "Statement" ∋ Fresh 67 ↦ Fresh 68
      , "rule" ∋ Fresh 68 ↦ Fresh 69
      , "eFst" ∋ Fresh 69 ↦ Fresh 70
      , "eSnd" ∋ Fresh 69 ↦ Fresh 75
      , "compose" ∋ Fresh 70 ↦ Fresh 71
      , "eFst" ∋ Fresh 71 ↦ Fresh 72
      , "eSnd" ∋ Fresh 71 ↦ Fresh 73
      , "pre" ∋ Fresh 72 ↦ "string"
      , "converse" ∋ Fresh 73 ↦ Fresh 74
      , "pre" ∋ Fresh 74 ↦ "string"
      , "Start" ∋ Fresh 76 ↦ Fresh 87
      , "Statement" ∋ Fresh 76 ↦ Fresh 77
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
      , "pre" ∋ Fresh 84 ↦ "relation"
      , "pre" ∋ Fresh 85 ↦ "string"
      , "pre" ∋ Fresh 86 ↦ "relationName"
      , "Start" ∋ Fresh 87 ↦ Fresh 98
      , "Statement" ∋ Fresh 87 ↦ Fresh 88
      , "rule" ∋ Fresh 88 ↦ Fresh 89
      , "eFst" ∋ Fresh 89 ↦ Fresh 90
      , "eSnd" ∋ Fresh 89 ↦ Fresh 97
      , "compose" ∋ Fresh 90 ↦ Fresh 91
      , "eFst" ∋ Fresh 91 ↦ Fresh 92
      , "eSnd" ∋ Fresh 91 ↦ Fresh 96
      , "compose" ∋ Fresh 92 ↦ Fresh 93
      , "eFst" ∋ Fresh 93 ↦ Fresh 94
      , "eSnd" ∋ Fresh 93 ↦ Fresh 95
      , "pre" ∋ Fresh 94 ↦ "declaration"
      , "pre" ∋ Fresh 95 ↦ "concepts"
      , "pre" ∋ Fresh 96 ↦ "snd"
      , "post" ∋ Fresh 97 ↦ "nonTerminal"
      , "Start" ∋ Fresh 98 ↦ Fresh 108
      , "Statement" ∋ Fresh 98 ↦ Fresh 99
      , "rule" ∋ Fresh 99 ↦ Fresh 100
      , "eFst" ∋ Fresh 100 ↦ Fresh 101
      , "eSnd" ∋ Fresh 100 ↦ Fresh 107
      , "compose" ∋ Fresh 101 ↦ Fresh 102
      , "eFst" ∋ Fresh 102 ↦ Fresh 103
      , "eSnd" ∋ Fresh 102 ↦ Fresh 105
      , "converse" ∋ Fresh 103 ↦ Fresh 104
      , "during" ∋ Fresh 104 ↦ "subConcepts"
      , "converse" ∋ Fresh 105 ↦ Fresh 106
      , "pre" ∋ Fresh 106 ↦ "concept"
      , "post" ∋ Fresh 107 ↦ "choice"
      , "Start" ∋ Fresh 108 ↦ Fresh 113
      , "Statement" ∋ Fresh 108 ↦ Fresh 109
      , "rule" ∋ Fresh 109 ↦ Fresh 110
      , "eFst" ∋ Fresh 110 ↦ Fresh 111
      , "eSnd" ∋ Fresh 110 ↦ Fresh 112
      , "pre" ∋ Fresh 111 ↦ "syntaxList"
      , "Start" ∋ Fresh 113 ↦ Fresh 118
      , "Statement" ∋ Fresh 113 ↦ Fresh 114
      , "rule" ∋ Fresh 114 ↦ Fresh 115
      , "eFst" ∋ Fresh 115 ↦ Fresh 116
      , "eSnd" ∋ Fresh 115 ↦ Fresh 117
      , "pre" ∋ Fresh 116 ↦ "head2"
      , "post" ∋ Fresh 117 ↦ "recogniser"
      , "Start" ∋ Fresh 118 ↦ Fresh 123
      , "Statement" ∋ Fresh 118 ↦ Fresh 119
      , "rule" ∋ Fresh 119 ↦ Fresh 120
      , "eFst" ∋ Fresh 120 ↦ Fresh 121
      , "eSnd" ∋ Fresh 120 ↦ Fresh 122
      , "pre" ∋ Fresh 121 ↦ "tail2"
      , "post" ∋ Fresh 122 ↦ "continuation"
      , "Start" ∋ Fresh 123 ↦ Fresh 139
      , "Statement" ∋ Fresh 123 ↦ Fresh 124
      , "rule" ∋ Fresh 124 ↦ Fresh 125
      , "eFst" ∋ Fresh 125 ↦ Fresh 126
      , "eSnd" ∋ Fresh 125 ↦ Fresh 138
      , "conjunct" ∋ Fresh 126 ↦ Fresh 127
      , "eFst" ∋ Fresh 127 ↦ Fresh 128
      , "eSnd" ∋ Fresh 127 ↦ Fresh 133
      , "compose" ∋ Fresh 128 ↦ Fresh 129
      , "eFst" ∋ Fresh 129 ↦ Fresh 130
      , "eSnd" ∋ Fresh 129 ↦ Fresh 131
      , "post" ∋ Fresh 130 ↦ "eFst"
      , "converse" ∋ Fresh 131 ↦ Fresh 132
      , "post" ∋ Fresh 132 ↦ "eFst"
      , "compose" ∋ Fresh 133 ↦ Fresh 134
      , "eFst" ∋ Fresh 134 ↦ Fresh 135
      , "eSnd" ∋ Fresh 134 ↦ Fresh 136
      , "post" ∋ Fresh 135 ↦ "eSnd"
      , "converse" ∋ Fresh 136 ↦ Fresh 137
      , "post" ∋ Fresh 137 ↦ "eSnd"
      , "Start" ∋ Fresh 139 ↦ Fresh 148
      , "Statement" ∋ Fresh 139 ↦ Fresh 140
      , "rule" ∋ Fresh 140 ↦ Fresh 141
      , "eFst" ∋ Fresh 141 ↦ Fresh 142
      , "eSnd" ∋ Fresh 141 ↦ Fresh 147
      , "compose" ∋ Fresh 142 ↦ Fresh 143
      , "eFst" ∋ Fresh 143 ↦ Fresh 144
      , "eSnd" ∋ Fresh 143 ↦ Fresh 145
      , "post" ∋ Fresh 144 ↦ "conjunct"
      , "converse" ∋ Fresh 145 ↦ Fresh 146
      , "post" ∋ Fresh 146 ↦ "conjunct"
      , "Start" ∋ Fresh 148 ↦ Fresh 157
      , "Statement" ∋ Fresh 148 ↦ Fresh 149
      , "rule" ∋ Fresh 149 ↦ Fresh 150
      , "eFst" ∋ Fresh 150 ↦ Fresh 151
      , "eSnd" ∋ Fresh 150 ↦ Fresh 156
      , "compose" ∋ Fresh 151 ↦ Fresh 152
      , "eFst" ∋ Fresh 152 ↦ Fresh 153
      , "eSnd" ∋ Fresh 152 ↦ Fresh 154
      , "post" ∋ Fresh 153 ↦ "converse"
      , "converse" ∋ Fresh 154 ↦ Fresh 155
      , "post" ∋ Fresh 155 ↦ "converse"
      , "Start" ∋ Fresh 157 ↦ Fresh 166
      , "Statement" ∋ Fresh 157 ↦ Fresh 158
      , "rule" ∋ Fresh 158 ↦ Fresh 159
      , "eFst" ∋ Fresh 159 ↦ Fresh 160
      , "eSnd" ∋ Fresh 159 ↦ Fresh 165
      , "compose" ∋ Fresh 160 ↦ Fresh 161
      , "eFst" ∋ Fresh 161 ↦ Fresh 162
      , "eSnd" ∋ Fresh 161 ↦ Fresh 163
      , "post" ∋ Fresh 162 ↦ "compose"
      , "converse" ∋ Fresh 163 ↦ Fresh 164
      , "post" ∋ Fresh 164 ↦ "compose"
      , "Start" ∋ Fresh 166 ↦ Fresh 175
      , "Statement" ∋ Fresh 166 ↦ Fresh 167
      , "rule" ∋ Fresh 167 ↦ Fresh 168
      , "eFst" ∋ Fresh 168 ↦ Fresh 169
      , "eSnd" ∋ Fresh 168 ↦ Fresh 174
      , "compose" ∋ Fresh 169 ↦ Fresh 170
      , "eFst" ∋ Fresh 170 ↦ Fresh 171
      , "eSnd" ∋ Fresh 170 ↦ Fresh 172
      , "post" ∋ Fresh 171 ↦ "pre"
      , "converse" ∋ Fresh 172 ↦ Fresh 173
      , "post" ∋ Fresh 173 ↦ "pre"
      , "Start" ∋ Fresh 175 ↦ Fresh 184
      , "Statement" ∋ Fresh 175 ↦ Fresh 176
      , "rule" ∋ Fresh 176 ↦ Fresh 177
      , "eFst" ∋ Fresh 177 ↦ Fresh 178
      , "eSnd" ∋ Fresh 177 ↦ Fresh 183
      , "compose" ∋ Fresh 178 ↦ Fresh 179
      , "eFst" ∋ Fresh 179 ↦ Fresh 180
      , "eSnd" ∋ Fresh 179 ↦ Fresh 181
      , "post" ∋ Fresh 180 ↦ "post"
      , "converse" ∋ Fresh 181 ↦ Fresh 182
      , "post" ∋ Fresh 182 ↦ "post"
      , "Start" ∋ Fresh 184 ↦ Fresh 193
      , "Statement" ∋ Fresh 184 ↦ Fresh 185
      , "rule" ∋ Fresh 185 ↦ Fresh 186
      , "eFst" ∋ Fresh 186 ↦ Fresh 187
      , "eSnd" ∋ Fresh 186 ↦ Fresh 192
      , "compose" ∋ Fresh 187 ↦ Fresh 188
      , "eFst" ∋ Fresh 188 ↦ Fresh 189
      , "eSnd" ∋ Fresh 188 ↦ Fresh 190
      , "post" ∋ Fresh 189 ↦ "during"
      , "converse" ∋ Fresh 190 ↦ Fresh 191
      , "post" ∋ Fresh 191 ↦ "during"
      , "Start" ∋ Fresh 193 ↦ Fresh 198
      , "Statement" ∋ Fresh 193 ↦ Fresh 194
      , "rule" ∋ Fresh 194 ↦ Fresh 195
      , "eFst" ∋ Fresh 195 ↦ Fresh 196
      , "eSnd" ∋ Fresh 195 ↦ Fresh 197
      , "pre" ∋ Fresh 196 ↦ "during"
      , "post" ∋ Fresh 197 ↦ "during"
      , "Start" ∋ Fresh 198 ↦ Fresh 203
      , "Statement" ∋ Fresh 198 ↦ Fresh 199
      , "rule" ∋ Fresh 199 ↦ Fresh 200
      , "eFst" ∋ Fresh 200 ↦ Fresh 201
      , "eSnd" ∋ Fresh 200 ↦ Fresh 202
      , "pre" ∋ Fresh 201 ↦ "pre"
      , "post" ∋ Fresh 202 ↦ "pre"
      , "Start" ∋ Fresh 203 ↦ Fresh 208
      , "Statement" ∋ Fresh 203 ↦ Fresh 204
      , "rule" ∋ Fresh 204 ↦ Fresh 205
      , "eFst" ∋ Fresh 205 ↦ Fresh 206
      , "eSnd" ∋ Fresh 205 ↦ Fresh 207
      , "pre" ∋ Fresh 206 ↦ "post"
      , "post" ∋ Fresh 207 ↦ "post"
      , "Start" ∋ Fresh 208 ↦ Fresh 213
      , "Statement" ∋ Fresh 208 ↦ Fresh 209
      , "rule" ∋ Fresh 209 ↦ Fresh 210
      , "eFst" ∋ Fresh 210 ↦ Fresh 211
      , "eSnd" ∋ Fresh 210 ↦ Fresh 212
      , "pre" ∋ Fresh 211 ↦ "converse"
      , "post" ∋ Fresh 212 ↦ "converse"
      , "Start" ∋ Fresh 213 ↦ Fresh 218
      , "Statement" ∋ Fresh 213 ↦ Fresh 214
      , "rule" ∋ Fresh 214 ↦ Fresh 215
      , "eFst" ∋ Fresh 215 ↦ Fresh 216
      , "eSnd" ∋ Fresh 215 ↦ Fresh 217
      , "pre" ∋ Fresh 216 ↦ "conjunct"
      , "post" ∋ Fresh 217 ↦ "conjunct"
      , "Start" ∋ Fresh 218 ↦ Fresh 223
      , "Statement" ∋ Fresh 218 ↦ Fresh 219
      , "rule" ∋ Fresh 219 ↦ Fresh 220
      , "eFst" ∋ Fresh 220 ↦ Fresh 221
      , "eSnd" ∋ Fresh 220 ↦ Fresh 222
      , "pre" ∋ Fresh 221 ↦ "eFst"
      , "post" ∋ Fresh 222 ↦ "eFst"
      , "Start" ∋ Fresh 223 ↦ Fresh 228
      , "Statement" ∋ Fresh 223 ↦ Fresh 224
      , "rule" ∋ Fresh 224 ↦ Fresh 225
      , "eFst" ∋ Fresh 225 ↦ Fresh 226
      , "eSnd" ∋ Fresh 225 ↦ Fresh 227
      , "pre" ∋ Fresh 226 ↦ "eSnd"
      , "post" ∋ Fresh 227 ↦ "eSnd"
      , "Start" ∋ Fresh 228 ↦ Fresh 233
      , "Statement" ∋ Fresh 228 ↦ Fresh 229
      , "rule" ∋ Fresh 229 ↦ Fresh 230
      , "eFst" ∋ Fresh 230 ↦ Fresh 231
      , "eSnd" ∋ Fresh 230 ↦ Fresh 232
      , "pre" ∋ Fresh 231 ↦ "compose"
      , "post" ∋ Fresh 232 ↦ "compose"
      , "Start" ∋ Fresh 233 ↦ Fresh 238
      , "Statement" ∋ Fresh 233 ↦ Fresh 234
      , "rule" ∋ Fresh 234 ↦ Fresh 235
      , "eFst" ∋ Fresh 235 ↦ Fresh 236
      , "eSnd" ∋ Fresh 235 ↦ Fresh 237
      , "pre" ∋ Fresh 236 ↦ "rule"
      , "post" ∋ Fresh 237 ↦ "rule"
      , "Start" ∋ Fresh 238 ↦ Fresh 243
      , "Statement" ∋ Fresh 238 ↦ Fresh 239
      , "rule" ∋ Fresh 239 ↦ Fresh 240
      , "eFst" ∋ Fresh 240 ↦ Fresh 241
      , "eSnd" ∋ Fresh 240 ↦ Fresh 242
      , "pre" ∋ Fresh 241 ↦ "pair1"
      , "post" ∋ Fresh 242 ↦ "pair1"
      , "Start" ∋ Fresh 243 ↦ Fresh 248
      , "Statement" ∋ Fresh 243 ↦ Fresh 244
      , "rule" ∋ Fresh 244 ↦ Fresh 245
      , "eFst" ∋ Fresh 245 ↦ Fresh 246
      , "eSnd" ∋ Fresh 245 ↦ Fresh 247
      , "pre" ∋ Fresh 246 ↦ "pair2"
      , "post" ∋ Fresh 247 ↦ "pair2"
      , "Start" ∋ Fresh 248 ↦ Fresh 253
      , "Statement" ∋ Fresh 248 ↦ Fresh 249
      , "rule" ∋ Fresh 249 ↦ Fresh 250
      , "eFst" ∋ Fresh 250 ↦ Fresh 251
      , "eSnd" ∋ Fresh 250 ↦ Fresh 252
      , "pre" ∋ Fresh 251 ↦ "declaration"
      , "post" ∋ Fresh 252 ↦ "rule"
      , "Start" ∋ Fresh 253 ↦ Fresh 264
      , "Statement" ∋ Fresh 253 ↦ Fresh 254
      , "rule" ∋ Fresh 254 ↦ Fresh 255
      , "eFst" ∋ Fresh 255 ↦ Fresh 256
      , "eSnd" ∋ Fresh 255 ↦ Fresh 260
      , "compose" ∋ Fresh 256 ↦ Fresh 257
      , "eFst" ∋ Fresh 257 ↦ Fresh 258
      , "eSnd" ∋ Fresh 257 ↦ Fresh 259
      , "pre" ∋ Fresh 258 ↦ "relation"
      , "pre" ∋ Fresh 259 ↦ "string"
      , "compose" ∋ Fresh 260 ↦ Fresh 261
      , "eFst" ∋ Fresh 261 ↦ Fresh 262
      , "eSnd" ∋ Fresh 261 ↦ Fresh 263
      , "post" ∋ Fresh 262 ↦ "eFst"
      , "post" ∋ Fresh 263 ↦ "pre"
      , "Start" ∋ Fresh 264 ↦ Fresh 275
      , "Statement" ∋ Fresh 264 ↦ Fresh 265
      , "rule" ∋ Fresh 265 ↦ Fresh 266
      , "eFst" ∋ Fresh 266 ↦ Fresh 267
      , "eSnd" ∋ Fresh 266 ↦ Fresh 271
      , "compose" ∋ Fresh 267 ↦ Fresh 268
      , "eFst" ∋ Fresh 268 ↦ Fresh 269
      , "eSnd" ∋ Fresh 268 ↦ Fresh 270
      , "pre" ∋ Fresh 269 ↦ "relation"
      , "pre" ∋ Fresh 270 ↦ "string"
      , "compose" ∋ Fresh 271 ↦ Fresh 272
      , "eFst" ∋ Fresh 272 ↦ Fresh 273
      , "eSnd" ∋ Fresh 272 ↦ Fresh 274
      , "post" ∋ Fresh 273 ↦ "eSnd"
      , "post" ∋ Fresh 274 ↦ "post"
      , "Start" ∋ Fresh 275 ↦ Fresh 280
      , "Statement" ∋ Fresh 275 ↦ Fresh 276
      , "rule" ∋ Fresh 276 ↦ Fresh 277
      , "eFst" ∋ Fresh 277 ↦ Fresh 278
      , "eSnd" ∋ Fresh 277 ↦ Fresh 279
      , "pair1" ∋ Fresh 278 ↦ "r1"
      , "pair2" ∋ Fresh 278 ↦ "r1"
      , "post" ∋ Fresh 279 ↦ "rule"
      , "Start" ∋ Fresh 280 ↦ Fresh 285
      , "Statement" ∋ Fresh 280 ↦ Fresh 281
      , "rule" ∋ Fresh 281 ↦ Fresh 282
      , "eFst" ∋ Fresh 282 ↦ Fresh 283
      , "eSnd" ∋ Fresh 282 ↦ Fresh 284
      , "pair1" ∋ Fresh 283 ↦ "r2"
      , "pair2" ∋ Fresh 283 ↦ "r2"
      , "post" ∋ Fresh 284 ↦ "rule"
      , "Start" ∋ Fresh 285 ↦ Fresh 293
      , "Statement" ∋ Fresh 285 ↦ Fresh 286
      , "rule" ∋ Fresh 286 ↦ Fresh 287
      , "eFst" ∋ Fresh 287 ↦ Fresh 288
      , "eSnd" ∋ Fresh 287 ↦ Fresh 289
      , "pair1" ∋ Fresh 288 ↦ "r1"
      , "pair2" ∋ Fresh 288 ↦ "string"
      , "compose" ∋ Fresh 289 ↦ Fresh 290
      , "eFst" ∋ Fresh 290 ↦ Fresh 291
      , "eSnd" ∋ Fresh 290 ↦ Fresh 292
      , "post" ∋ Fresh 291 ↦ "eFst"
      , "post" ∋ Fresh 292 ↦ "pre"
      , "Start" ∋ Fresh 293 ↦ Fresh 301
      , "Statement" ∋ Fresh 293 ↦ Fresh 294
      , "rule" ∋ Fresh 294 ↦ Fresh 295
      , "eFst" ∋ Fresh 295 ↦ Fresh 296
      , "eSnd" ∋ Fresh 295 ↦ Fresh 297
      , "pair1" ∋ Fresh 296 ↦ "r1"
      , "pair2" ∋ Fresh 296 ↦ "string"
      , "compose" ∋ Fresh 297 ↦ Fresh 298
      , "eFst" ∋ Fresh 298 ↦ Fresh 299
      , "eSnd" ∋ Fresh 298 ↦ Fresh 300
      , "post" ∋ Fresh 299 ↦ "eSnd"
      , "post" ∋ Fresh 300 ↦ "post"
      , "Start" ∋ Fresh 301 ↦ Fresh 309
      , "Statement" ∋ Fresh 301 ↦ Fresh 302
      , "rule" ∋ Fresh 302 ↦ Fresh 303
      , "eFst" ∋ Fresh 303 ↦ Fresh 304
      , "eSnd" ∋ Fresh 303 ↦ Fresh 305
      , "pair1" ∋ Fresh 304 ↦ "r2"
      , "pair2" ∋ Fresh 304 ↦ "origin"
      , "compose" ∋ Fresh 305 ↦ Fresh 306
      , "eFst" ∋ Fresh 306 ↦ Fresh 307
      , "eSnd" ∋ Fresh 306 ↦ Fresh 308
      , "post" ∋ Fresh 307 ↦ "eFst"
      , "post" ∋ Fresh 308 ↦ "pre"
      , "Start" ∋ Fresh 309 ↦ Fresh 317
      , "Statement" ∋ Fresh 309 ↦ Fresh 310
      , "rule" ∋ Fresh 310 ↦ Fresh 311
      , "eFst" ∋ Fresh 311 ↦ Fresh 312
      , "eSnd" ∋ Fresh 311 ↦ Fresh 313
      , "pair1" ∋ Fresh 312 ↦ "r2"
      , "pair2" ∋ Fresh 312 ↦ "origin"
      , "compose" ∋ Fresh 313 ↦ Fresh 314
      , "eFst" ∋ Fresh 314 ↦ Fresh 315
      , "eSnd" ∋ Fresh 314 ↦ Fresh 316
      , "post" ∋ Fresh 315 ↦ "eSnd"
      , "post" ∋ Fresh 316 ↦ "post"
      ])
  , ( "cfg"
    , [ "choice" ∋ "Choice" ↦ Fresh 754
      , "choice" ∋ "Continuation" ↦ Fresh 757
      , "choice" ∋ "Continuation" ↦ Fresh 759
      , "nonTerminal" ∋ "QuotedString" ↦ "QuotedString"
      , "rule" ∋ "QuotedString" ↦ Fresh 750
      , "choice" ∋ "Recogniser" ↦ Fresh 760
      , "choice" ∋ "Recogniser" ↦ Fresh 761
      , "choice" ∋ "Start" ↦ Fresh 751
      , "choice" ∋ "Start" ↦ Fresh 753
      , "nonTerminal" ∋ "UnquotedString" ↦ "UnquotedString"
      , "rule" ∋ "UnquotedString" ↦ Fresh 749
      , "nonTerminal" ∋ "choice" ↦ "Continuation"
      , "rule" ∋ "choice" ↦ Fresh 745
      , "nonTerminal" ∋ "continuation" ↦ "Continuation"
      , "rule" ∋ "continuation" ↦ Fresh 746
      , "nonTerminal" ∋ "more" ↦ "Start"
      , "rule" ∋ "more" ↦ Fresh 744
      , "nonTerminal" ∋ "nonTerminal" ↦ "UnquotedString"
      , "rule" ∋ "nonTerminal" ↦ Fresh 748
      , "eFst" ∋ "r1" ↦ Fresh 777
      , "eSnd" ∋ "r1" ↦ Fresh 776
      , "rule" ∋ "r1" ↦ "r1"
      , "eFst" ∋ "r2" ↦ Fresh 775
      , "eSnd" ∋ "r2" ↦ Fresh 774
      , "rule" ∋ "r2" ↦ "r2"
      , "nonTerminal" ∋ "recogniser" ↦ "Recogniser"
      , "rule" ∋ "recogniser" ↦ Fresh 747
      , "nonTerminal" ∋ "start" ↦ "Choice"
      , "rule" ∋ "start" ↦ Fresh 743
      , "eFst" ∋ Fresh 743 ↦ Fresh 778
      , "eSnd" ∋ Fresh 743 ↦ Fresh 779
      , "eFst" ∋ Fresh 744 ↦ Fresh 780
      , "eSnd" ∋ Fresh 744 ↦ Fresh 781
      , "eFst" ∋ Fresh 745 ↦ Fresh 782
      , "eSnd" ∋ Fresh 745 ↦ Fresh 783
      , "eFst" ∋ Fresh 746 ↦ Fresh 784
      , "eSnd" ∋ Fresh 746 ↦ Fresh 785
      , "eFst" ∋ Fresh 747 ↦ Fresh 786
      , "eSnd" ∋ Fresh 747 ↦ Fresh 787
      , "eFst" ∋ Fresh 748 ↦ Fresh 772
      , "eSnd" ∋ Fresh 748 ↦ Fresh 788
      , "eFst" ∋ Fresh 749 ↦ Fresh 764
      , "eSnd" ∋ Fresh 749 ↦ Fresh 789
      , "eFst" ∋ Fresh 750 ↦ Fresh 768
      , "eSnd" ∋ Fresh 750 ↦ Fresh 790
      , "continuation" ∋ Fresh 751 ↦ Fresh 752
      , "recogniser" ∋ Fresh 751 ↦ "more"
      , "recogniser" ∋ Fresh 752 ↦ "start"
      , "continuation" ∋ Fresh 754 ↦ Fresh 755
      , "recogniser" ∋ Fresh 754 ↦ "UnquotedString"
      , "continuation" ∋ Fresh 755 ↦ Fresh 756
      , "recogniser" ∋ Fresh 755 ↦ "\">\""
      , "recogniser" ∋ Fresh 756 ↦ "choice"
      , "continuation" ∋ Fresh 757 ↦ Fresh 758
      , "recogniser" ∋ Fresh 757 ↦ "recogniser"
      , "recogniser" ∋ Fresh 758 ↦ "continuation"
      , "recogniser" ∋ Fresh 760 ↦ "QuotedString"
      , "recogniser" ∋ Fresh 761 ↦ "nonTerminal"
      , "rule" ∋ Fresh 762 ↦ Fresh 763
      , "eFst" ∋ Fresh 763 ↦ Fresh 764
      , "eSnd" ∋ Fresh 763 ↦ Fresh 765
      , "pre" ∋ Fresh 764 ↦ "UnquotedString"
      , "rule" ∋ Fresh 766 ↦ Fresh 767
      , "eFst" ∋ Fresh 767 ↦ Fresh 768
      , "eSnd" ∋ Fresh 767 ↦ Fresh 769
      , "pre" ∋ Fresh 768 ↦ "QuotedString"
      , "rule" ∋ Fresh 770 ↦ Fresh 771
      , "eFst" ∋ Fresh 771 ↦ Fresh 772
      , "eSnd" ∋ Fresh 771 ↦ Fresh 773
      , "pre" ∋ Fresh 772 ↦ "nonTerminal"
      , "post" ∋ Fresh 774 ↦ "origin"
      , "pre" ∋ Fresh 775 ↦ "origin"
      , "post" ∋ Fresh 776 ↦ "string"
      , "pre" ∋ Fresh 777 ↦ "string"
      , "pre" ∋ Fresh 778 ↦ "start"
      , "post" ∋ Fresh 779 ↦ "start"
      , "pre" ∋ Fresh 780 ↦ "more"
      , "post" ∋ Fresh 781 ↦ "more"
      , "pre" ∋ Fresh 782 ↦ "choice"
      , "post" ∋ Fresh 783 ↦ "choice"
      , "pre" ∋ Fresh 784 ↦ "continuation"
      , "post" ∋ Fresh 785 ↦ "continuation"
      , "pre" ∋ Fresh 786 ↦ "recogniser"
      , "post" ∋ Fresh 787 ↦ "recogniser"
      , "post" ∋ Fresh 788 ↦ "nonTerminal"
      , "post" ∋ Fresh 789 ↦ "UnquotedString"
      , "post" ∋ Fresh 790 ↦ "QuotedString"
      ])
  , ( "parser"
    , [ "choice" ∋ "Classification" ↦ Fresh 903
      , "choice" ∋ "ClassificationStatement" ↦ Fresh 897
      , "choice" ∋ "Compose" ↦ Fresh 973
      , "choice" ∋ "ConceptList" ↦ Fresh 907
      , "choice" ∋ "ConceptList" ↦ Fresh 910
      , "choice" ∋ "Conjunct" ↦ Fresh 970
      , "choice" ∋ "ConsConceptList" ↦ Fresh 907
      , "choice" ∋ "ConsSyntaxList" ↦ Fresh 928
      , "choice" ∋ "Declaration" ↦ Fresh 914
      , "choice" ∋ "DeclarationStatement" ↦ Fresh 898
      , "choice" ∋ "DeclarationType" ↦ Fresh 911
      , "choice" ∋ "EmptySyntax" ↦ Fresh 923
      , "choice" ∋ "Expression" ↦ Fresh 950
      , "choice" ∋ "Expression" ↦ Fresh 953
      , "choice" ∋ "Expression" ↦ Fresh 956
      , "choice" ∋ "Expression" ↦ Fresh 958
      , "choice" ∋ "Expression" ↦ Fresh 960
      , "choice" ∋ "Expression" ↦ Fresh 962
      , "choice" ∋ "Expression" ↦ Fresh 964
      , "choice" ∋ "Expression" ↦ Fresh 969
      , "choice" ∋ "QuotedStringElement" ↦ Fresh 932
      , "choice" ∋ "RelationElement" ↦ Fresh 933
      , "choice" ∋ "RuleStatement" ↦ Fresh 945
      , "choice" ∋ "RuleSubset" ↦ Fresh 947
      , "choice" ∋ "Start" ↦ Fresh 900
      , "choice" ∋ "Start" ↦ Fresh 902
      , "nonTerminal" ∋ "Start" ↦ "Start"
      , "rule" ∋ "Start" ↦ Fresh 896
      , "choice" ∋ "Statement" ↦ Fresh 897
      , "choice" ∋ "Statement" ↦ Fresh 898
      , "choice" ∋ "Statement" ↦ Fresh 899
      , "choice" ∋ "Statement" ↦ Fresh 945
      , "nonTerminal" ∋ "Statement" ↦ "Statement"
      , "rule" ∋ "Statement" ↦ Fresh 895
      , "choice" ∋ "Syntax" ↦ Fresh 917
      , "choice" ∋ "Syntax" ↦ Fresh 923
      , "choice" ∋ "SyntaxElement" ↦ Fresh 932
      , "choice" ∋ "SyntaxElement" ↦ Fresh 933
      , "choice" ∋ "SyntaxList" ↦ Fresh 928
      , "choice" ∋ "SyntaxList" ↦ Fresh 931
      , "choice" ∋ "SyntaxStatement" ↦ Fresh 899
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 947
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 970
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 973
      , "nonTerminal" ∋ "classification" ↦ "Classification"
      , "rule" ∋ "classification" ↦ Fresh 878
      , "nonTerminal" ∋ "compose" ↦ "Compose"
      , "rule" ∋ "compose" ↦ Fresh 939
      , "nonTerminal" ∋ "concept" ↦ "String"
      , "rule" ∋ "concept" ↦ Fresh 889
      , "nonTerminal" ∋ "conceptList" ↦ "ConceptList"
      , "rule" ∋ "conceptList" ↦ Fresh 880
      , "nonTerminal" ∋ "concepts" ↦ "DeclarationType"
      , "rule" ∋ "concepts" ↦ Fresh 885
      , "nonTerminal" ∋ "conjunct" ↦ "Conjunct"
      , "rule" ∋ "conjunct" ↦ Fresh 937
      , "nonTerminal" ∋ "converse" ↦ "Expression"
      , "rule" ∋ "converse" ↦ Fresh 938
      , "nonTerminal" ∋ "declaration" ↦ "Declaration"
      , "rule" ∋ "declaration" ↦ Fresh 883
      , "nonTerminal" ∋ "during" ↦ "UnquotedString"
      , "rule" ∋ "during" ↦ Fresh 942
      , "nonTerminal" ∋ "eFst" ↦ "Expression"
      , "rule" ∋ "eFst" ↦ Fresh 935
      , "nonTerminal" ∋ "eSnd" ↦ "Expression"
      , "rule" ∋ "eSnd" ↦ Fresh 936
      , "nonTerminal" ∋ "fst" ↦ "String"
      , "rule" ∋ "fst" ↦ Fresh 886
      , "nonTerminal" ∋ "head1" ↦ "String"
      , "rule" ∋ "head1" ↦ Fresh 881
      , "nonTerminal" ∋ "head2" ↦ "SyntaxElement"
      , "rule" ∋ "head2" ↦ Fresh 892
      , "nonTerminal" ∋ "mainConcept" ↦ "String"
      , "rule" ∋ "mainConcept" ↦ Fresh 879
      , "nonTerminal" ∋ "pair1" ↦ "String"
      , "rule" ∋ "pair1" ↦ Fresh 943
      , "nonTerminal" ∋ "pair2" ↦ "String"
      , "rule" ∋ "pair2" ↦ Fresh 944
      , "nonTerminal" ∋ "post" ↦ "UnquotedString"
      , "rule" ∋ "post" ↦ Fresh 941
      , "nonTerminal" ∋ "pre" ↦ "UnquotedString"
      , "rule" ∋ "pre" ↦ Fresh 940
      , "nonTerminal" ∋ "qstring" ↦ "QuotedString"
      , "rule" ∋ "qstring" ↦ Fresh 894
      , "eFst" ∋ "r1" ↦ Fresh 979
      , "eSnd" ∋ "r1" ↦ Fresh 978
      , "rule" ∋ "r1" ↦ "r1"
      , "eFst" ∋ "r2" ↦ Fresh 977
      , "eSnd" ∋ "r2" ↦ Fresh 976
      , "rule" ∋ "r2" ↦ "r2"
      , "nonTerminal" ∋ "relation" ↦ "StringAndOrigin"
      , "rule" ∋ "relation" ↦ Fresh 884
      , "nonTerminal" ∋ "relationName" ↦ "UnquotedString"
      , "rule" ∋ "relationName" ↦ Fresh 890
      , "nonTerminal" ∋ "rule" ↦ "RuleSubset"
      , "rule" ∋ "rule" ↦ Fresh 934
      , "nonTerminal" ∋ "snd" ↦ "String"
      , "rule" ∋ "snd" ↦ Fresh 887
      , "nonTerminal" ∋ "syntax" ↦ "Syntax"
      , "rule" ∋ "syntax" ↦ Fresh 888
      , "nonTerminal" ∋ "syntaxList" ↦ "SyntaxList"
      , "rule" ∋ "syntaxList" ↦ Fresh 891
      , "nonTerminal" ∋ "tail1" ↦ "ConceptList"
      , "rule" ∋ "tail1" ↦ Fresh 882
      , "nonTerminal" ∋ "tail2" ↦ "SyntaxList"
      , "rule" ∋ "tail2" ↦ Fresh 893
      , "eFst" ∋ Fresh 878 ↦ Fresh 980
      , "eSnd" ∋ Fresh 878 ↦ Fresh 981
      , "eFst" ∋ Fresh 879 ↦ Fresh 982
      , "eSnd" ∋ Fresh 879 ↦ Fresh 983
      , "eFst" ∋ Fresh 880 ↦ Fresh 984
      , "eSnd" ∋ Fresh 880 ↦ Fresh 985
      , "eFst" ∋ Fresh 881 ↦ Fresh 986
      , "eSnd" ∋ Fresh 881 ↦ Fresh 987
      , "eFst" ∋ Fresh 882 ↦ Fresh 988
      , "eSnd" ∋ Fresh 882 ↦ Fresh 989
      , "eFst" ∋ Fresh 883 ↦ Fresh 990
      , "eSnd" ∋ Fresh 883 ↦ Fresh 991
      , "eFst" ∋ Fresh 884 ↦ Fresh 992
      , "eSnd" ∋ Fresh 884 ↦ Fresh 993
      , "eFst" ∋ Fresh 885 ↦ Fresh 994
      , "eSnd" ∋ Fresh 885 ↦ Fresh 995
      , "eFst" ∋ Fresh 886 ↦ Fresh 996
      , "eSnd" ∋ Fresh 886 ↦ Fresh 997
      , "eFst" ∋ Fresh 887 ↦ Fresh 998
      , "eSnd" ∋ Fresh 887 ↦ Fresh 999
      , "eFst" ∋ Fresh 888 ↦ Fresh 1000
      , "eSnd" ∋ Fresh 888 ↦ Fresh 1001
      , "eFst" ∋ Fresh 889 ↦ Fresh 1002
      , "eSnd" ∋ Fresh 889 ↦ Fresh 1003
      , "eFst" ∋ Fresh 890 ↦ Fresh 1004
      , "eSnd" ∋ Fresh 890 ↦ Fresh 1005
      , "eFst" ∋ Fresh 891 ↦ Fresh 1006
      , "eSnd" ∋ Fresh 891 ↦ Fresh 1007
      , "eFst" ∋ Fresh 892 ↦ Fresh 1008
      , "eSnd" ∋ Fresh 892 ↦ Fresh 1009
      , "eFst" ∋ Fresh 893 ↦ Fresh 1010
      , "eSnd" ∋ Fresh 893 ↦ Fresh 1011
      , "eFst" ∋ Fresh 894 ↦ Fresh 1012
      , "eSnd" ∋ Fresh 894 ↦ Fresh 1013
      , "eFst" ∋ Fresh 895 ↦ Fresh 1014
      , "eSnd" ∋ Fresh 895 ↦ Fresh 1015
      , "eFst" ∋ Fresh 896 ↦ Fresh 1016
      , "eSnd" ∋ Fresh 896 ↦ Fresh 1017
      , "recogniser" ∋ Fresh 897 ↦ "classification"
      , "recogniser" ∋ Fresh 898 ↦ "declaration"
      , "recogniser" ∋ Fresh 899 ↦ "syntax"
      , "continuation" ∋ Fresh 900 ↦ Fresh 901
      , "recogniser" ∋ Fresh 900 ↦ "Statement"
      , "recogniser" ∋ Fresh 901 ↦ "Start"
      , "continuation" ∋ Fresh 903 ↦ Fresh 904
      , "recogniser" ∋ Fresh 903 ↦ "\"CLASSIFY\""
      , "continuation" ∋ Fresh 904 ↦ Fresh 905
      , "recogniser" ∋ Fresh 904 ↦ "mainConcept"
      , "continuation" ∋ Fresh 905 ↦ Fresh 906
      , "recogniser" ∋ Fresh 905 ↦ "\"IS\""
      , "recogniser" ∋ Fresh 906 ↦ "conceptList"
      , "continuation" ∋ Fresh 907 ↦ Fresh 908
      , "recogniser" ∋ Fresh 907 ↦ "head1"
      , "continuation" ∋ Fresh 908 ↦ Fresh 909
      , "recogniser" ∋ Fresh 908 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 909 ↦ "tail1"
      , "recogniser" ∋ Fresh 910 ↦ "head1"
      , "continuation" ∋ Fresh 911 ↦ Fresh 912
      , "recogniser" ∋ Fresh 911 ↦ "fst"
      , "continuation" ∋ Fresh 912 ↦ Fresh 913
      , "recogniser" ∋ Fresh 912 ↦ "\"*\""
      , "recogniser" ∋ Fresh 913 ↦ "snd"
      , "continuation" ∋ Fresh 914 ↦ Fresh 915
      , "recogniser" ∋ Fresh 914 ↦ "relation"
      , "continuation" ∋ Fresh 915 ↦ Fresh 916
      , "recogniser" ∋ Fresh 915 ↦ "\"::\""
      , "recogniser" ∋ Fresh 916 ↦ "concepts"
      , "continuation" ∋ Fresh 917 ↦ Fresh 918
      , "recogniser" ∋ Fresh 917 ↦ "\"VIEW\""
      , "continuation" ∋ Fresh 918 ↦ Fresh 919
      , "recogniser" ∋ Fresh 918 ↦ "concept"
      , "continuation" ∋ Fresh 919 ↦ Fresh 920
      , "recogniser" ∋ Fresh 919 ↦ "\"=\""
      , "continuation" ∋ Fresh 920 ↦ Fresh 921
      , "recogniser" ∋ Fresh 920 ↦ "\"[\""
      , "continuation" ∋ Fresh 921 ↦ Fresh 922
      , "recogniser" ∋ Fresh 921 ↦ "syntaxList"
      , "recogniser" ∋ Fresh 922 ↦ "\"]\""
      , "continuation" ∋ Fresh 923 ↦ Fresh 924
      , "recogniser" ∋ Fresh 923 ↦ "\"VIEW\""
      , "continuation" ∋ Fresh 924 ↦ Fresh 925
      , "recogniser" ∋ Fresh 924 ↦ "concept"
      , "continuation" ∋ Fresh 925 ↦ Fresh 926
      , "recogniser" ∋ Fresh 925 ↦ "\"=\""
      , "continuation" ∋ Fresh 926 ↦ Fresh 927
      , "recogniser" ∋ Fresh 926 ↦ "\"[\""
      , "recogniser" ∋ Fresh 927 ↦ "\"]\""
      , "continuation" ∋ Fresh 928 ↦ Fresh 929
      , "recogniser" ∋ Fresh 928 ↦ "head2"
      , "continuation" ∋ Fresh 929 ↦ Fresh 930
      , "recogniser" ∋ Fresh 929 ↦ "\",\""
      , "recogniser" ∋ Fresh 930 ↦ "tail2"
      , "recogniser" ∋ Fresh 931 ↦ "head2"
      , "recogniser" ∋ Fresh 932 ↦ "qstring"
      , "recogniser" ∋ Fresh 933 ↦ "relationName"
      , "eFst" ∋ Fresh 934 ↦ Fresh 1018
      , "eSnd" ∋ Fresh 934 ↦ Fresh 1019
      , "eFst" ∋ Fresh 935 ↦ Fresh 1020
      , "eSnd" ∋ Fresh 935 ↦ Fresh 1021
      , "eFst" ∋ Fresh 936 ↦ Fresh 1022
      , "eSnd" ∋ Fresh 936 ↦ Fresh 1023
      , "eFst" ∋ Fresh 937 ↦ Fresh 1024
      , "eSnd" ∋ Fresh 937 ↦ Fresh 1025
      , "eFst" ∋ Fresh 938 ↦ Fresh 1026
      , "eSnd" ∋ Fresh 938 ↦ Fresh 1027
      , "eFst" ∋ Fresh 939 ↦ Fresh 1028
      , "eSnd" ∋ Fresh 939 ↦ Fresh 1029
      , "eFst" ∋ Fresh 940 ↦ Fresh 1030
      , "eSnd" ∋ Fresh 940 ↦ Fresh 1031
      , "eFst" ∋ Fresh 941 ↦ Fresh 1032
      , "eSnd" ∋ Fresh 941 ↦ Fresh 1033
      , "eFst" ∋ Fresh 942 ↦ Fresh 1034
      , "eSnd" ∋ Fresh 942 ↦ Fresh 1035
      , "eFst" ∋ Fresh 943 ↦ Fresh 1036
      , "eSnd" ∋ Fresh 943 ↦ Fresh 1037
      , "eFst" ∋ Fresh 944 ↦ Fresh 1038
      , "eSnd" ∋ Fresh 944 ↦ Fresh 1039
      , "continuation" ∋ Fresh 945 ↦ Fresh 946
      , "recogniser" ∋ Fresh 945 ↦ "\"RULE\""
      , "recogniser" ∋ Fresh 946 ↦ "rule"
      , "continuation" ∋ Fresh 947 ↦ Fresh 948
      , "recogniser" ∋ Fresh 947 ↦ "eFst"
      , "continuation" ∋ Fresh 948 ↦ Fresh 949
      , "recogniser" ∋ Fresh 948 ↦ "\"|-\""
      , "recogniser" ∋ Fresh 949 ↦ "eSnd"
      , "continuation" ∋ Fresh 950 ↦ Fresh 951
      , "recogniser" ∋ Fresh 950 ↦ "\"(\""
      , "continuation" ∋ Fresh 951 ↦ Fresh 952
      , "recogniser" ∋ Fresh 951 ↦ "conjunct"
      , "recogniser" ∋ Fresh 952 ↦ "\")\""
      , "continuation" ∋ Fresh 953 ↦ Fresh 954
      , "recogniser" ∋ Fresh 953 ↦ "\"(\""
      , "continuation" ∋ Fresh 954 ↦ Fresh 955
      , "recogniser" ∋ Fresh 954 ↦ "compose"
      , "recogniser" ∋ Fresh 955 ↦ "\")\""
      , "continuation" ∋ Fresh 956 ↦ Fresh 957
      , "recogniser" ∋ Fresh 956 ↦ "converse"
      , "recogniser" ∋ Fresh 957 ↦ "\"~\""
      , "continuation" ∋ Fresh 958 ↦ Fresh 959
      , "recogniser" ∋ Fresh 958 ↦ "\"pre\""
      , "recogniser" ∋ Fresh 959 ↦ "pre"
      , "continuation" ∋ Fresh 960 ↦ Fresh 961
      , "recogniser" ∋ Fresh 960 ↦ "\"post\""
      , "recogniser" ∋ Fresh 961 ↦ "post"
      , "continuation" ∋ Fresh 962 ↦ Fresh 963
      , "recogniser" ∋ Fresh 962 ↦ "\"during\""
      , "recogniser" ∋ Fresh 963 ↦ "during"
      , "continuation" ∋ Fresh 964 ↦ Fresh 965
      , "recogniser" ∋ Fresh 964 ↦ "\"<\""
      , "continuation" ∋ Fresh 965 ↦ Fresh 966
      , "recogniser" ∋ Fresh 965 ↦ "pair1"
      , "continuation" ∋ Fresh 966 ↦ Fresh 967
      , "recogniser" ∋ Fresh 966 ↦ "\",\""
      , "continuation" ∋ Fresh 967 ↦ Fresh 968
      , "recogniser" ∋ Fresh 967 ↦ "pair2"
      , "recogniser" ∋ Fresh 968 ↦ "\">\""
      , "recogniser" ∋ Fresh 969 ↦ "\"I\""
      , "continuation" ∋ Fresh 970 ↦ Fresh 971
      , "recogniser" ∋ Fresh 970 ↦ "eFst"
      , "continuation" ∋ Fresh 971 ↦ Fresh 972
      , "recogniser" ∋ Fresh 971 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 972 ↦ "eSnd"
      , "continuation" ∋ Fresh 973 ↦ Fresh 974
      , "recogniser" ∋ Fresh 973 ↦ "eFst"
      , "continuation" ∋ Fresh 974 ↦ Fresh 975
      , "recogniser" ∋ Fresh 974 ↦ "\";\""
      , "recogniser" ∋ Fresh 975 ↦ "eSnd"
      , "post" ∋ Fresh 976 ↦ "origin"
      , "pre" ∋ Fresh 977 ↦ "origin"
      , "post" ∋ Fresh 978 ↦ "string"
      , "pre" ∋ Fresh 979 ↦ "string"
      , "pre" ∋ Fresh 980 ↦ "classification"
      , "post" ∋ Fresh 981 ↦ "classification"
      , "pre" ∋ Fresh 982 ↦ "mainConcept"
      , "post" ∋ Fresh 983 ↦ "mainConcept"
      , "pre" ∋ Fresh 984 ↦ "conceptList"
      , "post" ∋ Fresh 985 ↦ "conceptList"
      , "pre" ∋ Fresh 986 ↦ "head1"
      , "post" ∋ Fresh 987 ↦ "head1"
      , "pre" ∋ Fresh 988 ↦ "tail1"
      , "post" ∋ Fresh 989 ↦ "tail1"
      , "pre" ∋ Fresh 990 ↦ "declaration"
      , "post" ∋ Fresh 991 ↦ "declaration"
      , "pre" ∋ Fresh 992 ↦ "relation"
      , "post" ∋ Fresh 993 ↦ "relation"
      , "pre" ∋ Fresh 994 ↦ "concepts"
      , "post" ∋ Fresh 995 ↦ "concepts"
      , "pre" ∋ Fresh 996 ↦ "fst"
      , "post" ∋ Fresh 997 ↦ "fst"
      , "pre" ∋ Fresh 998 ↦ "snd"
      , "post" ∋ Fresh 999 ↦ "snd"
      , "pre" ∋ Fresh 1000 ↦ "syntax"
      , "post" ∋ Fresh 1001 ↦ "syntax"
      , "pre" ∋ Fresh 1002 ↦ "concept"
      , "post" ∋ Fresh 1003 ↦ "concept"
      , "pre" ∋ Fresh 1004 ↦ "relationName"
      , "post" ∋ Fresh 1005 ↦ "relationName"
      , "pre" ∋ Fresh 1006 ↦ "syntaxList"
      , "post" ∋ Fresh 1007 ↦ "syntaxList"
      , "pre" ∋ Fresh 1008 ↦ "head2"
      , "post" ∋ Fresh 1009 ↦ "head2"
      , "pre" ∋ Fresh 1010 ↦ "tail2"
      , "post" ∋ Fresh 1011 ↦ "tail2"
      , "pre" ∋ Fresh 1012 ↦ "qstring"
      , "post" ∋ Fresh 1013 ↦ "qstring"
      , "pre" ∋ Fresh 1014 ↦ "Statement"
      , "post" ∋ Fresh 1015 ↦ "Statement"
      , "pre" ∋ Fresh 1016 ↦ "Start"
      , "post" ∋ Fresh 1017 ↦ "Start"
      , "pre" ∋ Fresh 1018 ↦ "rule"
      , "post" ∋ Fresh 1019 ↦ "rule"
      , "pre" ∋ Fresh 1020 ↦ "eFst"
      , "post" ∋ Fresh 1021 ↦ "eFst"
      , "pre" ∋ Fresh 1022 ↦ "eSnd"
      , "post" ∋ Fresh 1023 ↦ "eSnd"
      , "pre" ∋ Fresh 1024 ↦ "conjunct"
      , "post" ∋ Fresh 1025 ↦ "conjunct"
      , "pre" ∋ Fresh 1026 ↦ "converse"
      , "post" ∋ Fresh 1027 ↦ "converse"
      , "pre" ∋ Fresh 1028 ↦ "compose"
      , "post" ∋ Fresh 1029 ↦ "compose"
      , "pre" ∋ Fresh 1030 ↦ "pre"
      , "post" ∋ Fresh 1031 ↦ "pre"
      , "pre" ∋ Fresh 1032 ↦ "post"
      , "post" ∋ Fresh 1033 ↦ "post"
      , "pre" ∋ Fresh 1034 ↦ "during"
      , "post" ∋ Fresh 1035 ↦ "during"
      , "pre" ∋ Fresh 1036 ↦ "pair1"
      , "post" ∋ Fresh 1037 ↦ "pair1"
      , "pre" ∋ Fresh 1038 ↦ "pair2"
      , "post" ∋ Fresh 1039 ↦ "pair2"
      ])
  , ( "switches"
    , [ "cur" ∋ Fresh 1377 ↦ Fresh 1377
      , "first" ∋ Fresh 1377 ↦ Fresh 1387
      , "next" ∋ Fresh 1377 ↦ Fresh 1378
      , "string" ∋ Fresh 1377 ↦ "\"i\""
      , "next" ∋ Fresh 1378 ↦ Fresh 1379
      , "string" ∋ Fresh 1378 ↦ "\"asParser\""
      , "first" ∋ Fresh 1379 ↦ Fresh 1388
      , "next" ∋ Fresh 1379 ↦ Fresh 1380
      , "string" ∋ Fresh 1379 ↦ "\"i\""
      , "first" ∋ Fresh 1380 ↦ Fresh 1389
      , "next" ∋ Fresh 1380 ↦ Fresh 1381
      , "string" ∋ Fresh 1380 ↦ "\"apply\""
      , "first" ∋ Fresh 1381 ↦ Fresh 1392
      , "next" ∋ Fresh 1381 ↦ Fresh 1382
      , "string" ∋ Fresh 1381 ↦ "\"i\""
      , "first" ∋ Fresh 1382 ↦ Fresh 1393
      , "next" ∋ Fresh 1382 ↦ Fresh 1383
      , "string" ∋ Fresh 1382 ↦ "\"apply\""
      , "first" ∋ Fresh 1383 ↦ Fresh 1396
      , "next" ∋ Fresh 1383 ↦ Fresh 1384
      , "string" ∋ Fresh 1383 ↦ "\"apply\""
      , "first" ∋ Fresh 1384 ↦ Fresh 1398
      , "next" ∋ Fresh 1384 ↦ Fresh 1385
      , "string" ∋ Fresh 1384 ↦ "\"apply\""
      , "first" ∋ Fresh 1385 ↦ Fresh 1400
      , "next" ∋ Fresh 1385 ↦ Fresh 1386
      , "string" ∋ Fresh 1385 ↦ "\"collect\""
      , "first" ∋ Fresh 1386 ↦ Fresh 1401
      , "string" ∋ Fresh 1386 ↦ "\"showTS\""
      , "string" ∋ Fresh 1387 ↦ "\"boot.ASL\""
      , "string" ∋ Fresh 1388 ↦ "\"asParser.ASL\""
      , "next" ∋ Fresh 1389 ↦ Fresh 1390
      , "string" ∋ Fresh 1389 ↦ "\"parser\""
      , "next" ∋ Fresh 1390 ↦ Fresh 1391
      , "string" ∋ Fresh 1390 ↦ "\"population\""
      , "string" ∋ Fresh 1391 ↦ "\"asParser\""
      , "string" ∋ Fresh 1392 ↦ "\"cfg.ASL\""
      , "next" ∋ Fresh 1393 ↦ Fresh 1394
      , "string" ∋ Fresh 1393 ↦ "\"asParser\""
      , "next" ∋ Fresh 1394 ↦ Fresh 1395
      , "string" ∋ Fresh 1394 ↦ "\"population\""
      , "string" ∋ Fresh 1395 ↦ "\"cfg\""
      , "next" ∋ Fresh 1396 ↦ Fresh 1397
      , "string" ∋ Fresh 1396 ↦ "\"del\""
      , "string" ∋ Fresh 1397 ↦ "\"switches\""
      , "next" ∋ Fresh 1398 ↦ Fresh 1399
      , "string" ∋ Fresh 1398 ↦ "\"del\""
      , "string" ∋ Fresh 1399 ↦ "\"population\""
      , "string" ∋ Fresh 1400 ↦ "\"state\""
      , "string" ∋ Fresh 1401 ↦ "\"state\""
      ])
  ];}
