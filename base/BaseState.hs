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
  , ( "parser"
    , [ "choice" ∋ "Classification" ↦ Fresh 768
      , "choice" ∋ "ClassificationStatement" ↦ Fresh 762
      , "choice" ∋ "Compose" ↦ Fresh 838
      , "choice" ∋ "ConceptList" ↦ Fresh 772
      , "choice" ∋ "ConceptList" ↦ Fresh 775
      , "choice" ∋ "Conjunct" ↦ Fresh 835
      , "choice" ∋ "ConsConceptList" ↦ Fresh 772
      , "choice" ∋ "ConsSyntaxList" ↦ Fresh 793
      , "choice" ∋ "Declaration" ↦ Fresh 779
      , "choice" ∋ "DeclarationStatement" ↦ Fresh 763
      , "choice" ∋ "DeclarationType" ↦ Fresh 776
      , "choice" ∋ "EmptySyntax" ↦ Fresh 788
      , "choice" ∋ "Expression" ↦ Fresh 815
      , "choice" ∋ "Expression" ↦ Fresh 818
      , "choice" ∋ "Expression" ↦ Fresh 821
      , "choice" ∋ "Expression" ↦ Fresh 823
      , "choice" ∋ "Expression" ↦ Fresh 825
      , "choice" ∋ "Expression" ↦ Fresh 827
      , "choice" ∋ "Expression" ↦ Fresh 829
      , "choice" ∋ "Expression" ↦ Fresh 834
      , "choice" ∋ "QuotedStringElement" ↦ Fresh 797
      , "choice" ∋ "RelationElement" ↦ Fresh 798
      , "choice" ∋ "RuleStatement" ↦ Fresh 810
      , "choice" ∋ "RuleSubset" ↦ Fresh 812
      , "choice" ∋ "Start" ↦ Fresh 765
      , "choice" ∋ "Start" ↦ Fresh 767
      , "nonTerminal" ∋ "Start" ↦ "Start"
      , "rule" ∋ "Start" ↦ Fresh 761
      , "choice" ∋ "Statement" ↦ Fresh 762
      , "choice" ∋ "Statement" ↦ Fresh 763
      , "choice" ∋ "Statement" ↦ Fresh 764
      , "choice" ∋ "Statement" ↦ Fresh 810
      , "nonTerminal" ∋ "Statement" ↦ "Statement"
      , "rule" ∋ "Statement" ↦ Fresh 760
      , "choice" ∋ "Syntax" ↦ Fresh 782
      , "choice" ∋ "Syntax" ↦ Fresh 788
      , "choice" ∋ "SyntaxElement" ↦ Fresh 797
      , "choice" ∋ "SyntaxElement" ↦ Fresh 798
      , "choice" ∋ "SyntaxList" ↦ Fresh 793
      , "choice" ∋ "SyntaxList" ↦ Fresh 796
      , "choice" ∋ "SyntaxStatement" ↦ Fresh 764
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 812
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 835
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 838
      , "nonTerminal" ∋ "classification" ↦ "Classification"
      , "rule" ∋ "classification" ↦ Fresh 743
      , "nonTerminal" ∋ "compose" ↦ "Compose"
      , "rule" ∋ "compose" ↦ Fresh 804
      , "nonTerminal" ∋ "concept" ↦ "String"
      , "rule" ∋ "concept" ↦ Fresh 754
      , "nonTerminal" ∋ "conceptList" ↦ "ConceptList"
      , "rule" ∋ "conceptList" ↦ Fresh 745
      , "nonTerminal" ∋ "concepts" ↦ "DeclarationType"
      , "rule" ∋ "concepts" ↦ Fresh 750
      , "nonTerminal" ∋ "conjunct" ↦ "Conjunct"
      , "rule" ∋ "conjunct" ↦ Fresh 802
      , "nonTerminal" ∋ "converse" ↦ "Expression"
      , "rule" ∋ "converse" ↦ Fresh 803
      , "nonTerminal" ∋ "declaration" ↦ "Declaration"
      , "rule" ∋ "declaration" ↦ Fresh 748
      , "nonTerminal" ∋ "during" ↦ "UnquotedString"
      , "rule" ∋ "during" ↦ Fresh 807
      , "nonTerminal" ∋ "eFst" ↦ "Expression"
      , "rule" ∋ "eFst" ↦ Fresh 800
      , "nonTerminal" ∋ "eSnd" ↦ "Expression"
      , "rule" ∋ "eSnd" ↦ Fresh 801
      , "nonTerminal" ∋ "fst" ↦ "String"
      , "rule" ∋ "fst" ↦ Fresh 751
      , "nonTerminal" ∋ "head1" ↦ "String"
      , "rule" ∋ "head1" ↦ Fresh 746
      , "nonTerminal" ∋ "head2" ↦ "SyntaxElement"
      , "rule" ∋ "head2" ↦ Fresh 757
      , "nonTerminal" ∋ "mainConcept" ↦ "String"
      , "rule" ∋ "mainConcept" ↦ Fresh 744
      , "nonTerminal" ∋ "pair1" ↦ "String"
      , "rule" ∋ "pair1" ↦ Fresh 808
      , "nonTerminal" ∋ "pair2" ↦ "String"
      , "rule" ∋ "pair2" ↦ Fresh 809
      , "nonTerminal" ∋ "post" ↦ "UnquotedString"
      , "rule" ∋ "post" ↦ Fresh 806
      , "nonTerminal" ∋ "pre" ↦ "UnquotedString"
      , "rule" ∋ "pre" ↦ Fresh 805
      , "nonTerminal" ∋ "qstring" ↦ "QuotedString"
      , "rule" ∋ "qstring" ↦ Fresh 759
      , "eFst" ∋ "r1" ↦ Fresh 844
      , "eSnd" ∋ "r1" ↦ Fresh 843
      , "rule" ∋ "r1" ↦ "r1"
      , "eFst" ∋ "r2" ↦ Fresh 842
      , "eSnd" ∋ "r2" ↦ Fresh 841
      , "rule" ∋ "r2" ↦ "r2"
      , "nonTerminal" ∋ "relation" ↦ "StringAndOrigin"
      , "rule" ∋ "relation" ↦ Fresh 749
      , "nonTerminal" ∋ "relationName" ↦ "UnquotedString"
      , "rule" ∋ "relationName" ↦ Fresh 755
      , "nonTerminal" ∋ "rule" ↦ "RuleSubset"
      , "rule" ∋ "rule" ↦ Fresh 799
      , "nonTerminal" ∋ "snd" ↦ "String"
      , "rule" ∋ "snd" ↦ Fresh 752
      , "nonTerminal" ∋ "syntax" ↦ "Syntax"
      , "rule" ∋ "syntax" ↦ Fresh 753
      , "nonTerminal" ∋ "syntaxList" ↦ "SyntaxList"
      , "rule" ∋ "syntaxList" ↦ Fresh 756
      , "nonTerminal" ∋ "tail1" ↦ "ConceptList"
      , "rule" ∋ "tail1" ↦ Fresh 747
      , "nonTerminal" ∋ "tail2" ↦ "SyntaxList"
      , "rule" ∋ "tail2" ↦ Fresh 758
      , "eFst" ∋ Fresh 743 ↦ Fresh 845
      , "eSnd" ∋ Fresh 743 ↦ Fresh 846
      , "eFst" ∋ Fresh 744 ↦ Fresh 847
      , "eSnd" ∋ Fresh 744 ↦ Fresh 848
      , "eFst" ∋ Fresh 745 ↦ Fresh 849
      , "eSnd" ∋ Fresh 745 ↦ Fresh 850
      , "eFst" ∋ Fresh 746 ↦ Fresh 851
      , "eSnd" ∋ Fresh 746 ↦ Fresh 852
      , "eFst" ∋ Fresh 747 ↦ Fresh 853
      , "eSnd" ∋ Fresh 747 ↦ Fresh 854
      , "eFst" ∋ Fresh 748 ↦ Fresh 855
      , "eSnd" ∋ Fresh 748 ↦ Fresh 856
      , "eFst" ∋ Fresh 749 ↦ Fresh 857
      , "eSnd" ∋ Fresh 749 ↦ Fresh 858
      , "eFst" ∋ Fresh 750 ↦ Fresh 859
      , "eSnd" ∋ Fresh 750 ↦ Fresh 860
      , "eFst" ∋ Fresh 751 ↦ Fresh 861
      , "eSnd" ∋ Fresh 751 ↦ Fresh 862
      , "eFst" ∋ Fresh 752 ↦ Fresh 863
      , "eSnd" ∋ Fresh 752 ↦ Fresh 864
      , "eFst" ∋ Fresh 753 ↦ Fresh 865
      , "eSnd" ∋ Fresh 753 ↦ Fresh 866
      , "eFst" ∋ Fresh 754 ↦ Fresh 867
      , "eSnd" ∋ Fresh 754 ↦ Fresh 868
      , "eFst" ∋ Fresh 755 ↦ Fresh 869
      , "eSnd" ∋ Fresh 755 ↦ Fresh 870
      , "eFst" ∋ Fresh 756 ↦ Fresh 871
      , "eSnd" ∋ Fresh 756 ↦ Fresh 872
      , "eFst" ∋ Fresh 757 ↦ Fresh 873
      , "eSnd" ∋ Fresh 757 ↦ Fresh 874
      , "eFst" ∋ Fresh 758 ↦ Fresh 875
      , "eSnd" ∋ Fresh 758 ↦ Fresh 876
      , "eFst" ∋ Fresh 759 ↦ Fresh 877
      , "eSnd" ∋ Fresh 759 ↦ Fresh 878
      , "eFst" ∋ Fresh 760 ↦ Fresh 879
      , "eSnd" ∋ Fresh 760 ↦ Fresh 880
      , "eFst" ∋ Fresh 761 ↦ Fresh 881
      , "eSnd" ∋ Fresh 761 ↦ Fresh 882
      , "recogniser" ∋ Fresh 762 ↦ "classification"
      , "recogniser" ∋ Fresh 763 ↦ "declaration"
      , "recogniser" ∋ Fresh 764 ↦ "syntax"
      , "continuation" ∋ Fresh 765 ↦ Fresh 766
      , "recogniser" ∋ Fresh 765 ↦ "Statement"
      , "recogniser" ∋ Fresh 766 ↦ "Start"
      , "continuation" ∋ Fresh 768 ↦ Fresh 769
      , "recogniser" ∋ Fresh 768 ↦ "\"CLASSIFY\""
      , "continuation" ∋ Fresh 769 ↦ Fresh 770
      , "recogniser" ∋ Fresh 769 ↦ "mainConcept"
      , "continuation" ∋ Fresh 770 ↦ Fresh 771
      , "recogniser" ∋ Fresh 770 ↦ "\"IS\""
      , "recogniser" ∋ Fresh 771 ↦ "conceptList"
      , "continuation" ∋ Fresh 772 ↦ Fresh 773
      , "recogniser" ∋ Fresh 772 ↦ "head1"
      , "continuation" ∋ Fresh 773 ↦ Fresh 774
      , "recogniser" ∋ Fresh 773 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 774 ↦ "tail1"
      , "recogniser" ∋ Fresh 775 ↦ "head1"
      , "continuation" ∋ Fresh 776 ↦ Fresh 777
      , "recogniser" ∋ Fresh 776 ↦ "fst"
      , "continuation" ∋ Fresh 777 ↦ Fresh 778
      , "recogniser" ∋ Fresh 777 ↦ "\"*\""
      , "recogniser" ∋ Fresh 778 ↦ "snd"
      , "continuation" ∋ Fresh 779 ↦ Fresh 780
      , "recogniser" ∋ Fresh 779 ↦ "relation"
      , "continuation" ∋ Fresh 780 ↦ Fresh 781
      , "recogniser" ∋ Fresh 780 ↦ "\"::\""
      , "recogniser" ∋ Fresh 781 ↦ "concepts"
      , "continuation" ∋ Fresh 782 ↦ Fresh 783
      , "recogniser" ∋ Fresh 782 ↦ "\"VIEW\""
      , "continuation" ∋ Fresh 783 ↦ Fresh 784
      , "recogniser" ∋ Fresh 783 ↦ "concept"
      , "continuation" ∋ Fresh 784 ↦ Fresh 785
      , "recogniser" ∋ Fresh 784 ↦ "\"=\""
      , "continuation" ∋ Fresh 785 ↦ Fresh 786
      , "recogniser" ∋ Fresh 785 ↦ "\"[\""
      , "continuation" ∋ Fresh 786 ↦ Fresh 787
      , "recogniser" ∋ Fresh 786 ↦ "syntaxList"
      , "recogniser" ∋ Fresh 787 ↦ "\"]\""
      , "continuation" ∋ Fresh 788 ↦ Fresh 789
      , "recogniser" ∋ Fresh 788 ↦ "\"VIEW\""
      , "continuation" ∋ Fresh 789 ↦ Fresh 790
      , "recogniser" ∋ Fresh 789 ↦ "concept"
      , "continuation" ∋ Fresh 790 ↦ Fresh 791
      , "recogniser" ∋ Fresh 790 ↦ "\"=\""
      , "continuation" ∋ Fresh 791 ↦ Fresh 792
      , "recogniser" ∋ Fresh 791 ↦ "\"[\""
      , "recogniser" ∋ Fresh 792 ↦ "\"]\""
      , "continuation" ∋ Fresh 793 ↦ Fresh 794
      , "recogniser" ∋ Fresh 793 ↦ "head2"
      , "continuation" ∋ Fresh 794 ↦ Fresh 795
      , "recogniser" ∋ Fresh 794 ↦ "\",\""
      , "recogniser" ∋ Fresh 795 ↦ "tail2"
      , "recogniser" ∋ Fresh 796 ↦ "head2"
      , "recogniser" ∋ Fresh 797 ↦ "qstring"
      , "recogniser" ∋ Fresh 798 ↦ "relationName"
      , "eFst" ∋ Fresh 799 ↦ Fresh 883
      , "eSnd" ∋ Fresh 799 ↦ Fresh 884
      , "eFst" ∋ Fresh 800 ↦ Fresh 885
      , "eSnd" ∋ Fresh 800 ↦ Fresh 886
      , "eFst" ∋ Fresh 801 ↦ Fresh 887
      , "eSnd" ∋ Fresh 801 ↦ Fresh 888
      , "eFst" ∋ Fresh 802 ↦ Fresh 889
      , "eSnd" ∋ Fresh 802 ↦ Fresh 890
      , "eFst" ∋ Fresh 803 ↦ Fresh 891
      , "eSnd" ∋ Fresh 803 ↦ Fresh 892
      , "eFst" ∋ Fresh 804 ↦ Fresh 893
      , "eSnd" ∋ Fresh 804 ↦ Fresh 894
      , "eFst" ∋ Fresh 805 ↦ Fresh 895
      , "eSnd" ∋ Fresh 805 ↦ Fresh 896
      , "eFst" ∋ Fresh 806 ↦ Fresh 897
      , "eSnd" ∋ Fresh 806 ↦ Fresh 898
      , "eFst" ∋ Fresh 807 ↦ Fresh 899
      , "eSnd" ∋ Fresh 807 ↦ Fresh 900
      , "eFst" ∋ Fresh 808 ↦ Fresh 901
      , "eSnd" ∋ Fresh 808 ↦ Fresh 902
      , "eFst" ∋ Fresh 809 ↦ Fresh 903
      , "eSnd" ∋ Fresh 809 ↦ Fresh 904
      , "continuation" ∋ Fresh 810 ↦ Fresh 811
      , "recogniser" ∋ Fresh 810 ↦ "\"RULE\""
      , "recogniser" ∋ Fresh 811 ↦ "rule"
      , "continuation" ∋ Fresh 812 ↦ Fresh 813
      , "recogniser" ∋ Fresh 812 ↦ "eFst"
      , "continuation" ∋ Fresh 813 ↦ Fresh 814
      , "recogniser" ∋ Fresh 813 ↦ "\"|-\""
      , "recogniser" ∋ Fresh 814 ↦ "eSnd"
      , "continuation" ∋ Fresh 815 ↦ Fresh 816
      , "recogniser" ∋ Fresh 815 ↦ "\"(\""
      , "continuation" ∋ Fresh 816 ↦ Fresh 817
      , "recogniser" ∋ Fresh 816 ↦ "conjunct"
      , "recogniser" ∋ Fresh 817 ↦ "\")\""
      , "continuation" ∋ Fresh 818 ↦ Fresh 819
      , "recogniser" ∋ Fresh 818 ↦ "\"(\""
      , "continuation" ∋ Fresh 819 ↦ Fresh 820
      , "recogniser" ∋ Fresh 819 ↦ "compose"
      , "recogniser" ∋ Fresh 820 ↦ "\")\""
      , "continuation" ∋ Fresh 821 ↦ Fresh 822
      , "recogniser" ∋ Fresh 821 ↦ "converse"
      , "recogniser" ∋ Fresh 822 ↦ "\"~\""
      , "continuation" ∋ Fresh 823 ↦ Fresh 824
      , "recogniser" ∋ Fresh 823 ↦ "\"pre\""
      , "recogniser" ∋ Fresh 824 ↦ "pre"
      , "continuation" ∋ Fresh 825 ↦ Fresh 826
      , "recogniser" ∋ Fresh 825 ↦ "\"post\""
      , "recogniser" ∋ Fresh 826 ↦ "post"
      , "continuation" ∋ Fresh 827 ↦ Fresh 828
      , "recogniser" ∋ Fresh 827 ↦ "\"during\""
      , "recogniser" ∋ Fresh 828 ↦ "during"
      , "continuation" ∋ Fresh 829 ↦ Fresh 830
      , "recogniser" ∋ Fresh 829 ↦ "\"<\""
      , "continuation" ∋ Fresh 830 ↦ Fresh 831
      , "recogniser" ∋ Fresh 830 ↦ "pair1"
      , "continuation" ∋ Fresh 831 ↦ Fresh 832
      , "recogniser" ∋ Fresh 831 ↦ "\",\""
      , "continuation" ∋ Fresh 832 ↦ Fresh 833
      , "recogniser" ∋ Fresh 832 ↦ "pair2"
      , "recogniser" ∋ Fresh 833 ↦ "\">\""
      , "recogniser" ∋ Fresh 834 ↦ "\"I\""
      , "continuation" ∋ Fresh 835 ↦ Fresh 836
      , "recogniser" ∋ Fresh 835 ↦ "eFst"
      , "continuation" ∋ Fresh 836 ↦ Fresh 837
      , "recogniser" ∋ Fresh 836 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 837 ↦ "eSnd"
      , "continuation" ∋ Fresh 838 ↦ Fresh 839
      , "recogniser" ∋ Fresh 838 ↦ "eFst"
      , "continuation" ∋ Fresh 839 ↦ Fresh 840
      , "recogniser" ∋ Fresh 839 ↦ "\";\""
      , "recogniser" ∋ Fresh 840 ↦ "eSnd"
      , "post" ∋ Fresh 841 ↦ "origin"
      , "pre" ∋ Fresh 842 ↦ "origin"
      , "post" ∋ Fresh 843 ↦ "string"
      , "pre" ∋ Fresh 844 ↦ "string"
      , "pre" ∋ Fresh 845 ↦ "classification"
      , "post" ∋ Fresh 846 ↦ "classification"
      , "pre" ∋ Fresh 847 ↦ "mainConcept"
      , "post" ∋ Fresh 848 ↦ "mainConcept"
      , "pre" ∋ Fresh 849 ↦ "conceptList"
      , "post" ∋ Fresh 850 ↦ "conceptList"
      , "pre" ∋ Fresh 851 ↦ "head1"
      , "post" ∋ Fresh 852 ↦ "head1"
      , "pre" ∋ Fresh 853 ↦ "tail1"
      , "post" ∋ Fresh 854 ↦ "tail1"
      , "pre" ∋ Fresh 855 ↦ "declaration"
      , "post" ∋ Fresh 856 ↦ "declaration"
      , "pre" ∋ Fresh 857 ↦ "relation"
      , "post" ∋ Fresh 858 ↦ "relation"
      , "pre" ∋ Fresh 859 ↦ "concepts"
      , "post" ∋ Fresh 860 ↦ "concepts"
      , "pre" ∋ Fresh 861 ↦ "fst"
      , "post" ∋ Fresh 862 ↦ "fst"
      , "pre" ∋ Fresh 863 ↦ "snd"
      , "post" ∋ Fresh 864 ↦ "snd"
      , "pre" ∋ Fresh 865 ↦ "syntax"
      , "post" ∋ Fresh 866 ↦ "syntax"
      , "pre" ∋ Fresh 867 ↦ "concept"
      , "post" ∋ Fresh 868 ↦ "concept"
      , "pre" ∋ Fresh 869 ↦ "relationName"
      , "post" ∋ Fresh 870 ↦ "relationName"
      , "pre" ∋ Fresh 871 ↦ "syntaxList"
      , "post" ∋ Fresh 872 ↦ "syntaxList"
      , "pre" ∋ Fresh 873 ↦ "head2"
      , "post" ∋ Fresh 874 ↦ "head2"
      , "pre" ∋ Fresh 875 ↦ "tail2"
      , "post" ∋ Fresh 876 ↦ "tail2"
      , "pre" ∋ Fresh 877 ↦ "qstring"
      , "post" ∋ Fresh 878 ↦ "qstring"
      , "pre" ∋ Fresh 879 ↦ "Statement"
      , "post" ∋ Fresh 880 ↦ "Statement"
      , "pre" ∋ Fresh 881 ↦ "Start"
      , "post" ∋ Fresh 882 ↦ "Start"
      , "pre" ∋ Fresh 883 ↦ "rule"
      , "post" ∋ Fresh 884 ↦ "rule"
      , "pre" ∋ Fresh 885 ↦ "eFst"
      , "post" ∋ Fresh 886 ↦ "eFst"
      , "pre" ∋ Fresh 887 ↦ "eSnd"
      , "post" ∋ Fresh 888 ↦ "eSnd"
      , "pre" ∋ Fresh 889 ↦ "conjunct"
      , "post" ∋ Fresh 890 ↦ "conjunct"
      , "pre" ∋ Fresh 891 ↦ "converse"
      , "post" ∋ Fresh 892 ↦ "converse"
      , "pre" ∋ Fresh 893 ↦ "compose"
      , "post" ∋ Fresh 894 ↦ "compose"
      , "pre" ∋ Fresh 895 ↦ "pre"
      , "post" ∋ Fresh 896 ↦ "pre"
      , "pre" ∋ Fresh 897 ↦ "post"
      , "post" ∋ Fresh 898 ↦ "post"
      , "pre" ∋ Fresh 899 ↦ "during"
      , "post" ∋ Fresh 900 ↦ "during"
      , "pre" ∋ Fresh 901 ↦ "pair1"
      , "post" ∋ Fresh 902 ↦ "pair1"
      , "pre" ∋ Fresh 903 ↦ "pair2"
      , "post" ∋ Fresh 904 ↦ "pair2"
      ])
  ];}
