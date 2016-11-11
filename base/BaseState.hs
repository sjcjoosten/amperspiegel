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
      , "pair1" ∋ Fresh 278 ↦ "keepString"
      , "pair2" ∋ Fresh 278 ↦ "keepString"
      , "post" ∋ Fresh 279 ↦ "rule"
      , "Start" ∋ Fresh 280 ↦ Fresh 285
      , "Statement" ∋ Fresh 280 ↦ Fresh 281
      , "rule" ∋ Fresh 281 ↦ Fresh 282
      , "eFst" ∋ Fresh 282 ↦ Fresh 283
      , "eSnd" ∋ Fresh 282 ↦ Fresh 284
      , "pair1" ∋ Fresh 283 ↦ "keepOrigin"
      , "pair2" ∋ Fresh 283 ↦ "keepOrigin"
      , "post" ∋ Fresh 284 ↦ "rule"
      , "Start" ∋ Fresh 285 ↦ Fresh 293
      , "Statement" ∋ Fresh 285 ↦ Fresh 286
      , "rule" ∋ Fresh 286 ↦ Fresh 287
      , "eFst" ∋ Fresh 287 ↦ Fresh 288
      , "eSnd" ∋ Fresh 287 ↦ Fresh 289
      , "pair1" ∋ Fresh 288 ↦ "keepString"
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
      , "pair1" ∋ Fresh 296 ↦ "keepString"
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
      , "pair1" ∋ Fresh 304 ↦ "keepOrigin"
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
      , "pair1" ∋ Fresh 312 ↦ "keepOrigin"
      , "pair2" ∋ Fresh 312 ↦ "origin"
      , "compose" ∋ Fresh 313 ↦ Fresh 314
      , "eFst" ∋ Fresh 314 ↦ Fresh 315
      , "eSnd" ∋ Fresh 314 ↦ Fresh 316
      , "post" ∋ Fresh 315 ↦ "eSnd"
      , "post" ∋ Fresh 316 ↦ "post"
      , "Start" ∋ Fresh 317 ↦ Fresh 322
      , "Statement" ∋ Fresh 317 ↦ Fresh 318
      , "rule" ∋ Fresh 318 ↦ Fresh 319
      , "eFst" ∋ Fresh 319 ↦ Fresh 320
      , "eSnd" ∋ Fresh 319 ↦ Fresh 321
      , "pair1" ∋ Fresh 320 ↦ "Start"
      , "pair2" ∋ Fresh 320 ↦ "endOfFile"
      , "post" ∋ Fresh 321 ↦ "choice"
      , "Start" ∋ Fresh 322 ↦ Fresh 327
      , "Statement" ∋ Fresh 322 ↦ Fresh 323
      , "rule" ∋ Fresh 323 ↦ Fresh 324
      , "eFst" ∋ Fresh 324 ↦ Fresh 325
      , "eSnd" ∋ Fresh 324 ↦ Fresh 326
      , "pair1" ∋ Fresh 325 ↦ "Start"
      , "pair2" ∋ Fresh 325 ↦ "NextStatement"
      , "post" ∋ Fresh 326 ↦ "choice"
      , "Start" ∋ Fresh 327 ↦ Fresh 332
      , "Statement" ∋ Fresh 327 ↦ Fresh 328
      , "rule" ∋ Fresh 328 ↦ Fresh 329
      , "eFst" ∋ Fresh 329 ↦ Fresh 330
      , "eSnd" ∋ Fresh 329 ↦ Fresh 331
      , "pair1" ∋ Fresh 330 ↦ "NextStatement"
      , "pair2" ∋ Fresh 330 ↦ "Statement"
      , "post" ∋ Fresh 331 ↦ "recogniser"
      , "Start" ∋ Fresh 332 ↦ Fresh 337
      , "Statement" ∋ Fresh 332 ↦ Fresh 333
      , "rule" ∋ Fresh 333 ↦ Fresh 334
      , "eFst" ∋ Fresh 334 ↦ Fresh 335
      , "eSnd" ∋ Fresh 334 ↦ Fresh 336
      , "pair1" ∋ Fresh 335 ↦ "NextStatement"
      , "pair2" ∋ Fresh 335 ↦ "gotoStart"
      , "post" ∋ Fresh 336 ↦ "continuation"
      , "Start" ∋ Fresh 337 ↦ Fresh 342
      , "Statement" ∋ Fresh 337 ↦ Fresh 338
      , "rule" ∋ Fresh 338 ↦ Fresh 339
      , "eFst" ∋ Fresh 339 ↦ Fresh 340
      , "eSnd" ∋ Fresh 339 ↦ Fresh 341
      , "pair1" ∋ Fresh 340 ↦ "gotoStart"
      , "pair2" ∋ Fresh 340 ↦ "Start"
      , "post" ∋ Fresh 341 ↦ "recogniser"
      , "Start" ∋ Fresh 342 ↦ Fresh 347
      , "Statement" ∋ Fresh 342 ↦ Fresh 343
      , "rule" ∋ Fresh 343 ↦ Fresh 344
      , "eFst" ∋ Fresh 344 ↦ Fresh 345
      , "eSnd" ∋ Fresh 344 ↦ Fresh 346
      , "pair1" ∋ Fresh 345 ↦ "Start"
      , "pair2" ∋ Fresh 345 ↦ "Start"
      , "post" ∋ Fresh 346 ↦ "nonTerminal"
      , "Start" ∋ Fresh 347 ↦ Fresh 352
      , "Statement" ∋ Fresh 347 ↦ Fresh 348
      , "rule" ∋ Fresh 348 ↦ Fresh 349
      , "eFst" ∋ Fresh 349 ↦ Fresh 350
      , "eSnd" ∋ Fresh 349 ↦ Fresh 351
      , "pair1" ∋ Fresh 350 ↦ "Statement"
      , "pair2" ∋ Fresh 350 ↦ "Statement"
      , "post" ∋ Fresh 351 ↦ "nonTerminal"
      ])
  , ( "cfg"
    , [ "choice" ∋ "Choice" ↦ Fresh 845
      , "choice" ∋ "Continuation" ↦ Fresh 848
      , "choice" ∋ "Continuation" ↦ Fresh 850
      , "continuation" ∋ "NextStatement" ↦ "gotoStart"
      , "recogniser" ∋ "NextStatement" ↦ "Statement"
      , "nonTerminal" ∋ "QuotedString" ↦ "QuotedString"
      , "rule" ∋ "QuotedString" ↦ Fresh 841
      , "choice" ∋ "Recogniser" ↦ Fresh 851
      , "choice" ∋ "Recogniser" ↦ Fresh 852
      , "choice" ∋ "Start" ↦ "NextStatement"
      , "choice" ∋ "Start" ↦ "endOfFile"
      , "choice" ∋ "Start" ↦ Fresh 842
      , "choice" ∋ "Start" ↦ Fresh 844
      , "nonTerminal" ∋ "Start" ↦ "Start"
      , "nonTerminal" ∋ "Statement" ↦ "Statement"
      , "nonTerminal" ∋ "UnquotedString" ↦ "UnquotedString"
      , "rule" ∋ "UnquotedString" ↦ Fresh 840
      , "nonTerminal" ∋ "choice" ↦ "Continuation"
      , "rule" ∋ "choice" ↦ Fresh 836
      , "nonTerminal" ∋ "continuation" ↦ "Continuation"
      , "rule" ∋ "continuation" ↦ Fresh 837
      , "recogniser" ∋ "gotoStart" ↦ "Start"
      , "eFst" ∋ "keepOrigin" ↦ Fresh 866
      , "eSnd" ∋ "keepOrigin" ↦ Fresh 865
      , "rule" ∋ "keepOrigin" ↦ "keepOrigin"
      , "eFst" ∋ "keepString" ↦ Fresh 868
      , "eSnd" ∋ "keepString" ↦ Fresh 867
      , "rule" ∋ "keepString" ↦ "keepString"
      , "nonTerminal" ∋ "more" ↦ "Start"
      , "rule" ∋ "more" ↦ Fresh 835
      , "nonTerminal" ∋ "nonTerminal" ↦ "UnquotedString"
      , "rule" ∋ "nonTerminal" ↦ Fresh 839
      , "nonTerminal" ∋ "recogniser" ↦ "Recogniser"
      , "rule" ∋ "recogniser" ↦ Fresh 838
      , "nonTerminal" ∋ "start" ↦ "Choice"
      , "rule" ∋ "start" ↦ Fresh 834
      , "eFst" ∋ Fresh 834 ↦ Fresh 869
      , "eSnd" ∋ Fresh 834 ↦ Fresh 870
      , "eFst" ∋ Fresh 835 ↦ Fresh 871
      , "eSnd" ∋ Fresh 835 ↦ Fresh 872
      , "eFst" ∋ Fresh 836 ↦ Fresh 873
      , "eSnd" ∋ Fresh 836 ↦ Fresh 874
      , "eFst" ∋ Fresh 837 ↦ Fresh 875
      , "eSnd" ∋ Fresh 837 ↦ Fresh 876
      , "eFst" ∋ Fresh 838 ↦ Fresh 877
      , "eSnd" ∋ Fresh 838 ↦ Fresh 878
      , "eFst" ∋ Fresh 839 ↦ Fresh 863
      , "eSnd" ∋ Fresh 839 ↦ Fresh 879
      , "eFst" ∋ Fresh 840 ↦ Fresh 855
      , "eSnd" ∋ Fresh 840 ↦ Fresh 880
      , "eFst" ∋ Fresh 841 ↦ Fresh 859
      , "eSnd" ∋ Fresh 841 ↦ Fresh 881
      , "continuation" ∋ Fresh 842 ↦ Fresh 843
      , "recogniser" ∋ Fresh 842 ↦ "more"
      , "recogniser" ∋ Fresh 843 ↦ "start"
      , "continuation" ∋ Fresh 845 ↦ Fresh 846
      , "recogniser" ∋ Fresh 845 ↦ "UnquotedString"
      , "continuation" ∋ Fresh 846 ↦ Fresh 847
      , "recogniser" ∋ Fresh 846 ↦ "\">\""
      , "recogniser" ∋ Fresh 847 ↦ "choice"
      , "continuation" ∋ Fresh 848 ↦ Fresh 849
      , "recogniser" ∋ Fresh 848 ↦ "recogniser"
      , "recogniser" ∋ Fresh 849 ↦ "continuation"
      , "recogniser" ∋ Fresh 851 ↦ "QuotedString"
      , "recogniser" ∋ Fresh 852 ↦ "nonTerminal"
      , "rule" ∋ Fresh 853 ↦ Fresh 854
      , "eFst" ∋ Fresh 854 ↦ Fresh 855
      , "eSnd" ∋ Fresh 854 ↦ Fresh 856
      , "pre" ∋ Fresh 855 ↦ "UnquotedString"
      , "rule" ∋ Fresh 857 ↦ Fresh 858
      , "eFst" ∋ Fresh 858 ↦ Fresh 859
      , "eSnd" ∋ Fresh 858 ↦ Fresh 860
      , "pre" ∋ Fresh 859 ↦ "QuotedString"
      , "rule" ∋ Fresh 861 ↦ Fresh 862
      , "eFst" ∋ Fresh 862 ↦ Fresh 863
      , "eSnd" ∋ Fresh 862 ↦ Fresh 864
      , "pre" ∋ Fresh 863 ↦ "nonTerminal"
      , "post" ∋ Fresh 865 ↦ "origin"
      , "pre" ∋ Fresh 866 ↦ "origin"
      , "post" ∋ Fresh 867 ↦ "string"
      , "pre" ∋ Fresh 868 ↦ "string"
      , "pre" ∋ Fresh 869 ↦ "start"
      , "post" ∋ Fresh 870 ↦ "start"
      , "pre" ∋ Fresh 871 ↦ "more"
      , "post" ∋ Fresh 872 ↦ "more"
      , "pre" ∋ Fresh 873 ↦ "choice"
      , "post" ∋ Fresh 874 ↦ "choice"
      , "pre" ∋ Fresh 875 ↦ "continuation"
      , "post" ∋ Fresh 876 ↦ "continuation"
      , "pre" ∋ Fresh 877 ↦ "recogniser"
      , "post" ∋ Fresh 878 ↦ "recogniser"
      , "post" ∋ Fresh 879 ↦ "nonTerminal"
      , "post" ∋ Fresh 880 ↦ "UnquotedString"
      , "post" ∋ Fresh 881 ↦ "QuotedString"
      ])
  , ( "parser"
    , [ "choice" ∋ "Classification" ↦ Fresh 996
      , "choice" ∋ "ClassificationStatement" ↦ Fresh 993
      , "choice" ∋ "Compose" ↦ Fresh 1066
      , "choice" ∋ "ConceptList" ↦ Fresh 1000
      , "choice" ∋ "ConceptList" ↦ Fresh 1003
      , "choice" ∋ "Conjunct" ↦ Fresh 1063
      , "choice" ∋ "ConsConceptList" ↦ Fresh 1000
      , "choice" ∋ "ConsSyntaxList" ↦ Fresh 1021
      , "choice" ∋ "Declaration" ↦ Fresh 1007
      , "choice" ∋ "DeclarationStatement" ↦ Fresh 994
      , "choice" ∋ "DeclarationType" ↦ Fresh 1004
      , "choice" ∋ "EmptySyntax" ↦ Fresh 1016
      , "choice" ∋ "Expression" ↦ Fresh 1043
      , "choice" ∋ "Expression" ↦ Fresh 1046
      , "choice" ∋ "Expression" ↦ Fresh 1049
      , "choice" ∋ "Expression" ↦ Fresh 1051
      , "choice" ∋ "Expression" ↦ Fresh 1053
      , "choice" ∋ "Expression" ↦ Fresh 1055
      , "choice" ∋ "Expression" ↦ Fresh 1057
      , "choice" ∋ "Expression" ↦ Fresh 1062
      , "choice" ∋ "QuotedStringElement" ↦ Fresh 1025
      , "choice" ∋ "RelationElement" ↦ Fresh 1026
      , "choice" ∋ "RuleStatement" ↦ Fresh 1038
      , "choice" ∋ "RuleSubset" ↦ Fresh 1040
      , "choice" ∋ "Start" ↦ Fresh 1071
      , "choice" ∋ "Start" ↦ Fresh 1073
      , "nonTerminal" ∋ "Start" ↦ "Start"
      , "rule" ∋ "Start" ↦ Fresh 1070
      , "choice" ∋ "Statement" ↦ Fresh 993
      , "choice" ∋ "Statement" ↦ Fresh 994
      , "choice" ∋ "Statement" ↦ Fresh 995
      , "choice" ∋ "Statement" ↦ Fresh 1038
      , "nonTerminal" ∋ "Statement" ↦ "Statement"
      , "rule" ∋ "Statement" ↦ Fresh 1069
      , "choice" ∋ "Syntax" ↦ Fresh 1010
      , "choice" ∋ "Syntax" ↦ Fresh 1016
      , "choice" ∋ "SyntaxElement" ↦ Fresh 1025
      , "choice" ∋ "SyntaxElement" ↦ Fresh 1026
      , "choice" ∋ "SyntaxList" ↦ Fresh 1021
      , "choice" ∋ "SyntaxList" ↦ Fresh 1024
      , "choice" ∋ "SyntaxStatement" ↦ Fresh 995
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 1040
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 1063
      , "choice" ∋ "TwoExpressionArguments" ↦ Fresh 1066
      , "nonTerminal" ∋ "classification" ↦ "Classification"
      , "rule" ∋ "classification" ↦ Fresh 976
      , "nonTerminal" ∋ "compose" ↦ "Compose"
      , "rule" ∋ "compose" ↦ Fresh 1032
      , "nonTerminal" ∋ "concept" ↦ "String"
      , "rule" ∋ "concept" ↦ Fresh 987
      , "nonTerminal" ∋ "conceptList" ↦ "ConceptList"
      , "rule" ∋ "conceptList" ↦ Fresh 978
      , "nonTerminal" ∋ "concepts" ↦ "DeclarationType"
      , "rule" ∋ "concepts" ↦ Fresh 983
      , "nonTerminal" ∋ "conjunct" ↦ "Conjunct"
      , "rule" ∋ "conjunct" ↦ Fresh 1030
      , "nonTerminal" ∋ "converse" ↦ "Expression"
      , "rule" ∋ "converse" ↦ Fresh 1031
      , "nonTerminal" ∋ "declaration" ↦ "Declaration"
      , "rule" ∋ "declaration" ↦ Fresh 981
      , "nonTerminal" ∋ "during" ↦ "UnquotedString"
      , "rule" ∋ "during" ↦ Fresh 1035
      , "nonTerminal" ∋ "eFst" ↦ "Expression"
      , "rule" ∋ "eFst" ↦ Fresh 1028
      , "nonTerminal" ∋ "eSnd" ↦ "Expression"
      , "rule" ∋ "eSnd" ↦ Fresh 1029
      , "nonTerminal" ∋ "fst" ↦ "String"
      , "rule" ∋ "fst" ↦ Fresh 984
      , "nonTerminal" ∋ "head1" ↦ "String"
      , "rule" ∋ "head1" ↦ Fresh 979
      , "nonTerminal" ∋ "head2" ↦ "SyntaxElement"
      , "rule" ∋ "head2" ↦ Fresh 990
      , "nonTerminal" ∋ "mainConcept" ↦ "String"
      , "rule" ∋ "mainConcept" ↦ Fresh 977
      , "nonTerminal" ∋ "pair1" ↦ "String"
      , "rule" ∋ "pair1" ↦ Fresh 1036
      , "nonTerminal" ∋ "pair2" ↦ "String"
      , "rule" ∋ "pair2" ↦ Fresh 1037
      , "nonTerminal" ∋ "post" ↦ "UnquotedString"
      , "rule" ∋ "post" ↦ Fresh 1034
      , "nonTerminal" ∋ "pre" ↦ "UnquotedString"
      , "rule" ∋ "pre" ↦ Fresh 1033
      , "nonTerminal" ∋ "qstring" ↦ "QuotedString"
      , "rule" ∋ "qstring" ↦ Fresh 992
      , "eFst" ∋ "r1" ↦ Fresh 1077
      , "eSnd" ∋ "r1" ↦ Fresh 1076
      , "rule" ∋ "r1" ↦ "r1"
      , "eFst" ∋ "r2" ↦ Fresh 1075
      , "eSnd" ∋ "r2" ↦ Fresh 1074
      , "rule" ∋ "r2" ↦ "r2"
      , "nonTerminal" ∋ "relation" ↦ "StringAndOrigin"
      , "rule" ∋ "relation" ↦ Fresh 982
      , "nonTerminal" ∋ "relationName" ↦ "UnquotedString"
      , "rule" ∋ "relationName" ↦ Fresh 988
      , "nonTerminal" ∋ "rule" ↦ "RuleSubset"
      , "rule" ∋ "rule" ↦ Fresh 1027
      , "nonTerminal" ∋ "snd" ↦ "String"
      , "rule" ∋ "snd" ↦ Fresh 985
      , "nonTerminal" ∋ "syntax" ↦ "Syntax"
      , "rule" ∋ "syntax" ↦ Fresh 986
      , "nonTerminal" ∋ "syntaxList" ↦ "SyntaxList"
      , "rule" ∋ "syntaxList" ↦ Fresh 989
      , "nonTerminal" ∋ "tail1" ↦ "ConceptList"
      , "rule" ∋ "tail1" ↦ Fresh 980
      , "nonTerminal" ∋ "tail2" ↦ "SyntaxList"
      , "rule" ∋ "tail2" ↦ Fresh 991
      , "eFst" ∋ Fresh 976 ↦ Fresh 1078
      , "eSnd" ∋ Fresh 976 ↦ Fresh 1079
      , "eFst" ∋ Fresh 977 ↦ Fresh 1080
      , "eSnd" ∋ Fresh 977 ↦ Fresh 1081
      , "eFst" ∋ Fresh 978 ↦ Fresh 1082
      , "eSnd" ∋ Fresh 978 ↦ Fresh 1083
      , "eFst" ∋ Fresh 979 ↦ Fresh 1084
      , "eSnd" ∋ Fresh 979 ↦ Fresh 1085
      , "eFst" ∋ Fresh 980 ↦ Fresh 1086
      , "eSnd" ∋ Fresh 980 ↦ Fresh 1087
      , "eFst" ∋ Fresh 981 ↦ Fresh 1088
      , "eSnd" ∋ Fresh 981 ↦ Fresh 1089
      , "eFst" ∋ Fresh 982 ↦ Fresh 1090
      , "eSnd" ∋ Fresh 982 ↦ Fresh 1091
      , "eFst" ∋ Fresh 983 ↦ Fresh 1092
      , "eSnd" ∋ Fresh 983 ↦ Fresh 1093
      , "eFst" ∋ Fresh 984 ↦ Fresh 1094
      , "eSnd" ∋ Fresh 984 ↦ Fresh 1095
      , "eFst" ∋ Fresh 985 ↦ Fresh 1096
      , "eSnd" ∋ Fresh 985 ↦ Fresh 1097
      , "eFst" ∋ Fresh 986 ↦ Fresh 1098
      , "eSnd" ∋ Fresh 986 ↦ Fresh 1099
      , "eFst" ∋ Fresh 987 ↦ Fresh 1100
      , "eSnd" ∋ Fresh 987 ↦ Fresh 1101
      , "eFst" ∋ Fresh 988 ↦ Fresh 1102
      , "eSnd" ∋ Fresh 988 ↦ Fresh 1103
      , "eFst" ∋ Fresh 989 ↦ Fresh 1104
      , "eSnd" ∋ Fresh 989 ↦ Fresh 1105
      , "eFst" ∋ Fresh 990 ↦ Fresh 1106
      , "eSnd" ∋ Fresh 990 ↦ Fresh 1107
      , "eFst" ∋ Fresh 991 ↦ Fresh 1108
      , "eSnd" ∋ Fresh 991 ↦ Fresh 1109
      , "eFst" ∋ Fresh 992 ↦ Fresh 1110
      , "eSnd" ∋ Fresh 992 ↦ Fresh 1111
      , "recogniser" ∋ Fresh 993 ↦ "classification"
      , "recogniser" ∋ Fresh 994 ↦ "declaration"
      , "recogniser" ∋ Fresh 995 ↦ "syntax"
      , "continuation" ∋ Fresh 996 ↦ Fresh 997
      , "recogniser" ∋ Fresh 996 ↦ "\"CLASSIFY\""
      , "continuation" ∋ Fresh 997 ↦ Fresh 998
      , "recogniser" ∋ Fresh 997 ↦ "mainConcept"
      , "continuation" ∋ Fresh 998 ↦ Fresh 999
      , "recogniser" ∋ Fresh 998 ↦ "\"IS\""
      , "recogniser" ∋ Fresh 999 ↦ "conceptList"
      , "continuation" ∋ Fresh 1000 ↦ Fresh 1001
      , "recogniser" ∋ Fresh 1000 ↦ "head1"
      , "continuation" ∋ Fresh 1001 ↦ Fresh 1002
      , "recogniser" ∋ Fresh 1001 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 1002 ↦ "tail1"
      , "recogniser" ∋ Fresh 1003 ↦ "head1"
      , "continuation" ∋ Fresh 1004 ↦ Fresh 1005
      , "recogniser" ∋ Fresh 1004 ↦ "fst"
      , "continuation" ∋ Fresh 1005 ↦ Fresh 1006
      , "recogniser" ∋ Fresh 1005 ↦ "\"*\""
      , "recogniser" ∋ Fresh 1006 ↦ "snd"
      , "continuation" ∋ Fresh 1007 ↦ Fresh 1008
      , "recogniser" ∋ Fresh 1007 ↦ "relation"
      , "continuation" ∋ Fresh 1008 ↦ Fresh 1009
      , "recogniser" ∋ Fresh 1008 ↦ "\"::\""
      , "recogniser" ∋ Fresh 1009 ↦ "concepts"
      , "continuation" ∋ Fresh 1010 ↦ Fresh 1011
      , "recogniser" ∋ Fresh 1010 ↦ "\"VIEW\""
      , "continuation" ∋ Fresh 1011 ↦ Fresh 1012
      , "recogniser" ∋ Fresh 1011 ↦ "concept"
      , "continuation" ∋ Fresh 1012 ↦ Fresh 1013
      , "recogniser" ∋ Fresh 1012 ↦ "\"=\""
      , "continuation" ∋ Fresh 1013 ↦ Fresh 1014
      , "recogniser" ∋ Fresh 1013 ↦ "\"[\""
      , "continuation" ∋ Fresh 1014 ↦ Fresh 1015
      , "recogniser" ∋ Fresh 1014 ↦ "syntaxList"
      , "recogniser" ∋ Fresh 1015 ↦ "\"]\""
      , "continuation" ∋ Fresh 1016 ↦ Fresh 1017
      , "recogniser" ∋ Fresh 1016 ↦ "\"VIEW\""
      , "continuation" ∋ Fresh 1017 ↦ Fresh 1018
      , "recogniser" ∋ Fresh 1017 ↦ "concept"
      , "continuation" ∋ Fresh 1018 ↦ Fresh 1019
      , "recogniser" ∋ Fresh 1018 ↦ "\"=\""
      , "continuation" ∋ Fresh 1019 ↦ Fresh 1020
      , "recogniser" ∋ Fresh 1019 ↦ "\"[\""
      , "recogniser" ∋ Fresh 1020 ↦ "\"]\""
      , "continuation" ∋ Fresh 1021 ↦ Fresh 1022
      , "recogniser" ∋ Fresh 1021 ↦ "head2"
      , "continuation" ∋ Fresh 1022 ↦ Fresh 1023
      , "recogniser" ∋ Fresh 1022 ↦ "\",\""
      , "recogniser" ∋ Fresh 1023 ↦ "tail2"
      , "recogniser" ∋ Fresh 1024 ↦ "head2"
      , "recogniser" ∋ Fresh 1025 ↦ "qstring"
      , "recogniser" ∋ Fresh 1026 ↦ "relationName"
      , "eFst" ∋ Fresh 1027 ↦ Fresh 1112
      , "eSnd" ∋ Fresh 1027 ↦ Fresh 1113
      , "eFst" ∋ Fresh 1028 ↦ Fresh 1114
      , "eSnd" ∋ Fresh 1028 ↦ Fresh 1115
      , "eFst" ∋ Fresh 1029 ↦ Fresh 1116
      , "eSnd" ∋ Fresh 1029 ↦ Fresh 1117
      , "eFst" ∋ Fresh 1030 ↦ Fresh 1118
      , "eSnd" ∋ Fresh 1030 ↦ Fresh 1119
      , "eFst" ∋ Fresh 1031 ↦ Fresh 1120
      , "eSnd" ∋ Fresh 1031 ↦ Fresh 1121
      , "eFst" ∋ Fresh 1032 ↦ Fresh 1122
      , "eSnd" ∋ Fresh 1032 ↦ Fresh 1123
      , "eFst" ∋ Fresh 1033 ↦ Fresh 1124
      , "eSnd" ∋ Fresh 1033 ↦ Fresh 1125
      , "eFst" ∋ Fresh 1034 ↦ Fresh 1126
      , "eSnd" ∋ Fresh 1034 ↦ Fresh 1127
      , "eFst" ∋ Fresh 1035 ↦ Fresh 1128
      , "eSnd" ∋ Fresh 1035 ↦ Fresh 1129
      , "eFst" ∋ Fresh 1036 ↦ Fresh 1130
      , "eSnd" ∋ Fresh 1036 ↦ Fresh 1131
      , "eFst" ∋ Fresh 1037 ↦ Fresh 1132
      , "eSnd" ∋ Fresh 1037 ↦ Fresh 1133
      , "continuation" ∋ Fresh 1038 ↦ Fresh 1039
      , "recogniser" ∋ Fresh 1038 ↦ "\"RULE\""
      , "recogniser" ∋ Fresh 1039 ↦ "rule"
      , "continuation" ∋ Fresh 1040 ↦ Fresh 1041
      , "recogniser" ∋ Fresh 1040 ↦ "eFst"
      , "continuation" ∋ Fresh 1041 ↦ Fresh 1042
      , "recogniser" ∋ Fresh 1041 ↦ "\"|-\""
      , "recogniser" ∋ Fresh 1042 ↦ "eSnd"
      , "continuation" ∋ Fresh 1043 ↦ Fresh 1044
      , "recogniser" ∋ Fresh 1043 ↦ "\"(\""
      , "continuation" ∋ Fresh 1044 ↦ Fresh 1045
      , "recogniser" ∋ Fresh 1044 ↦ "conjunct"
      , "recogniser" ∋ Fresh 1045 ↦ "\")\""
      , "continuation" ∋ Fresh 1046 ↦ Fresh 1047
      , "recogniser" ∋ Fresh 1046 ↦ "\"(\""
      , "continuation" ∋ Fresh 1047 ↦ Fresh 1048
      , "recogniser" ∋ Fresh 1047 ↦ "compose"
      , "recogniser" ∋ Fresh 1048 ↦ "\")\""
      , "continuation" ∋ Fresh 1049 ↦ Fresh 1050
      , "recogniser" ∋ Fresh 1049 ↦ "converse"
      , "recogniser" ∋ Fresh 1050 ↦ "\"~\""
      , "continuation" ∋ Fresh 1051 ↦ Fresh 1052
      , "recogniser" ∋ Fresh 1051 ↦ "\"pre\""
      , "recogniser" ∋ Fresh 1052 ↦ "pre"
      , "continuation" ∋ Fresh 1053 ↦ Fresh 1054
      , "recogniser" ∋ Fresh 1053 ↦ "\"post\""
      , "recogniser" ∋ Fresh 1054 ↦ "post"
      , "continuation" ∋ Fresh 1055 ↦ Fresh 1056
      , "recogniser" ∋ Fresh 1055 ↦ "\"during\""
      , "recogniser" ∋ Fresh 1056 ↦ "during"
      , "continuation" ∋ Fresh 1057 ↦ Fresh 1058
      , "recogniser" ∋ Fresh 1057 ↦ "\"<\""
      , "continuation" ∋ Fresh 1058 ↦ Fresh 1059
      , "recogniser" ∋ Fresh 1058 ↦ "pair1"
      , "continuation" ∋ Fresh 1059 ↦ Fresh 1060
      , "recogniser" ∋ Fresh 1059 ↦ "\",\""
      , "continuation" ∋ Fresh 1060 ↦ Fresh 1061
      , "recogniser" ∋ Fresh 1060 ↦ "pair2"
      , "recogniser" ∋ Fresh 1061 ↦ "\">\""
      , "recogniser" ∋ Fresh 1062 ↦ "\"I\""
      , "continuation" ∋ Fresh 1063 ↦ Fresh 1064
      , "recogniser" ∋ Fresh 1063 ↦ "eFst"
      , "continuation" ∋ Fresh 1064 ↦ Fresh 1065
      , "recogniser" ∋ Fresh 1064 ↦ "\"/\\\\\""
      , "recogniser" ∋ Fresh 1065 ↦ "eSnd"
      , "continuation" ∋ Fresh 1066 ↦ Fresh 1067
      , "recogniser" ∋ Fresh 1066 ↦ "eFst"
      , "continuation" ∋ Fresh 1067 ↦ Fresh 1068
      , "recogniser" ∋ Fresh 1067 ↦ "\";\""
      , "recogniser" ∋ Fresh 1068 ↦ "eSnd"
      , "eFst" ∋ Fresh 1069 ↦ Fresh 1134
      , "eSnd" ∋ Fresh 1069 ↦ Fresh 1135
      , "eFst" ∋ Fresh 1070 ↦ Fresh 1136
      , "eSnd" ∋ Fresh 1070 ↦ Fresh 1137
      , "continuation" ∋ Fresh 1071 ↦ Fresh 1072
      , "recogniser" ∋ Fresh 1071 ↦ "Statement"
      , "recogniser" ∋ Fresh 1072 ↦ "Start"
      , "post" ∋ Fresh 1074 ↦ "origin"
      , "pre" ∋ Fresh 1075 ↦ "origin"
      , "post" ∋ Fresh 1076 ↦ "string"
      , "pre" ∋ Fresh 1077 ↦ "string"
      , "pre" ∋ Fresh 1078 ↦ "classification"
      , "post" ∋ Fresh 1079 ↦ "classification"
      , "pre" ∋ Fresh 1080 ↦ "mainConcept"
      , "post" ∋ Fresh 1081 ↦ "mainConcept"
      , "pre" ∋ Fresh 1082 ↦ "conceptList"
      , "post" ∋ Fresh 1083 ↦ "conceptList"
      , "pre" ∋ Fresh 1084 ↦ "head1"
      , "post" ∋ Fresh 1085 ↦ "head1"
      , "pre" ∋ Fresh 1086 ↦ "tail1"
      , "post" ∋ Fresh 1087 ↦ "tail1"
      , "pre" ∋ Fresh 1088 ↦ "declaration"
      , "post" ∋ Fresh 1089 ↦ "declaration"
      , "pre" ∋ Fresh 1090 ↦ "relation"
      , "post" ∋ Fresh 1091 ↦ "relation"
      , "pre" ∋ Fresh 1092 ↦ "concepts"
      , "post" ∋ Fresh 1093 ↦ "concepts"
      , "pre" ∋ Fresh 1094 ↦ "fst"
      , "post" ∋ Fresh 1095 ↦ "fst"
      , "pre" ∋ Fresh 1096 ↦ "snd"
      , "post" ∋ Fresh 1097 ↦ "snd"
      , "pre" ∋ Fresh 1098 ↦ "syntax"
      , "post" ∋ Fresh 1099 ↦ "syntax"
      , "pre" ∋ Fresh 1100 ↦ "concept"
      , "post" ∋ Fresh 1101 ↦ "concept"
      , "pre" ∋ Fresh 1102 ↦ "relationName"
      , "post" ∋ Fresh 1103 ↦ "relationName"
      , "pre" ∋ Fresh 1104 ↦ "syntaxList"
      , "post" ∋ Fresh 1105 ↦ "syntaxList"
      , "pre" ∋ Fresh 1106 ↦ "head2"
      , "post" ∋ Fresh 1107 ↦ "head2"
      , "pre" ∋ Fresh 1108 ↦ "tail2"
      , "post" ∋ Fresh 1109 ↦ "tail2"
      , "pre" ∋ Fresh 1110 ↦ "qstring"
      , "post" ∋ Fresh 1111 ↦ "qstring"
      , "pre" ∋ Fresh 1112 ↦ "rule"
      , "post" ∋ Fresh 1113 ↦ "rule"
      , "pre" ∋ Fresh 1114 ↦ "eFst"
      , "post" ∋ Fresh 1115 ↦ "eFst"
      , "pre" ∋ Fresh 1116 ↦ "eSnd"
      , "post" ∋ Fresh 1117 ↦ "eSnd"
      , "pre" ∋ Fresh 1118 ↦ "conjunct"
      , "post" ∋ Fresh 1119 ↦ "conjunct"
      , "pre" ∋ Fresh 1120 ↦ "converse"
      , "post" ∋ Fresh 1121 ↦ "converse"
      , "pre" ∋ Fresh 1122 ↦ "compose"
      , "post" ∋ Fresh 1123 ↦ "compose"
      , "pre" ∋ Fresh 1124 ↦ "pre"
      , "post" ∋ Fresh 1125 ↦ "pre"
      , "pre" ∋ Fresh 1126 ↦ "post"
      , "post" ∋ Fresh 1127 ↦ "post"
      , "pre" ∋ Fresh 1128 ↦ "during"
      , "post" ∋ Fresh 1129 ↦ "during"
      , "pre" ∋ Fresh 1130 ↦ "pair1"
      , "post" ∋ Fresh 1131 ↦ "pair1"
      , "pre" ∋ Fresh 1132 ↦ "pair2"
      , "post" ∋ Fresh 1133 ↦ "pair2"
      , "pre" ∋ Fresh 1134 ↦ "Statement"
      , "post" ∋ Fresh 1135 ↦ "Statement"
      , "pre" ∋ Fresh 1136 ↦ "Start"
      , "post" ∋ Fresh 1137 ↦ "Start"
      ])
  , ( "switches"
    , [ "cur" ∋ Fresh 1475 ↦ Fresh 1475
      , "first" ∋ Fresh 1475 ↦ Fresh 1485
      , "next" ∋ Fresh 1475 ↦ Fresh 1476
      , "string" ∋ Fresh 1475 ↦ "\"i\""
      , "next" ∋ Fresh 1476 ↦ Fresh 1477
      , "string" ∋ Fresh 1476 ↦ "\"asParser\""
      , "first" ∋ Fresh 1477 ↦ Fresh 1486
      , "next" ∋ Fresh 1477 ↦ Fresh 1478
      , "string" ∋ Fresh 1477 ↦ "\"i\""
      , "first" ∋ Fresh 1478 ↦ Fresh 1487
      , "next" ∋ Fresh 1478 ↦ Fresh 1479
      , "string" ∋ Fresh 1478 ↦ "\"apply\""
      , "first" ∋ Fresh 1479 ↦ Fresh 1490
      , "next" ∋ Fresh 1479 ↦ Fresh 1480
      , "string" ∋ Fresh 1479 ↦ "\"i\""
      , "first" ∋ Fresh 1480 ↦ Fresh 1491
      , "next" ∋ Fresh 1480 ↦ Fresh 1481
      , "string" ∋ Fresh 1480 ↦ "\"apply\""
      , "first" ∋ Fresh 1481 ↦ Fresh 1494
      , "next" ∋ Fresh 1481 ↦ Fresh 1482
      , "string" ∋ Fresh 1481 ↦ "\"apply\""
      , "first" ∋ Fresh 1482 ↦ Fresh 1496
      , "next" ∋ Fresh 1482 ↦ Fresh 1483
      , "string" ∋ Fresh 1482 ↦ "\"apply\""
      , "first" ∋ Fresh 1483 ↦ Fresh 1498
      , "next" ∋ Fresh 1483 ↦ Fresh 1484
      , "string" ∋ Fresh 1483 ↦ "\"collect\""
      , "first" ∋ Fresh 1484 ↦ Fresh 1499
      , "string" ∋ Fresh 1484 ↦ "\"showTS\""
      , "string" ∋ Fresh 1485 ↦ "\"boot.ASL\""
      , "string" ∋ Fresh 1486 ↦ "\"asParser.ASL\""
      , "next" ∋ Fresh 1487 ↦ Fresh 1488
      , "string" ∋ Fresh 1487 ↦ "\"parser\""
      , "next" ∋ Fresh 1488 ↦ Fresh 1489
      , "string" ∋ Fresh 1488 ↦ "\"population\""
      , "string" ∋ Fresh 1489 ↦ "\"asParser\""
      , "string" ∋ Fresh 1490 ↦ "\"cfg.ASL\""
      , "next" ∋ Fresh 1491 ↦ Fresh 1492
      , "string" ∋ Fresh 1491 ↦ "\"asParser\""
      , "next" ∋ Fresh 1492 ↦ Fresh 1493
      , "string" ∋ Fresh 1492 ↦ "\"population\""
      , "string" ∋ Fresh 1493 ↦ "\"cfg\""
      , "next" ∋ Fresh 1494 ↦ Fresh 1495
      , "string" ∋ Fresh 1494 ↦ "\"del\""
      , "string" ∋ Fresh 1495 ↦ "\"switches\""
      , "next" ∋ Fresh 1496 ↦ Fresh 1497
      , "string" ∋ Fresh 1496 ↦ "\"del\""
      , "string" ∋ Fresh 1497 ↦ "\"population\""
      , "string" ∋ Fresh 1498 ↦ "\"state\""
      , "string" ∋ Fresh 1499 ↦ "\"state\""
      ])
  ];}
