

source_type :: Compiler -> DataStructure
target_type :: Compiler -> DataStructure

CLASSIFY Compilation ISA Result
compiler :: Result -> Compiler
source :: Result -> Instance

target :: Compilation -> Instance
type :: Instance -> DataStructure


RULE source;type = compiler;source_type
RULE target;type = compiler;target_type

CLASSIFY Chain ISA Compiler
fst :: Chain -> Compiler
snd :: Chain -> Compiler

RULE source_type = fst;source_type
RULE target_type = snd;target_type
RULE snd;source_type = fst;target_type

CLASSIFY ChainedResult ISA Result
...
