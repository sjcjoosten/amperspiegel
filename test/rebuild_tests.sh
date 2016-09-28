#! /bin/bash
for f in *.test
do
  sh "$f" 1> "${f%.test}.result" 2> "${f%.test}.err"
done
