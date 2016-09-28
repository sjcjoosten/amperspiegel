#! /bin/bash

rc=0
for f in *.test
do
  echo "$f"
  (sh "$f" | diff -y --suppress-common-lines - "${f%.test}.result") 2>&1 | diff -y -c - "${f%.test}.err"
  rcs=${PIPESTATUS[*]}
  for i in ${rcs}
    do rc=$(($i > $rc ? $i : $rc))
  done
done

exit $rc