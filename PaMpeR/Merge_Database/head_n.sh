#!/bin/bash

echo 'start renaming'

FILES="Database_*"
for f in $FILES
do
  echo "$f"
  head -n 150 $f > temp_$f
  mv temp_$f $f
done

