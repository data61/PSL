#!/bin/bash

echo 'start renaming'

FILES="Database_*"
for f in $FILES
do
  echo "$f"
  sort $f > sorted_$f
  mv sorted_$f $f
done

