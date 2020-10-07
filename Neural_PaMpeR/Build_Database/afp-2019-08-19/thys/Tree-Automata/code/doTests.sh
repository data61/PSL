#!/bin/bash

DIR=$PWD
LOG="/tmp/ta_tests.log"

function display_stats {
  egrep "(^(real|user|sys))|(^(\\[[^,]+\\]\\!.+))" $LOG
}

date > $LOG

echo "ML"
cd $DIR/ml && ./doTests.sh 1>>$LOG 2>>$LOG
display_stats

echo "OCaml"
cd $DIR/ocaml && ./doTests.sh 1>>$LOG 2>>$LOG
display_stats

echo "Haskell"
cd $DIR/haskell && ./doTests.sh 1>>$LOG 2>>$LOG
display_stats

