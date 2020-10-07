#!/bin/sh
echo "[Haskell] Compiling"
if ./make.sh; then
  echo "[Haskell]! Test cases with top-down reduction product algorithm"
  time -p ./Main 2>&1
  echo "[Haskell]! Test cases with brute-force product algorithm without reduction"
  time -p ./Main -wr
else
  echo "[Haskell]! Error"
fi
