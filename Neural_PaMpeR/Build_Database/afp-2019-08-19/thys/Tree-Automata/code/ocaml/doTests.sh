#!/bin/sh
echo "[OCaml] Compiling" &&
  ./make.sh &&
  echo "[OCaml]! Running test cases" &&
  time ./Main

