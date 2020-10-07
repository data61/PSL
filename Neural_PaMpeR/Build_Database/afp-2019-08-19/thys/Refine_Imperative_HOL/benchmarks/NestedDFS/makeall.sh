#!/bin/bash

echo "Compiling C++ NDFS"
cd "c++"
g++ -O3 dfs.c -o dfsO3
g++ -O0 dfs.c -o dfsO0
cd ..

echo "Compiling ML NDFS"
cd "isabelle"
./build
cd ..

echo "Building examples (this may take looooong)"
cd "c++"
./create_ex.sh
cd ..
