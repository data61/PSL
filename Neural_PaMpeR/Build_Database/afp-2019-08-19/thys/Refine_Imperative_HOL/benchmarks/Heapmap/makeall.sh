#!/bin/bash

echo "Compiling Java Heapmap"
cd "java"
javac -cp ".:stdlib.jar" Test.java
cd ..

echo "Compiling ML Heapmap"
cd "isabelle"
./build
cd ..

