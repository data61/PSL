#!/bin/bash

(
  while read n
  do
    echo "$n $(./test/ifgen $n > test/if.c && compcertSSA/ccomp -stdlib compcertSSA/runtime -ssa on -c test/if.c | grep "Braun   " | awk '{print $NF}')"
  done
) > ifplot.data
