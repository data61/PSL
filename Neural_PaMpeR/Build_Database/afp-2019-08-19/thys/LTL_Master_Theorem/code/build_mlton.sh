#!/bin/sh

mlton -runtime 'ram-slop 0.5' -output ltl_to_dra -profile time ltl_to_dra_mlton.mlb
