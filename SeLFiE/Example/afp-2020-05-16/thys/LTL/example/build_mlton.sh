#!/bin/sh

mlton -runtime 'ram-slop 0.5' -output rewrite_example -profile time rewrite_example_mlton.mlb
