#!/bin/sh
ocamlopt -o Main -I generated nums.cmxa generated/Ta.ml Test_setup.ml Pt_examples.ml Main.ml

