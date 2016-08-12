# PSL

This repository contains our proof strategy language (PSL) and its default strategy, try_hard.

Instructions:
Users can use PSL and try_hard by importing PSL to their theory files with the Isabelle keyword,
"imports".
The keyword "strategy" defines a new strategy.
The keyword "find_proof" invokes PLS's runtime system searching for a proof based on a given strategy.
The keyword "try_hard" searches for a proof based on the default strategy.

Contents:
./src/PSL.thy        reads all the necessary files to use PSL and try_hard.
./src/Example.thy    contains small example strategies and use cases.
./src/TryHardCore/ contains the interpreter of PSL.
./src/Runtime/     contains the interpretation of each dynamic tactic.
./src/Category/    contains a general purpose constructor class library used to develop PSL.

For more details, please read the paper "A Proof Strategy Language and Proof Script Generation for Isabelle"
available at arXiv.org.
