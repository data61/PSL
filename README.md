# PSL

This repository contains our proof strategy language (PSL) and its default strategy, try_hard.

Instructions:
Users can use PSL and try_hard by importing PSL to their theory files with the Isabelle keyword,
"imports".
The keyword "strategy" defines a new strategy.
The keyword "find_proof" invokes PLS's runtime system searching for a proof based on a given strategy.
The keyword "try_hard" searches for a proof based on the default strategy.

Hints:
PSL's runtime tactic generation can result in a large number of messages in Isabelle/jEdit's output panel.
This might cause Isabelle/jEdit to pause PSL's proof search after reaching its default upper limit for tracing messages.
One can circumvent this situation by changing the upper limit to an extreamly large number, say 99999999.
One can change the upper limit for tracing messages via jEdit's menus:
  Plugin Options => Isabelle => Generatl => Editor Reactivity => Editor Tracing Messages.

Contents:
./PSL.thy      reads all the necessary files to use PSL and try_hard.
./Example.thy  contains small example strategies and use cases.
./TryHardCore/ contains the interpreter of PSL.
./Runtime/     contains the interpretation of each dynamic tactic.
./Category/    contains a general purpose constructor class library used to develop PSL.

For more details, please read the paper "A Proof Strategy Language and Proof Script Generation for Isabelle/HOL"
available at arXiv.org.
