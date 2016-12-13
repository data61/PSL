# PSL

This repository contains the implementation of *proof strategy language (PSL)* and its default strategy,
**try_hard**, for Isabelle2016**-1**. Note that Isabelle2016 is no longer supported.

## Installation
1. Install [Isabelle2016-1](https://isabelle.in.tum.de/).
2. Download or clone this repository (git clone https://github.com/data61/PSL.git).
3. Then, Users can install PSL and try_hard by importing *.PSL.thy* to their theory files
   with the Isabelle keyword, **imports**.

## Basic Commands
- The keyword **strategy** defines a new strategy.
- The keyword **find_proof** invokes PLS's runtime system searching for a proof based on a given strategy.
- The keyword **try_hard** searches for a proof based on the default strategy.

## Hints
PSL's runtime tactic generation can result in a large number of messages in Isabelle/jEdit's output panel.
This might cause Isabelle/jEdit to pause PSL's proof search after reaching its default upper limit for tracing messages.
- One can circumvent this situation by changing the upper limit to an extreamly large number, say 99999999.
- One can change the upper limit for tracing messages via jEdit's menus:
  Plugin Options => Isabelle => General => Editor Reactivity => Editor Tracing Messages.

## Contents
- *./PSL.thy*      reads all the necessary files to use PSL and try_hard.
- *./Example.thy*  contains small example strategies and use cases.
- *./PSLCore/*     contains the interpreter of PSL.
- *./Runtime/*     contains the interpretation of each dynamic tactic.
- *./Category/*    contains a general purpose constructor class library used to develop PSL.

## Documentations
For more details, please read the paper [A Proof Strategy Language and Proof Script Generation for Isabelle/HOL](https://arxiv.org/abs/1606.02941) available at arXiv.org.
