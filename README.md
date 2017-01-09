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
- The keyword **try_hard1** is similar to try_hard, but focuses only on the first sub-goal.

## Hints
PSL's runtime tactic generation can result in a large number of messages in Isabelle/jEdit's output panel.
This might cause Isabelle/jEdit to pause PSL's proof search after reaching its default upper limit for tracing messages.
- One can circumvent this situation by changing the upper limit to an extreamly large number, say 99999999.
- One can change the upper limit for tracing messages via jEdit's menus:
  Plugin Options => Isabelle => General => Editor Reactivity => Editor Tracing Messages.

## Contents
- *./Utils.ML*                     includes various utility functions.
- *./Subtool.ML*                   treats Isabelle's subtools as state-monad tactics.
- *./Dynamic_Tactic_Generation.ML* facilitates runtime tactic generation.
- *./Constructor_Class.ML/*        is a general purpose constructor class library.
- *./Instantiation.ML*             instantiates some type constructors as members of constructor classes.
- *./Monadic_Prover.ML*            contains the interpreter of PSL.
- *./Parser_Combinator.ML*         contains general purpose monadic parser combinators.
- *./PSL_Parser.ML*                defines the PSL parser.
- *./Isar_Interface.thy*           sets up the Isabelle/Isar interface for PSL.
- *./Try_Hard.thy*                 defines the default strategy try_hard.
- *./PSL.thy*                      reads all the necessary files to use PSL and try_hard.
- *./Example.thy*                  presents small example strategies and use cases.

## FAQ

*Q1.* Why yet another tactic language? How is PSL different from, say, Eisbach?

*A1.* PSL’s runtime system attempts to generate efficient proof scripts from a given strategy by searching for the appropriate specialisation and combination of tactics for a particular conjecture without direct user interaction. Eisbach does not generate methods dynamically, trace proof attempts, nor support parallelism natively. Eisbach is good when engineers already know how to prove their conjecture in Isabelle, while PSL is good when they want to find out how to prove it.

*Q2.* To be honest, I do not have time to learn a new language. Can I still use PSL without learning its syntax?

*A2.* We made PSL’s syntax similar to that of Isabelle’s tactic language to lower the learning barrier of PSL. But if you do not feel writing your custom strategy, enter *try_hard*. It invokes the default strategy, TryHard. The lack of input from human engineers on the proof obligation at hand makes the TryHard less specific to each conjecture; however, we made try hard more powerful than existing proof automation tools for Isabelle by specifying larger search spaces.

## Documentations
For more details, please read the paper [A Proof Strategy Language and Proof Script Generation for Isabelle/HOL](https://arxiv.org/abs/1606.02941) available at arXiv.org.

## Screenshot
![Screenshot](https://github.com/data61/PSL/blob/master/image/screen_shot_tall.png)
