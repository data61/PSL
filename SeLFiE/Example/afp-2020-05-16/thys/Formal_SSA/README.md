Verified Construction of Static Single Assignment Form
======================================================

Abstract
--------
Modern compilers use an intermediate representation in static single assignment (SSA) form, which simplifies many optimizations.
However, the high implementation complexity of efficient SSA construction algorithms poses a challenge to verified compilers.
In this paper, we consider a variant of the recent SSA construction algorithm by Braun et al. that combines simplicity and efficiency, and is therefore a promising candidate to tackle this challenge.
We prove the correctness of the algorithm using the theorem prover Isabelle/HOL.
Furthermore, we prove that the algorithm constructs pruned SSA form and, in case of a reducible control flow graph, minimal SSA form.
To the best of our knowledge, these are the first formal proofs regarding the quality of an SSA construction algorithm.
Finally, we replace the unverified SSA construction of the CompCertSSA project with code extracted by Isabelle's code generator to demonstrate the applicability to real world programs.



Requirements
------------

For running the formalization you need

- A running version of [Isabelle2015](https://isabelle.in.tum.de/) with `isabelle` in your `$PATH`.

If you'd like to build the example interpretation with a While language you additionally need

- the [archive of formal proofs (AFP)](http://isa-afp.org/) installed as an Isabelle component.
  See [http://isa-afp.org/using.shtml](http://isa-afp.org/using.shtml) for details on how to do that.

For building the CompCertSSA compiler using our SSA construction algorithm

- see [http://compcert.inria.fr/download.html](http://compcert.inria.fr/download.html) for additional requirements.


Build instructions
------------------

You can use GNU make to build several targets:

- `compcertSSA`: downloads CompCertSSA stable version 2.0 from the [CompCertSSA homepage](http://compcertssa.gforge.inria.fr/),
  and applies a patch weaving in some glue code to use the SSA construction from Braun et al. (see `./compcertSSA-Braun.patch` for details)

- `FormalSSA`: runs the Isabelle formalization and generates the verified SSA construction algorithm.
  (File `./compcertSSA/midend/SSA/BraunSSA.ml`)

- `ccomp`: builds the CompCertSSA compiler for the target platform `ia32-linux`. You can change that by setting the environment variable `COMPCERTSSA_TARGET` to the target platform of your choice (see `Makefile`).

- `ifplot`: performs measurements on the family of test programs referenced in section 7 of our paper and plots the result via `gnuplot`. You can change the testing parameters by editing the `Makefile`.


