This file explains how to replicate the evaluation results reported in our paper titled
  "Faster Smarter Induction in Isabelle/HOL" submitted to TACAS2021.

Important notice: by default VirtualBox assigns about 2 GB of memory and 1 processor to the virtual
machine. This is not enough. The limited memory leads to not only poor performance but also the 
failure of the experiment.

When we conducted our evlauation. We used a MacBook Pro (15-inch, 2019) with 2.6 GHz Intel Core i7 
6-core memory 32 GB 2400 MHz DDR4.

Prerequisite: Unpack the Artifact
  To use our artifact submission, we have to unpack it first. The submitted ZIP file should contain 
  two directories: Isabelle2020 and PSL. In the following we assume that these directories are 
  stored in Desktop of the virtual machine provided by the Artifact Evalution Committiee as follows.
  - /home/tacas/Desktop/Yutaka/Isabelle2020
  - /home/tacas/Desktop/Yutaka/PSL

How to see semantic_induct at Work

We can see semantic_induct at work for the running example presented in our paper in the interactive 
mode of Isabelle/HOL. The necessary command is the following.

  /home/Desktop/Yutaka/Isabelle2020/bin/isabelle jedit -d /home/Desktop/Yutaka/PSL -l Smart_Isabelle /home/Desktop/Yutaka/PSL/SeLFiE/Test_SeLFiE.thy

How to replicate the results.

This experiment consists of two phases:
- (Optional) Phase 1 produces the raw output files. These files are are named Database.txt.
- Phase 2 formats the raw output files, so that the results becomes easier for human engineers to interpret.

Phase 1 takes about 10-20 hours. Therefore, we also pre-built the results from Phase 1, so that
the Artifact Evaluation Committiee (AEC) can skip Phase 1 and proceed to Phase 2 if they wish so.

Phase 0 : Unpack the Artifact.
  We unpack the submitted artifact. The submitted ZIP file should contain two directories:
  Isabelle2020 and PSL. In the following we assume that these directories are stored in Desktop
  of the virtual machine provided by the Artifact Evalution Committiee as follows.

  /home/tacas/Desktop/Yutaka/Isabelle2020
  /home/tacas/Desktop/Yutaka/PSL

Phase 1: Optional Construction of the Raw Results.

Phase 1 - Step 1.
  We build the raw output file for semantic_induct, our tool presented in the paper.
  The evaluation suite for semantic_induct resides in 
  /home/tacas/Desktop/Yutaka/PSL/SeLFiE/Evaluation

  The evaluation target theory files also reside in this directory.
  Therefore, we move our current directory to this directory by typing the following:

  cd /home/tacas/Desktop/Yutaka/PSL/SeLFiE/Evaluation

  Then, we build the raw evaluation result, Database.txt, using the following command:

  /home/Desktop/Yutaka/Isabelle2020/bin/isabelle build -D . -c -j1 -o threads=10

  This command should use the ROOTS file stored in this directory to run Isabelle2020 stored in
  /home/Desktop/Yutaka/Isabelle2020.

  The results should be appear in 
  /home/tacas/Desktop/Yutaka/PSL/SeLFiE/Evaluation/Eval_Base/Database.txt

Phase 1 - Step 2.
  We build the raw output file for smart_induct to compare the performance of semantic_induct.

  The evaluation suite for smart_induct resides in 
  /home/tacas/Desktop/Yutaka/PSL/Semantic_Induct/Evaluation

  The evaluation target theory files also reside in this directory.
  Therefore, we move our current directory to this directory by typing the following:

  cd /home/tacas/Desktop/Yutaka/PSL/Smart_Induct/Evaluation

  Then, we build the raw evaluation result, Database.txt, using the following command:

  /home/Desktop/Yutaka/Isabelle2020/bin/isabelle build -D . -c -j1 -o threads=10

  This command should use the ROOTS file stored in this directory to run Isabelle2020 stored in
  /home/Desktop/Yutaka/Isabelle2020.

  The results should appear in 
  /home/tacas/Desktop/Yutaka/PSL/Smart_Induct/Evaluation/Eval_Base/Database.txt

Phase 1 - Step 3.
  We copy the raw results from Phase 1 to the right locations with the right names, so that theory
  files for formatting the raw results can handle them.
  Note that we have already produced these files at the right locations with the right names,
  so that the AEC can skip Phase 1.

  For semantic_induct
  cp /home/tacas/Desktop/Yutaka/PSL/SeLFiE/Evaluation/Eval_Base/Database.txt /home/tacas/Desktop/Yutaka/PSL/SeLFiE/Evaluation/Format_Result/tacas2021_timeout5.csv

  For smart_induct
  cp /home/tacas/Desktop/Yutaka/PSL/Smart_Induct/Evaluation/Eval_Base/Database.txt /home/tacas/Desktop/Yutaka/PSL/Smart_Induct/Evaluation/Format_Result/tacas2021_timeout5.csv

  This completes Phase 1.

Phase 2: Format the Raw Results.

  Now we open Isabelle/HOL in the interactive mode with semantic_induct and smart_induct using the ROOT
  file in /home/tacas/Desktop/Yutaka/PSL.
  We can do so by typing the following command.

  /home/Desktop/Yutaka/Isabelle2020/bin/isabelle jedit -d /home/tacas/Desktop/Yutaka/PSL/ -l Smart_Isabelle /home/tacas/Desktop/Yutaka/PSL/Smart_Induct/Evaluation/Format_Result/Format_Result_Smart_Induct.thy

  Format_Result_Smart_Induct.thy imports SeLFiE/Evaluation/Format_Result/Format_Result_Semantic_induct.thy,
  which formats the raw file for semantic_induct.

  And Line 298 of Format_Result_Smart_Induct.thy produces a table presented in our paper.
  We can observe this formatted result by moving the cursor of the virtual machine on top of Line 298,
  which states "val _ = map tracing both_results".
  Then, the Output panel of Isabelle/jEdit should show the table presented in our paper.
  We included a screenshot (screenshot.png) in our artifact submission to show how this looks.
