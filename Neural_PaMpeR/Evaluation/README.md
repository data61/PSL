## The details of our preliminary evaluation.

### Machine specification:
   - CPU model name: Intel (R) Xeon(R) CPU E5-2690 v4 @ 2.60GHz
   - cache size: 35840 KB
   - number of CPUs: 56
   - main memory: 252 GB

### Evaluation steps:
1. Build a training dataset from Isabelle's standard library
   1. Modify Isabelle/src/Pure/Isar/outer_syntax.ML,
      - so that we can overwrite the definition of the **apply** command and the **by** command.
      - We provided our version of outer_syntax.ML within PSL/PaMpeR. You can replace the original file with this file.
   2. Include the path to PSL/PaMpeR/Build_Database/Build_Database.thy in the **import** statement in Isabelle/src/HOL/Main.thy.
   3. Include the following line almost at the end of Isabelle/src/HOL/Main.thy but just before the **end** command.
      - ML{\*FE_Interface.FE_activate ()\*}
   4. Build an Isabelle image as usual.
      - Warning! This step is very time-consuming. On our machine, it took 29 hours of elapsed time and 462 cpu hours.
      - This step creates a rawdatabase, **Database**, in PSL/PaMpeR.
2. Preprocess the resulting raw training data.
   - Build our session **Preprocess** provided in PaMpeR/Preprocess.
   - This step creates a database for each proof method in PaMpeR/Databases.
   - This step also creates method_names, a file containing the list of proof methods found in the training data.
3. Build regression trees.
   - Build our session **Build_Regression_Tree** provided in PaMpeR/Build_Regression_Tree.
   - This step creates a file (regression_trees.txt) containing regression trees for all proof methods appearing in the trainig dta.
5. Build a new Isabelle image for cross-evaluation.
   1. Remove the Isabelle image stored in ~/.isabelle.
   2. Remove the path to PSL/PaMpeR/Build_Database/Build_Database.thy in the **import** statement in Isabelle/src/HOL/Main.thy added in Step 1.
   3. Include the path to PSL/PaMpeR/Build_Database/Evaluation/Evaluation.thy in the **import** statement in Isabelle/src/HOL/Main.thy.
   4. Build Isabelle.
      - Warning! This step is time consuming.
   5. This step creates a file, evaluation.txt, in PSL/PaMpeR/Evaluation.
6. Remove the **evaluation.txt** in PSL/PaMpeR/Evaluation.
   - This is an evaluation file created from Isabelle's standard library.
   - We should not include this evaluation result, since we used this library as a training dataset.
7. Build the evaluation results from the target AFP library.
   1. Download the AFP from https://www.isa-afp.org/.
      - We used the AFP files downloaded on 27th of October 2017.
   2. Built the AFP only with the target articles written below.
      - Modify the **ROOTS** file in thys, so that it lists articles written below.
   3. This step creates a file, evaluation.txt, in PSL/PaMpeR/Evaluation.
      - Warning! This step is time consuming.
8. Postprocess the raw evalation results.
   1. Build the session in PSL/PaMpeR/Postprocess.
   2. This process creates eval_result.txt in PSL/PaMpeR/Postprocess.
   3. If you want to sort the results, type **sort -k3 -nr eval_result.txt** in PSL/PaMeR/Postprocess.
   4. This should generate the table presented below:

## PaMpeR: The complete table for the ITP2018 preliminary evaluation:

| method | number of recorded occrences in training dataset | percentage in training dataset | number of occurences in testing dataset | percentage in testing dataset | How often PaMpeR recommended this method among the 1 most promising method in testing dataset [%] | How often PaMpeR recommended this method among the 2 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 3 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 4 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 5 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 6 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 7 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 8 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 9 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 10 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 11 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 12 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 13 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 14 most promising methods in testing dataset [%] | How often PaMpeR recommended this method among the 15 most promising methods in testing dataset [%] |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|simp | 38251 | 27.4 | 36643 | 24.3 | 60 | 98 | 99 | 99 | 99 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100|
|auto | 26985 | 19.4 | 39996 | 26.5 | 54 | 84 | 94 | 96 | 97 | 98 | 99 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100|
|rule | 16547 | 11.9 | 15040 | 10.0 | 5 | 7 | 44 | 84 | 96 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100|
|blast | 8500 | 6.1 | 8003 | 5.3 | 0 | 21 | 21 | 31 | 53 | 81 | 94 | 98 | 99 | 100 | 100 | 100 | 100 | 100 | 100|
|metis | 5147 | 3.7 | 6757 | 4.5 | 0 | 0 | 0 | 17 | 28 | 37 | 39 | 46 | 58 | 72 | 82 | 88 | 91 | 93 | 96|
|intro | 3063 | 2.2 | 2234 | 1.5 | 0 | 0 | 0 | 2 | 10 | 11 | 19 | 42 | 70 | 83 | 89 | 92 | 93 | 94 | 94|
|erule | 2734 | 2.0 | 1463 | 1.0 | 0 | 0 | 2 | 8 | 18 | 28 | 38 | 44 | 56 | 61 | 63 | 65 | 65 | 66 | 66|
|induct | 2672 | 1.9 | 3609 | 2.4 | 0 | 6 | 8 | 9 | 13 | 19 | 48 | 66 | 74 | 77 | 78 | 78 | 80 | 86 | 92|
|rule_tac | 2586 | 1.9 | 1018 | 0.7 | 0 | 21 | 23 | 28 | 30 | 31 | 32 | 34 | 38 | 40 | 41 | 41 | 42 | 46 | 51|
|force | 2397 | 1.7 | 2861 | 1.9 | 0 | 0 | 0 | 0 | 0 | 3 | 12 | 23 | 34 | 44 | 51 | 67 | 78 | 88 | 93|
|cases | 2381 | 1.7 | 3383 | 2.2 | 0 | 0 | 0 | 0 | 0 | 19 | 46 | 65 | 72 | 75 | 75 | 77 | 79 | 82 | 85|
|subst | 2369 | 1.7 | 2746 | 1.8 | 0 | 0 | 0 | 0 | 2 | 6 | 14 | 26 | 37 | 42 | 46 | 50 | 55 | 61 | 65|
|simp_all | 2088 | 1.5 | 2477 | 1.6 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 9 | 24 | 44 | 56 | 71 | 81 | 88|
|drule | 1672 | 1.2 | 763 | 0.5 | 0 | 0 | 0 | 0 | 4 | 5 | 8 | 10 | 20 | 37 | 54 | 72 | 86 | 94 | 97|
|drule_tac | 1563 | 1.1 | 208 | 0.1 | 0 | 0 | 0 | 1 | 1 | 1 | 1 | 12 | 25 | 37 | 54 | 67 | 74 | 76 | 78|
|fastforce | 1315 | 0.9 | 2663 | 1.8 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 9 | 14 | 22 | 36 | 51 | 65|
|unfold | 1261 | 0.9 | 1525 | 1.0 | 0 | 0 | 0 | 0 | 2 | 5 | 7 | 7 | 7 | 9 | 18 | 31 | 47 | 60 | 67|
|transfer | 1161 | 0.8 | 1418 | 0.9 | 0 | 49 | 56 | 56 | 56 | 56 | 56 | 56 | 58 | 62 | 72 | 80 | 88 | 92 | 92|
|fact | 1146 | 0.8 | 2354 | 1.6 | 0 | 4 | 4 | 4 | 4 | 4 | 4 | 8 | 17 | 31 | 48 | 53 | 53 | 53 | 53|
|fast | 1047 | 0.8 | 1311 | 0.9 | 0 | 0 | 0 | 8 | 10 | 10 | 11 | 11 | 11 | 11 | 12 | 12 | 13 | 14 | 15|
|case_tac | 934 | 0.7 | 918 | 0.6 | 0 | 0 | 0 | 2 | 7 | 8 | 10 | 12 | 15 | 16 | 20 | 41 | 54 | 61 | 68|
|subgoal_tac | 870 | 0.6 | 329 | 0.2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 5 | 9 | 21 | 33 | 44 | 51|
|clarsimp | 861 | 0.6 | 2311 | 1.5 | 0 | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 5 | 7 | 8 | 11|
|clarify | 826 | 0.6 | 352 | 0.2 | 0 | 0 | 0 | 1 | 5 | 11 | 11 | 11 | 12 | 12 | 13 | 14 | 16 | 19 | 24|
|meson | 685 | 0.5 | 333 | 0.2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 5 | 13 | 25 | 43 | 48|
|assumption | 665 | 0.5 | 459 | 0.3 | 5 | 6 | 6 | 17 | 33 | 42 | 47 | 48 | 48 | 48 | 48 | 48 | 48 | 49 | 49|
|induction | 644 | 0.5 | 916 | 0.6 | 0 | 0 | 0 | 9 | 18 | 23 | 27 | 27 | 27 | 27 | 27 | 27 | 28 | 34 | 36|
|arith | 594 | 0.4 | 428 | 0.3 | 0 | 0 | 0 | 0 | 0 | 0 | 32 | 48 | 49 | 49 | 50 | 50 | 50 | 50 | 50|
|erule_tac | 481 | 0.3 | 214 | 0.1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 17 | 23 | 33 | 41 | 49 | 49 | 50|
|- | 478 | 0.3 | 419 | 0.3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 6 | 13 | 16 | 22 | 22 | 22|
|tactic | 468 | 0.3 | 30 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 3 | 3|
|safe | 458 | 0.3 | 523 | 0.3 | 0 | 3 | 9 | 13 | 13 | 13 | 13 | 13 | 14 | 20 | 24 | 30 | 30 | 34 | 40|
|standard | 415 | 0.3 | 246 | 0.2 | 44 | 54 | 55 | 59 | 70 | 76 | 76 | 77 | 78 | 78 | 78 | 78 | 78 | 78 | 78|
|iprover | 336 | 0.2 | 265 | 0.2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 3 | 19 | 24 | 24|
|induct_tac | 335 | 0.2 | 116 | 0.1 | 0 | 0 | 0 | 0 | 2 | 6 | 7 | 7 | 7 | 7 | 7 | 7 | 7 | 7 | 7|
|elim | 318 | 0.2 | 213 | 0.1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|frule_tac | 303 | 0.2 | 61 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|frule | 286 | 0.2 | 267 | 0.2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|nominal_induct | 280 | 0.2 | 24 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|linarith | 235 | 0.2 | 104 | 0.1 | 0 | 0 | 0 | 0 | 14 | 15 | 15 | 15 | 16 | 19 | 19 | 19 | 19 | 19 | 19|
|rename_tac | 221 | 0.2 | 258 | 0.2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|generate_fresh | 199 | 0.1 | 21 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|unfold_locales | 176 | 0.1 | 1117 | 0.7 | 0 | 0 | 0 | 0 | 8 | 14 | 32 | 39 | 41 | 43 | 47 | 50 | 54 | 54 | 55|
|eventually_elim | 153 | 0.1 | 297 | 0.2 | 0 | 0 | 27 | 46 | 61 | 84 | 97 | 99 | 99 | 100 | 100 | 100 | 100 | 100 | 100|
|insert | 146 | 0.1 | 169 | 0.1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1|
|cut_tac | 128 | 0.1 | 77 | 0.1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|rotate_tac | 120 | 0.1 | 6 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|smt | 116 | 0.1 | 129 | 0.1 | 0 | 0 | 0 | 12 | 16 | 20 | 20 | 20 | 20 | 20 | 20 | 20 | 20 | 20 | 20|
|intro_classes | 116 | 0.1 | 236 | 0.2 | 70 | 74 | 91 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100|
|algebra | 81 | 0.1 | 55 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 18 | 22 | 22 | 22 | 22 | 22 | 22 | 22|
|contradiction | 78 | 0.1 | 46 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 70 | 70 | 74 | 74 | 74|
|presburger | 77 | 0.1 | 251 | 0.2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|sos | 72 | 0.1 | 7 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|ind_cases | 72 | 0.1 | 18 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|transfer_prover | 68 | 0.0 | 114 | 0.1 | 59 | 61 | 69 | 93 | 96 | 96 | 96 | 96 | 96 | 96 | 96 | 96 | 96 | 96 | 96|
|normalization | 68 | 0.0 | 40 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|relation | 65 | 0.0 | 63 | 0.0 | 84 | 84 | 84 | 84 | 84 | 84 | 84 | 84 | 84 | 84 | 84 | 84 | 84 | 84 | 84|
|vector | 60 | 0.0 | 73 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|pat_completeness | 57 | 0.0 | 115 | 0.1 | 96 | 96 | 96 | 96 | 96 | 96 | 96 | 96 | 96 | 96 | 96 | 96 | 96 | 96 | 96|
|measurable | 53 | 0.0 | 44 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|atomize_elim | 48 | 0.0 | 56 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 5 | 5 | 5 | 12 | 12 | 16 | 16 | 16|
|fold | 38 | 0.0 | 68 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|countable_datatype | 37 | 0.0 | 12 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 100 | 100 | 100 | 100|
|eval | 35 | 0.0 | 111 | 0.1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 12 | 27 | 52 | 52 | 53|
|uint_arith | 32 | 0.0 | 185 | 0.1 | 63 | 69 | 69 | 69 | 69 | 69 | 69 | 69 | 69 | 69 | 69 | 69 | 69 | 69 | 69|
|coinduction | 30 | 0.0 | 118 | 0.1 | 0 | 13 | 32 | 33 | 33 | 33 | 33 | 33 | 33 | 33 | 33 | 33 | 33 | 33 | 33|
|hypsubst | 22 | 0.0 | 10 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|best | 21 | 0.0 | 116 | 0.1 | 0 | 0 | 0 | 0 | 0 | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3|
|coinduct | 20 | 0.0 | 61 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 30 | 33 | 33 | 33 | 33 | 33 | 33 | 33|
|atomize | 20 | 0.0 | 9 | 0.0 | 0 | 0 | 0 | 44 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100|
|thin_tac | 17 | 0.0 | 27 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|split | 14 | 0.0 | 18 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|approximation | 14 | 0.0 | 3 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|hypsubst_thin | 13 | 0.0 | 15 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|vcg | 11 | 0.0 | 198 | 0.1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|moura | 10 | 0.0 | 7 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 14 | 57 | 100 | 100 | 100|
|intro_locales | 10 | 0.0 | 13 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 8 | 23|
|lexicographic_order | 7 | 0.0 | 17 | 0.0 | 0 | 0 | 0 | 6 | 6 | 6 | 6 | 6 | 29 | 65 | 65 | 65 | 65 | 65 | 65|
|induction_schema | 7 | 0.0 | 10 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|use | 6 | 0.0 | 4 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|unat_arith | 6 | 0.0 | 34 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 15|
|transfer_step | 4 | 0.0 | 5 | 0.0 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100 | 100|
|satx | 4 | 0.0 | 3 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|norm | 4 | 0.0 | 8 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|coherent | 4 | 0.0 | 1 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|transfer_prover_start | 3 | 0.0 | 1 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|slowsimp | 3 | 0.0 | 3 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
|bestsimp | 3 | 0.0 | 4 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|
this | 2 | 0.0 | 30 | 0.0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0|

## The list of AFP articles used in the preliminary evaluation at ITP2018.
- Abstract-Rewriting
- Affine_Arithmetic
- Akra_Bazzi
- Allen_Calculus
- Applicative_Lifting
- Automatic_Refinement
- Binomial-Heaps
- Buildings
- Category3
- Cauchy
- CAVA_Automata
- Coinductive
- Coinductive_Languages
- Collections
- Containers
- Datatype_Order_Generator
- Deep_Learning
- Density_Compiler
- Deriving
- DFS_Framework
- Efficient-Mergesort
- Finger-Trees
- Gauss_Jordan
- Gauss-Jordan-Elim-Fun
- IP_Addresses
- Jinja
- Jordan_Normal_Form
- Landau_Symbols
- LightweightJava
- List-Index
- List_Update
- Kleene_Algebra
- Markov_Models
- Matrix
- MonoidalCategory
- Name_Carrying_Type_Inference
- Native_Word
- Ordinal
- Ordinals_and_Cardinals
- Ordinary_Differential_Equations
- Pairing_Heap
- Paraconsistency
- Partial_Function_MR
- Perfect-Number-Thm
- Pi_Calculus
- Polynomial_Factorization
- Polynomial_Interpolation
- Program-Conflict-Analysis
- Rank_Nullity_Theorem
- Refine_Monadic
- Regular-Sets
- Show
- Simpl
- SPARCv8
- Splay_Tree
- Sqrt_Babylonian
- Stone_Algebras
- Stone_Kleene_Relation_Algebras
- Stone_Relation_Algebras
- Timed_Automata
- Transition_Systems_and_Automata
- Triangle
- Trie
- VectorSpace
- Word_Lib
