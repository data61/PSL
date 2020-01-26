# smart_induct

Dear IJCAR reviewers.
Our running example explained in the paper resides in ``PSL/Smart_Induct/Example/Induction_Demo.thy``.

To use ``smart_induct`` in your own file, 
you only have to use import ``Smart_Induct.thy`` in this directory using the ``imports`` keyword of Isabelle/HOL.
It is important to set the path to ``Smart_Induct.thy`` correctly.

The evaluation files reside in the ``Evaluation`` directory. 
If you open the following files using Isabelle2019, you can see ``smart_induct`` at work:

- ``PSL/Smart_Induct/Evaluation/Depth-First-Search/DFS.thy``
- ``PSL/Smart_Induct/Evaluation/KD_Tree/Nearest_Neighbor.thy``
- ``PSL/Smart_Induct/Evaluation/Priority_Search_Trees/PST_RBT.thy``.

Enjoy!

System requirements:
- A modern computer that can handle Isabelle/HOL will do. For example, you might want to have 16 GB of memory.
