session Smart_Isabelle (psl) = HOL +
  options [timeout = 30000]
  theories
    Smart_Isabelle
  document_files
    "root.tex"
    "root.bib"

session "PSL" (psl) in PSL = HOL +
  options [timeout = 600]
  theories [document = false]
    "PSL"
  document_files
    "root.tex"
    "root.bib"
(*
session "PaMpeR" (psl) in PaMpeR = "PSL" +
  options [timeout = 6000]
  theories [document = false]
    "PaMpeR"
  document_files
    "root.tex"
    "root.bib"
*)
session "LiFtEr" (psl) in LiFtEr = "PSL" +
  options [timeout = 600]
  theories [document = false]
    "LiFtEr"
  document_files
    "root.tex"
    "root.bib"

session Smart_Induct (psl) in Smart_Induct = "LiFtEr" +
  options [timeout = 3000]
  theories
    Smart_Induct
  document_files
    "root.tex"
    "root.bib"
(*
session Evaluation (psl) in "Smart_Induct/Evaluation" = "Smart_Induct" +
  options [timeout = 300000]
  sessions
    "HOL-Data_Structures"
    "HOL-Analysis"
(* The top-level theories of the submission: *)
  theories
    "Nearest_Neighbors"
    "Goodstein_Lambda"
    "DFS"
    "PST_RBT"
    "Challenge1A"
  document_files
    "root.tex"
    "root.bib"
*)