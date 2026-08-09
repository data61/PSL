session "SeLFiE" (psl) in SeLFiE = HOL +
  options [timeout = 600]
  theories [document = false]
    "SeLFiE"
  document_files
    "root.tex"
    "root.bib"
(*
session "PaMpeR" (psl) in PaMpeR = "SeLFiE" +
  options [timeout = 6000]
  theories [document = false]
    "PaMpeR"
  document_files
    "root.tex"
    "root.bib"
*)
session "PSL" (psl) in PSL = "SeLFiE" +
  options [timeout = 600]
  theories [document = false]
    "PSL"
  document_files
    "root.tex"
    "root.bib"

session "TBC" (psl) in TBC =  "PSL" +
  options [timeout = 600]
  theories [document = false]
    "TBC"
  document_files
    "root.tex"
    "root.bib"

session "Abduction" (psl) in Abduction = "TBC" +
  options [timeout = 600]
  theories [document = false]
    "Abduction"
  document_files
    "root.tex"
    "root.bib"

session "Test_Abduction" (psl) in "Abduction/Test" = "Abduction" +
  description "Fast regression tests: concurrency and resource primitives (seconds, no search)."
  theories [document = false]
    "Test_Abduction"

session "Test_Abduction_Isar" (psl) in "Abduction/Test_Isar" = "Abduction" +
  description "Isar-integration scenarios: where AbductionProver can be invoked and whether what it produces fits the surrounding proof. Minutes, not seconds - separate from the fast Test_Abduction suite."
  theories [document = false]
    (*chained by imports, so they build strictly in order rather than in parallel*)
    "Scenario_Chained_Facts"
    "Scenario_Parameters"
    (*pins the assumption steps 2-4 rest on: focus, prove, retrofit*)
    "Retrofit_Probe"

session Smart_Isabelle (psl) = "Abduction" +
  options [timeout = 30000]
  theories
    Smart_Isabelle
  document_files
    "root.tex"
    "root.bib"