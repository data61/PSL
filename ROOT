session "SeLFiE" (psl) in SeLFiE = HOL +
  options [timeout = 600]
  theories [document = false]
    "SeLFiE"
  document_files
    "root.tex"
    "root.bib"

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

session Smart_Isabelle (psl) = "Abduction" +
  options [timeout = 30000]
  theories
    Smart_Isabelle
  document_files
    "root.tex"
    "root.bib"
session Contract_Test (psl) in "Contract_Test" = Smart_Isabelle +
  description "The producer's half of the PSL/consumer contract - golden fixtures for
    everything external consumers parse. See Contract_Test.thy's header."
  options [timeout = 600]
  theories
    Contract_Test
