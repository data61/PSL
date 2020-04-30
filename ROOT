session PSL_And_All_That (psl) = HOL +
  options [timeout = 30000]
  theories
    PSL_And_All_That
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

session "PaMpeR" (psl) in PaMpeR = "PSL" +
  options [timeout = 6000]
  theories [document = false]
    "PaMpeR"
  document_files
    "root.tex"
    "root.bib"

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