chapter AFP
   
session Isabelle_Meta_Model (AFP) = "HOL-Library" +
  description "Isabelle_Meta_Model containing a Toy Example"
  options [timeout = 600]
  theories [document = false]
    "isabelle_home/src/HOL/Isabelle_Main0"
    "isabelle_home/src/HOL/Isabelle_Main1"
    "isabelle_home/src/HOL/Isabelle_Main2"
  theories
    "meta_isabelle/Parser_Pure"
    "meta_isabelle/Meta_Isabelle"
    "meta_isabelle/Printer_Isabelle"
  theories [document = false]
    "toy_example/embedding/Printer"
  theories
    "toy_example/embedding/Generator_static"
    "toy_example/embedding/Generator_dynamic_sequential"
    "toy_example/generator/Design_deep"
    "toy_example/generator/Design_shallow"
    "document/Rail"
  theories
    (* This part ensures that generated theories are accepted:
       in general, if X..._generated_generated.thy is wellformed
                   then we also have X..._generated.thy wellformed *)
    "toy_example/document_generated/Design_generated"
    "toy_example/document_generated/Design_generated_generated"
  document_files
    "root.bib"
    "root.tex"
