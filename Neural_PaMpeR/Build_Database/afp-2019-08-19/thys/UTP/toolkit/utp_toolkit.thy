(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: utp_toolkit.thy                                                      *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open> Meta-theory for UTP Toolkit \<close>

theory utp_toolkit
  imports
  HOL.Deriv
  "HOL-Library.Adhoc_Overloading"
  "HOL-Library.Char_ord"
  "HOL-Library.Countable_Set"
  "HOL-Library.FSet"
  "HOL-Library.Monad_Syntax"
  "HOL-Library.Countable"
  "HOL-Library.Order_Continuity"
  "HOL-Library.Prefix_Order"
  "HOL-Library.Product_Order"
  "HOL-Library.Sublist"
  "HOL-Algebra.Complete_Lattice"
  "HOL-Algebra.Galois_Connection"
  "HOL-Eisbach.Eisbach"
  "Optics.Lenses"
  Countable_Set_Extra
  FSet_Extra
  Map_Extra
  List_Extra
  List_Lexord_Alt
  Partial_Fun
  Finite_Fun
  Infinity
  Positive
  Total_Recall
begin end