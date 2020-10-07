(*<*)
theory Monitor_Code
  imports Monitor
  "HOL-Library.Code_Target_Nat"
  "HOL.String"
  Containers.Containers
begin
(*>*)

derive ccompare MFOTL.trm
derive (eq) ceq MFOTL.trm
derive (rbt) set_impl MFOTL.trm

lemma image_these: "f ` Option.these X = Option.these (map_option f ` X)"
  by (force simp: in_these_eq Bex_def image_iff map_option_case split: option.splits)

lemma meval_MPred: "meval n t db (MPred e ts) = ([Option.these
  ((map_option (\<lambda>f. tabulate f 0 n) o match ts) ` (\<Union>(e', x)\<in>db. if e = e' then {x} else {}))], MPred e ts)"
  unfolding meval.simps image_these image_image o_def ..

lemma meval_MPred': "meval n t db (MPred e ts) = ([Option.these
  (\<Union>(e', x)\<in>db. if e = e' then {map_option (\<lambda>f. tabulate f 0 n) (match ts x)} else {})], MPred e ts)"
  unfolding meval_MPred image_UN split_beta if_distrib[of "image _"] image_insert image_empty o_apply
  ..

lemma these_UNION: "Option.these (UNION A B) = UNION A (Option.these o B)"
  by (auto simp: Option.these_def)

lemma meval_MPred'': "meval n t db (MPred e ts) = ([
  (\<Union>(e', x)\<in>db. if e = e' then set_option (map_option (\<lambda>f. tabulate f 0 n) (match ts x)) else {})], MPred e ts)"
  unfolding meval_MPred' these_UNION o_def prod.case_distrib[of Option.these]
  by (auto simp: Option.these_def map_option_case image_iff split: if_splits option.splits)

lemmas meval_code[code] = meval.simps(1) meval_MPred'' meval.simps(3-9)

definition db_code :: "(char list \<times> 'a list) list \<Rightarrow> (char list \<times> 'a list) set" where
  "db_code = set"

definition verdict_code :: "_ \<Rightarrow> (nat \<times> 'a :: ccompare option list) list" where
  "verdict_code = RBT_Set2.keys"

export_code HOL.equal Collection_Eq.ceq Collection_Order.ccompare Eq Lt Gt set_RBT set_impl phantom
  nat_of_integer integer_of_nat enat literal.explode db_code set interval RBT_set verdict_code
  MFOTL.Var MFOTL.Const
  MFOTL.Pred MFOTL.Eq MFOTL.Neg MFOTL.Or MFOTL.Exists
  MFOTL.Prev MFOTL.Next MFOTL.Since MFOTL.Until
  checking OCaml?

export_code HOL.equal Collection_Eq.ceq Collection_Order.ccompare Eq Lt Gt set_RBT set_impl phantom
  nat_of_integer integer_of_nat enat literal.explode db_code set interval RBT_set verdict_code
  MFOTL.Var MFOTL.Const
  MFOTL.Pred MFOTL.Eq MFOTL.Neg MFOTL.Or MFOTL.Exists
  MFOTL.Prev MFOTL.Next MFOTL.Since MFOTL.Until
  minit_safe mstep in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
