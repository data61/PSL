(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section "Tests"
theory PerformanceTest
imports Collections.Collections "HOL-Library.Code_Target_Numeral" 
begin
text_raw \<open>\label{thy:PerformanceTest}\<close>

text \<open>
  In this theory, the performance of the basic operations (memb, ins, delete and iterator) of
  various set implementations is tested.
\<close>

  \<comment> \<open>Simple linear congruence generator for (low-quality) random numbers\<close>
  definition "lcg_next s r = (s mod r, ((22695477::nat)*s + 1) mod 268435456)"

  \<comment> \<open>Repeatedly apply function\<close>
  fun repeat where
    "repeat 0 f \<sigma> = \<sigma>" |
    "repeat (Suc n) f \<sigma> = repeat n f (f \<sigma>)"

  
  \<comment> \<open>Insert random number in range [0..M[ to set\<close>
  definition "rnd_ins_step i M == (\<lambda>(t,s). let (x,s')=lcg_next s M; t'=i x t in (t',s'))"

  \<comment> \<open>Insert N random numbers in range 0..M\<close>
  definition "rnd_insert e i s N M == repeat 
    N (rnd_ins_step i M) (e,s)"

  \<comment> \<open>Remove random number in range [0..M[ from set\<close>
  definition "rnd_remove_step r M == (\<lambda>(t,s). let (x,s')=lcg_next s M; t'=r x t in (t',s'))"
  \<comment> \<open>Remove N random numbers in range 0..M from set\<close>
  definition "rnd_remove r N M txs == 
    repeat N (rnd_remove_step r M) txs"

  \<comment> \<open>Test random number in range [0..M[ for membership\<close>
  definition "rnd_memc_step m M t == (\<lambda>(c,s). let (x,s')=lcg_next s M; c'=if m x t then c+(1::nat) else c in (c',s'))"

  \<comment> \<open>Count how many of N random numbers in range [0..M[ are in set\<close>
  definition "rnd_memc m N M txs ==
    let (t,s) = txs in
      repeat 
        N
        (rnd_memc_step m M t)
        (0::nat,s)
      "

  \<comment> \<open>Parameters: empty, member, insert, delete, iterate,  seed, N, M $\rightarrow$ count, size\<close>
  definition 
    test_all :: "(unit \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's) 
      \<Rightarrow> ('s \<Rightarrow> (nat,nat) set_iterator) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)"
    where
    "test_all e m i d it s N M == let (t,s) = (rnd_remove d N M (rnd_insert (e ()) i s N M)) in
      (fst (rnd_memc m N M (t,s)), it t (\<lambda>_. True) (\<lambda>x c. c+(1::nat)) 0)"

  (* No iteration *)
  definition 
    test_all' :: "(unit \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 
      nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
    where
    "test_all' e m i d s N M == let (t,s) = (rnd_remove d N M (rnd_insert (e ()) i s N M)) in
      (fst (rnd_memc m N M (t,s)))"

  (* No iteration, no removal *)
  definition 
    test_all'' :: "(unit \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
    where
    "test_all'' e m i s N M == let (t,s) = (rnd_insert (e ()) i s N M) in
      (fst (rnd_memc m N M (t,s)))"



  definition "test_hs == test_all hs.empty hs.memb hs.ins hs.delete hs.iteratei"
  definition "test_rs == test_all rs.empty rs.memb rs.ins rs.delete rs.iteratei"
  definition "test_ls == test_all ls.empty ls.memb ls.ins ls.delete ls.iteratei"
  (*definition "test_ts == test_all ts_empty ts_memb ts_ins ts_delete ts_iteratei"*)
  definition "test_ahs == test_all ahs.empty ahs.memb ahs.ins ahs.delete ahs.iteratei"

  definition "test_ias == test_all ias.empty ias.memb ias.ins ias.delete ias.iteratei"

  definition "test_hs' == test_all' hs.empty hs.memb hs.ins hs.delete"
  definition "test_rs' == test_all' rs.empty rs.memb rs.ins rs.delete"
  definition "test_ls' == test_all' ls.empty ls.memb ls.ins ls.delete"
  (*definition "test_ts' == test_all' ts_empty ts_memb ts_ins ts_delete"*)
  definition "test_ahs' == test_all' ahs.empty ahs.memb ahs.ins ahs.delete"
  definition "test_cg' == test_all' (\<lambda>_. {}) (\<in>) insert (\<lambda>x s. s-{x})"
  definition "test_ias' == test_all' ias.empty ias.memb ias.ins ias.delete"


  definition "test_hs'' == test_all'' hs.empty hs.memb hs.ins"
  definition "test_rs'' == test_all'' rs.empty rs.memb rs.ins"
  definition "test_ls'' == test_all'' ls.empty ls.memb ls.ins"
  (*definition "test_ts'' == test_all'' ts_empty ts_memb ts_ins"*)
  definition "test_ahs'' == test_all'' ahs.empty ahs.memb ahs.ins"
  definition "test_cg'' == test_all'' (\<lambda>_. {}) (\<in>) insert"

  definition "test_ias'' == test_all'' ias.empty ias.memb ias.ins"


(*
  code_module Test file "/dev/stdout" contains test_cg' test_cg''
  ML {*
    open Test;

    val start = Time.now();
    test_cg' 1 8000 16000;
    val rt = Time.toMilliseconds (Time.now() - start);
    *}
*)


  export_code
    test_hs test_rs test_ls test_ahs test_ias
    test_hs' test_rs' test_ls' test_ahs' test_cg' test_ias'
    test_hs'' test_rs'' test_ls'' test_ahs'' test_cg'' test_ias''
    checking SML 
    

  (*
    Ad-hoc test code:
  *)
  definition "test_hs_eval a b c = test_hs (nat_of_integer a) (nat_of_integer b) (nat_of_integer c)"
  ML_val \<open>
    val start = Time.now();
    @{code test_hs_eval} 1 100000 200000;
    val rt = Time.toMilliseconds (Time.now() - start);
\<close>

  (*
  export_code 
    test_hs test_rs test_ls test_ts test_ahs 
    test_hs' test_rs' test_ls' test_ts' test_ahs'  test_nts' test_ntsc' test_cg'
    test_hs'' test_rs'' test_ls'' test_ts'' test_ahs''  test_nts'' test_cg''
    in SML 
    module_name Test 
    file "code/sml/generated/Test.ml"
  export_code 
    test_hs test_rs test_ls test_ts test_ahs
    test_hs' test_rs' test_ls' test_ts' test_ahs' test_nts' test_ntsc' test_cg'
    test_hs'' test_rs'' test_ls'' test_ts'' test_ahs'' test_nts'' test_cg''
    in OCaml 
    module_name Test 
    file "code/ocaml/generated/Test.ml"
  export_code 
    test_hs test_rs test_ls test_ts test_ahs
    test_hs' test_rs' test_ls' test_ts' test_ahs' test_nts' test_ntsc' test_cg'
    test_hs'' test_rs'' test_ls'' test_ts'' test_ahs'' test_nts'' test_cg''
    in Haskell 
    module_name Test 
    file "code/haskell/generated"
    (*string_classes*)
    *)


end
