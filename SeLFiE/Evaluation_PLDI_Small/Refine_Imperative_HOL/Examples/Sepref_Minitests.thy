(*<*)
section \<open>Miscellaneous Tests\<close>
theory Sepref_Minitests
imports 
  "../IICF/IICF"
  Sepref_Graph
  "HOL-Library.Code_Target_Numeral"
begin


  (* (* Pattern to analyze why preparing with a rule fails *)
  apply (tactic \<open> let 
      val ctxt = @{context}
      val i = 0
      val thm = @{thm sepref_fr_rules(30)}
      open Sepref_Translate Refine_Util
    in  
      CONVERSION (Refine_Util.HOL_concl_conv (monitor_conv' "" (prepare_refine_conv (i,thm))) ctxt) 1
    end  
      \<close>)
  *)

  definition [simp]: "mop_plus = RETURN oo (+)"
  definition [simp]: "mop_plusi = return oo (+)"
  lemma [sepref_fr_rules]: "(uncurry mop_plusi,uncurry mop_plus) \<in> nat_assn\<^sup>k*\<^sub>anat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    by (sep_auto intro!: hfrefI hn_refineI simp: pure_def)
  sepref_register mop_plus

  sepref_definition copy_test is "(\<lambda>x. do {
    let y = x+ x;
    mop_plus y y
    })" :: "((nat_assn)\<^sup>k \<rightarrow>\<^sub>a UNSPEC)"
    by sepref

  definition "bar s \<equiv> do {
    x\<leftarrow>RETURN (insert (1::nat) s);
    y\<leftarrow>RETURN (insert (1::nat) x);
    ASSERT (y\<noteq>{});
    if 1\<in>y then
      RETURN (y)
    else RETURN (insert (1::nat) y)
  }"

definition "bar2 s \<equiv> do {
    if (1::nat)\<in>s then
      RETURN True
    else RETURN False
  }"


definition "bar' \<equiv> do {
    y \<leftarrow> RETURN {1,1::nat};
    if 1\<in>y then
      RETURN (y)
    else RETURN (insert 1 y)
  }"


definition "foo \<equiv> do {
  s \<leftarrow> RETURN [1,1,1::nat];
  y \<leftarrow> RETURN ({}::nat set);
  RECT (\<lambda>D l. 
    case l of 
      [] \<Rightarrow> RETURN (case [0,1] of [] \<Rightarrow> {} | x#xs \<Rightarrow> {x})
    | x#l \<Rightarrow> do {
        \<^cancel>\<open>r \<leftarrow> RETURN (y\<union>y);\<close>
        r \<leftarrow> D l;
        \<^cancel>\<open>RETURN (insert (x+1) r)\<close>
        RETURN (if x<1 then insert x r else insert (x+1) r)
    }) s
  }
"

definition "simple_rec \<equiv> do {
  RECT (\<lambda>D l. case l of 
    [] \<Rightarrow> RETURN 0 
  | x#xs \<Rightarrow> do {
      a\<leftarrow>D xs;
      RETURN (a+x)
    }
  ) [1,0::nat]
}"


definition "simple_while \<equiv> do {
  WHILEIT (\<lambda>(i,m). i \<notin> dom m) (\<lambda>(i,m). i\<ge>1) (\<lambda>(i,m). do {
    let i=i+1;
    RETURN (i,m)
  }) (10::nat, Map.empty::nat \<rightharpoonup> nat)
}"

definition "lst_mem_to_sets \<equiv> do {
  l\<leftarrow>RETURN [0,1,0::nat];
  RECT (\<lambda>D l. 
    case l of 
      [] \<Rightarrow> RETURN []
    | x#l \<Rightarrow> do {
        r \<leftarrow> D l;
        RETURN ({x}#r)
    }) l
  }
"

definition "lst_mem_to_sets_nonlin \<equiv> do {
  l\<leftarrow>RETURN [0,1,0::nat];
  RECT (\<lambda>D l. 
    case l of 
      [] \<Rightarrow> RETURN []
    | x#l \<Rightarrow> do {
        r \<leftarrow> D l;
        RETURN ({x,x}#r)
    }) l
  }
"

definition "lst_mem_to_sets_nonlin2 \<equiv> do {
  l\<leftarrow>RETURN [0,1,0::nat];
  RECT (\<lambda>D l. 
    case l of 
      [] \<Rightarrow> RETURN []
    | x#l \<Rightarrow> do {
        r \<leftarrow> D l;
        RETURN ({x}#r@r)
    }) l
  }
"

definition "lst_nonlin \<equiv> do {
  l\<leftarrow>RETURN [0::nat];
  RETURN (case l of [] \<Rightarrow> l | x#xs \<Rightarrow> x#l)
}"

definition "lst_nonlin2 \<equiv> do {
  l\<leftarrow>RETURN [0::nat];
  RETURN (case l of [] \<Rightarrow> [] | x#xs \<Rightarrow> x#(x#xs))
}"

definition "lst_nonlin3 \<equiv> do {
  l\<leftarrow>RETURN [{0::nat}];
  RETURN (case l of [] \<Rightarrow> [] | x#xs \<Rightarrow> x#(x#xs))
}"

definition "lst_nonlin4 \<equiv> do {
  l\<leftarrow>RETURN [{0::nat}];
  RETURN (l@l)
}"


definition "dup_arg == do {
  x <- RETURN [1::nat];
  RETURN (x@x)
}"

definition "big_list == RETURN [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1::nat]"
definition "big_list2 == do {
  x1 <- RETURN ({}::nat set);
  x2 <- RETURN {};
  x3 <- RETURN {};
  x4 <- RETURN {};
  x5 <- RETURN {};
  x6 <- RETURN {};
  x7 <- RETURN {};
  x8 <- RETURN {};
\<^cancel>\<open>  x9 <- RETURN {};
  x10 <- RETURN {};
  x11 <- RETURN {};
  x12 <- RETURN {};
  x13 <- RETURN {};
  x14 <- RETURN {};
  x15 <- RETURN {};
  x16 <- RETURN {};\<close>
  RETURN [x1,x2,x3,x4,x5,x6,x7,x8\<^cancel>\<open>,x9,x10,x11,x12,x13,x14,x14,x15,x16]\<close>]
}"


term Set.insert

definition "foo1 \<equiv> 
  case [] of 
    [] \<Rightarrow> RETURN {} 
  | x#l \<Rightarrow> do {
      r \<leftarrow> RETURN ({}::nat set);
      RETURN (if x<1 then insert x r else insert x r)
  }
"

definition "basic_foreach \<equiv> do {
  FOREACH\<^sub>C {0,1::nat} (\<lambda>s. s>1) (\<lambda>x s. RETURN (x+s)) 0
}"

definition "basic_foreach2 \<equiv> do {
  FOREACH\<^sub>C {0,1::nat} (\<lambda>_. True) (\<lambda>x s. RETURN (insert x s)) {}
}"


definition "basic_option \<equiv> do {
  let a={};
  let b=Some a;
  let c=Some (0::nat);
  let d=Some (1::nat);
  RETURN (b,c=d)
}"


definition dfs :: "(('a\<times>'a) set) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a set \<times> bool) nres" 
  where
  "\<And>E vd v0. dfs E vd v0 \<equiv> REC\<^sub>T (\<lambda>D (V,v). 
    if v=vd then RETURN (V,True)
    else if v\<in>V then RETURN (V,False)
    else do {
      let V=insert v V;
      FOREACH\<^sub>C (E``{v}) (\<lambda>(_,b). b=False) (\<lambda>v' (V,_). D (V,v')) (V,False) }
  ) ({},v0)"


lemma ID_unfold_vars: "ID x y T \<Longrightarrow> x\<equiv>y" by simp

schematic_goal testsuite_basic_param:
  fixes s
  notes [id_rules] = 
    itypeI[Pure.of s "TYPE(nat set)"]
  shows 
    "hn_refine (emp * hn_ctxt (hs.assn id_assn) s s') (?c1::?'c1 Heap) ?\<Gamma>1' ?R1 (bar s)"
    "hn_refine (emp * hn_ctxt (hs.assn id_assn) s s') (?c2::?'c2 Heap) ?\<Gamma>2' ?R2 (bar2 s)"
  unfolding bar_def bar2_def
  using [[id_debug]]
  by sepref+


term case_list
thm id_rules

lemmas [id_rules] = 
  itypeI[Pure.of RECT "TYPE ((('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b)"]
  itypeI[Pure.of case_list "TYPE('a \<Rightarrow> ('b \<Rightarrow> 'b list \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a)"]

ML \<open>
  fun is_eta_norm t = t aconv (Envir.eta_contract t)


  fun find_not_eta_norm (a$b) = (find_not_eta_norm a @ find_not_eta_norm b)
    | find_not_eta_norm (t as Abs (_,_,t'$Bound 0)) = t :: find_not_eta_norm t'
    | find_not_eta_norm (Abs (_,_,t)) = find_not_eta_norm t
    | find_not_eta_norm _ = []

  fun is_eta_norm_tac st = if is_eta_norm (Thm.prop_of st) then Seq.single st
    else (raise TERM ("\<not>eta-norm",find_not_eta_norm (Thm.prop_of st)))

\<close>


definition "xfoo \<equiv> do {
  s \<leftarrow> RETURN [1::nat];
  y \<leftarrow> RETURN ({}::nat set);
  RECT (\<lambda>D l. 
    case l of 
      [] \<Rightarrow> RETURN ({0})
    | x#l \<Rightarrow> do {
        r \<leftarrow> D l;
        RETURN (insert x r)
    }) s
  }
"

schematic_goal testsuite_basic1:
  notes [sepref_fr_rules] = HOL_list_empty_hnr hs.hnr_op_empty[of nat_assn] (* TODO: handle open relations *)
  shows "hn_refine emp (?c1::?'c1 Heap) ?\<Gamma>1' ?R1 bar'"
  and "hn_refine emp (?c2::?'c2 Heap) ?\<Gamma>2' ?R2 foo"
  and "hn_refine emp (?c3::?'c3 Heap) ?\<Gamma>3' ?R3 simple_rec"
  and "hn_refine emp (?c4::?'c4 Heap) ?\<Gamma>4' ?R4 lst_mem_to_sets"
  and "hn_refine emp (?c5::?'c5 Heap) ?\<Gamma>5' ?R5 lst_mem_to_sets_nonlin"
  (*and "hn_refine emp (?c6::?'c6 Heap) ?\<Gamma>6' ?R6 lst_mem_to_sets_nonlin2"*)
  and "hn_refine emp (?c7::?'c7 Heap) ?\<Gamma>7' ?R7 lst_nonlin"
  and "hn_refine emp (?c8::?'c8 Heap) ?\<Gamma>8' ?R8 lst_nonlin2"
  (*and "hn_refine emp (?c9::?'c9 Heap) ?\<Gamma>9' ?R9 lst_nonlin3"*)
  (*and "hn_refine emp (?ca::?'ca Heap) ?\<Gamma>a' ?Ra lst_nonlin4"*)
  unfolding bar'_def foo_def simple_rec_def lst_mem_to_sets_def 
    lst_mem_to_sets_nonlin_def lst_mem_to_sets_nonlin2_def
    lst_nonlin_def lst_nonlin2_def lst_nonlin3_def lst_nonlin4_def
  using [[goals_limit = 1]]
  apply sepref+
  done


schematic_goal testsuite_basic2:
  notes [sepref_fr_rules] = HOL_list_empty_hnr hs.hnr_op_empty hm.empty_hnr
  shows "hn_refine emp (?c1::?'c1 Heap) ?\<Gamma>1' ?R1 dup_arg"
  and "hn_refine emp (?c2::?'c2 Heap) ?\<Gamma>2' ?R2 big_list"
  and "hn_refine emp (?c3::?'c3 Heap) ?\<Gamma>3' ?R3 big_list2"
  and "hn_refine emp (?c4::?'c4 Heap) ?\<Gamma>4' ?R4 foo1"
  and "hn_refine emp (?c5::?'c5 Heap) ?\<Gamma>5' ?R5 basic_foreach"
  and "hn_refine emp (?c6::?'c6 Heap) ?\<Gamma>6' ?R6 basic_foreach2"
  and "hn_refine emp (?c7::?'c7 Heap) ?\<Gamma>7' ?R7 basic_option"
  and "hn_refine emp (?c8::?'c8 Heap) ?\<Gamma>8' ?R8 simple_while"
  unfolding dup_arg_def big_list_def big_list2_def foo1_def 
    basic_foreach_def basic_foreach2_def simple_while_def
    basic_option_def
  using [[goals_limit = 1, id_debug]]
  apply sepref+
  done

sepref_definition imp_dfs is "uncurry2 dfs" :: "((adjg_assn nat_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a prod_assn (hs.assn nat_assn) bool_assn)"
  unfolding dfs_def[abs_def] 
  apply (rewrite in "FOREACHc \<hole>" op_graph_succ_def[symmetric])
  apply (rewrite in "(\<hole>,_)" hs.fold_custom_empty)
  using [[goals_limit = 1]]
  by sepref

export_code imp_dfs checking SML_imp 

definition "simple_algo a c m x = do {
  let s = {m};
  RECT (\<lambda>D (x,s,l).
    if x\<in>s then RETURN l
    else D ((a*x+c) mod m,insert x s,l+1)
  ) (x::nat,s,0::nat)
}"

schematic_goal sa_impl:
  notes [autoref_tyrel] = ty_REL[where 'a = "nat set" 
    and R="\<langle>nat_rel\<rangle>iam_set_rel"]
  assumes [autoref_rules]: "(a,a)\<in>nat_rel" 
  assumes [autoref_rules]: "(c,c)\<in>nat_rel" 
  assumes [autoref_rules]: "(m,m)\<in>nat_rel" 
  assumes [autoref_rules]: "(x,x)\<in>nat_rel" 
  shows "(?c::?'c,simple_algo a c m x)\<in>?R"
  unfolding simple_algo_def[abs_def]
  using [[autoref_trace_failed_id]]
  apply autoref_monadic
  done

concrete_definition sa_impl uses sa_impl
prepare_code_thms sa_impl_def
export_code sa_impl checking SML

sepref_definition sai_impl is 
    "(uncurry2 (uncurry simple_algo))" 
  :: "(nat_assn\<^sup>k*\<^sub>anat_assn\<^sup>k*\<^sub>anat_assn\<^sup>k*\<^sub>anat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn)"
  unfolding simple_algo_def[abs_def]
  unfolding ias.fold_custom_empty
  using [[goals_limit = 1]]
  using [[id_debug]]
  by sepref
export_code sai_impl checking SML

term Array.upd

definition "sad_impl a c m x \<equiv> do {
  s\<leftarrow>Array.new m False;
  heap.fixp_fun (\<lambda>D (x,s,l). do {
    brk\<leftarrow>Array.nth s x;
    if brk then return l
    else do {
      _\<leftarrow>Array.len s;
      _\<leftarrow>if x<l then return True else return False; 
      s\<leftarrow>Array.upd x True s;
      D ((a*x+c) mod m,s,l+1)
    }
  }) (x,s,0::nat)
}"

definition "sad_impl2 a c m x \<equiv> do {
  s\<leftarrow>Array.new m False;
  heap.fixp_fun (\<lambda>D (x,l). do {
    brk\<leftarrow>Array.nth s x;
    if brk then return l
    else do {
      Array.upd x True s;
      D ((a*x+c) mod m,l+1)
    }
  }) (x,0::nat)
}"

prepare_code_thms sad_impl_def
prepare_code_thms sad_impl2_def

code_thms sai_impl 

lemma
 "ias_ins k a = do {
    l\<leftarrow>Array.len a;
    if k<l then 
      Array.upd k True a
    else do {
      let newsz = max (k+1) (2 * l + 3);
      a\<leftarrow>Array_Blit.array_grow a newsz False;
      Array.upd k True a
    }    
  }"
  unfolding ias_ins_def
  apply (fo_rule cong[OF arg_cong])
  apply (auto)
  done

export_code sa_impl sad_impl sad_impl2 sai_impl 
  checking SML_imp

schematic_goal
  shows "hn_refine emp (?c1::?'c1 Heap) ?\<Gamma>1' ?R1 
  (do {
    let x=(1::nat);
    RETURN {x,x}
  })"
  apply (rewrite in "RETURN \<hole>" hs.fold_custom_empty)
  apply sepref
  done

term hn_invalid


definition "remdup l \<equiv> 
  RECT (\<lambda>remdup. \<lambda>(
    [],s) \<Rightarrow> RETURN op_HOL_list_empty 
  | (x#xs,s) \<Rightarrow> if x\<in>s then 
      remdup (xs,s )
    else do {
      l \<leftarrow> remdup (xs, insert x s);
      RETURN (x#l)
    } 
  ) (l,op_hs_empty)
"

schematic_goal 
  fixes l :: "nat list"
  notes [id_rules] = itypeI[Pure.of l "TYPE(nat list)"]
  shows "hn_refine ( (hn_ctxt (list_assn (pure Id))) l li) (?c::?'c Heap) ?\<Gamma> ?R (remdup l)"
  unfolding remdup_def
  using [[id_debug]]
  by sepref
  


  text \<open>Test structural frame-inference and merging (on product type)\<close>

  definition "smart_match_test1 \<equiv> \<lambda>(p1,p2). RETURN (p1+p2)"

  sepref_definition smart_match_test1_impl is "smart_match_test1" :: "((prod_assn nat_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn)"
    unfolding smart_match_test1_def
    by sepref
  sepref_register smart_match_test1
  lemmas [sepref_fr_rules] = smart_match_test1_impl.refine

  definition "smart_match_test2 \<equiv> do {
    let p = (2::nat,2::nat);

    f \<leftarrow> if True then
      case p of (a,b) \<Rightarrow> RETURN (Some b)
    else  
      case p of (a,b) \<Rightarrow> RETURN (Some a);

    smart_match_test1 p
  }"

  sepref_thm smart_match_test2_impl is "uncurry0 smart_match_test2" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    unfolding smart_match_test2_def
    by sepref



  (* Regression from incomplete monadify, that could not not handle nested 
    plain operations that get converted to monadic operations. *)
  sepref_thm regr_incomplete_monadify is "RETURN o (\<lambda>l. fold (\<lambda>x. (#) (case x of (x, xa) \<Rightarrow> x + xa)) l [])" :: "(list_assn (prod_assn nat_assn nat_assn))\<^sup>k \<rightarrow>\<^sub>a list_assn nat_assn"
    unfolding test_def[abs_def] "HOL_list.fold_custom_empty"
    by sepref
  

end
(*>*)

