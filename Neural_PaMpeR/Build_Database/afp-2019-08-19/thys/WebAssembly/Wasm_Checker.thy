section \<open>Executable Type Checker\<close>

theory Wasm_Checker imports Wasm_Checker_Types begin

fun convert_cond :: "t \<Rightarrow> t \<Rightarrow> sx option \<Rightarrow> bool" where
  "convert_cond t1 t2 sx = ((t1 \<noteq> t2) \<and> (sx = None) = ((is_float_t t1 \<and> is_float_t t2)
                                                        \<or> (is_int_t t1 \<and> is_int_t t2 \<and> (t_length t1 < t_length t2))))"

fun same_lab_h :: "nat list \<Rightarrow> (t list) list \<Rightarrow> t list \<Rightarrow> (t list) option" where
  "same_lab_h [] _ ts = Some ts"
| "same_lab_h (i#is) lab_c ts = (if i \<ge> length lab_c
                                 then None
                                 else (if lab_c!i = ts
                                       then same_lab_h is lab_c (lab_c!i)
                                       else None))" 

fun same_lab :: "nat list \<Rightarrow> (t list) list \<Rightarrow> (t list) option" where
  "same_lab [] lab_c = None"
| "same_lab (i#is) lab_c = (if i \<ge> length lab_c
                            then None
                            else same_lab_h is lab_c (lab_c!i))"

lemma same_lab_h_conv_list_all:
  assumes "same_lab_h ils ls ts' = Some ts"
  shows "list_all (\<lambda>i. i < length ls \<and> ls!i = ts) ils \<and> ts' = ts"
  using assms
proof(induction ils)
  case (Cons a ils)
  thus ?case
    apply (simp,safe)
       apply (metis not_less option.distinct(1))+
    done
qed simp

lemma same_lab_conv_list_all:
  assumes "same_lab ils ls = Some ts"
  shows "list_all (\<lambda>i. i < length ls \<and> ls!i = ts) ils"
  using assms
proof (induction rule: same_lab.induct)
case (2 i "is" lab_c)
  thus ?case
    using same_lab_h_conv_list_all
    by (metis (mono_tags, lifting) list_all_simps(1) not_less option.distinct(1) same_lab.simps(2))
qed simp

lemma list_all_conv_same_lab_h:
  assumes "list_all (\<lambda>i. i < length ls \<and> ls!i = ts) ils"
  shows "same_lab_h ils ls ts = Some ts"
  using assms
  by (induction ils, simp_all)

lemma list_all_conv_same_lab:
  assumes "list_all (\<lambda>i. i < length ls \<and>ls!i = ts) (is@[i])"
  shows "same_lab (is@[i]) ls = Some ts"                      
  using assms
proof (induction "(is@[i])")
  case (Cons a x)
  thus ?case
    using list_all_conv_same_lab_h[OF Cons(3)]
    by (metis option.distinct(1) same_lab.simps(2) same_lab_h.simps(2))
qed auto
    
fun b_e_type_checker :: "t_context \<Rightarrow>  b_e list \<Rightarrow> tf \<Rightarrow> bool"
and check :: "t_context \<Rightarrow> b_e list \<Rightarrow> checker_type \<Rightarrow> checker_type"
and check_single :: "t_context \<Rightarrow>  b_e \<Rightarrow> checker_type \<Rightarrow> checker_type" where
  "b_e_type_checker \<C> es (tn _> tm) = c_types_agree (check \<C> es (Type tn)) tm"
| "check \<C> es ts = (case es of
                     [] \<Rightarrow> ts
                   | (e#es) \<Rightarrow> (case ts of 
                                  Bot \<Rightarrow> Bot
                                | _ \<Rightarrow> check \<C> es (check_single \<C> e ts)))"
(*
foldl (\<lambda> ts e. (case ts of Bot \<Rightarrow> Bot | _ \<Rightarrow> check_single \<C> e ts)) es



primrec foldl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
foldl_Nil:  "foldl f a [] = a" |
foldl_Cons: "foldl f a (x # xs) = foldl f (f a x) xs"
*)
  (* num ops *)
| "check_single \<C> (C v) ts = type_update ts [] (Type [typeof v])"
| "check_single \<C> (Unop_i t _) ts = (if is_int_t t
                                       then type_update ts [TSome t] (Type [t])
                                       else Bot)"
| "check_single \<C> (Unop_f t _) ts = (if is_float_t t
                                       then type_update ts [TSome t] (Type [t])
                                       else Bot)"
| "check_single \<C> (Binop_i t _) ts = (if is_int_t t
                                       then type_update ts [TSome t, TSome t] (Type [t])
                                       else Bot)"
| "check_single \<C> (Binop_f t _) ts = (if is_float_t t
                                       then type_update ts [TSome t, TSome t] (Type [t])
                                       else Bot)"
| "check_single \<C> (Testop t _) ts = (if is_int_t t
                                       then type_update ts [TSome t] (Type [T_i32])
                                       else Bot)"
| "check_single \<C> (Relop_i t _) ts = (if is_int_t t
                                       then type_update ts [TSome t, TSome t] (Type [T_i32])
                                       else Bot)"
| "check_single \<C> (Relop_f t _) ts =  (if is_float_t t
                                       then type_update ts [TSome t, TSome t] (Type [T_i32])
                                       else Bot)"
  (* convert *)
| "check_single \<C> (Cvtop t1 Convert t2 sx) ts = (if (convert_cond t1 t2 sx)
                                                   then type_update ts [TSome t2] (Type [t1])
                                                   else Bot)"
  (* reinterpret *)
| "check_single \<C> (Cvtop t1 Reinterpret t2 sx) ts = (if ((t1 \<noteq> t2) \<and> t_length t1 = t_length t2 \<and> sx = None)
                                                         then type_update ts [TSome t2] (Type [t1])
                                                         else Bot)"
  (* unreachable, nop, drop, select *)
| "check_single \<C> (Unreachable) ts = type_update ts [] (TopType [])"
| "check_single \<C> (Nop) ts = ts"
| "check_single \<C> (Drop) ts = type_update ts [TAny] (Type [])"
| "check_single \<C> (Select) ts = type_update_select ts"
  (* block *)                                 
| "check_single \<C> (Block (tn _> tm) es) ts = (if (b_e_type_checker (\<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr>) es (tn _> tm))
                                                then type_update ts (to_ct_list tn) (Type tm)
                                                else Bot)"
  (* loop *)
| "check_single \<C> (Loop (tn _> tm) es) ts = (if (b_e_type_checker (\<C>\<lparr>label := ([tn] @ (label \<C>))\<rparr>) es (tn _> tm))
                                                then type_update ts (to_ct_list tn) (Type tm)
                                                else Bot)"
  (* if *)
| "check_single \<C> (If (tn _> tm) es1 es2) ts = (if (b_e_type_checker (\<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr>) es1 (tn _> tm)
                                                    \<and> b_e_type_checker (\<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr>) es2 (tn _> tm))
                                                then type_update ts (to_ct_list (tn@[T_i32])) (Type tm)
                                                else Bot)"
  (* br *)
| "check_single \<C> (Br i) ts = (if i < length (label \<C>)
                                 then type_update ts (to_ct_list ((label \<C>)!i)) (TopType [])
                                 else Bot)"
  (* br_if *)
| "check_single \<C> (Br_if i) ts = (if i < length (label \<C>)
                                    then type_update ts (to_ct_list ((label \<C>)!i @ [T_i32])) (Type ((label \<C>)!i))
                                    else Bot)"
  (* br_table *)
| "check_single \<C> (Br_table is i) ts = (case (same_lab (is@[i]) (label \<C>)) of
                                        None \<Rightarrow> Bot
                                      | Some tls \<Rightarrow> type_update ts (to_ct_list (tls @ [T_i32])) (TopType []))"
  (* return *)
| "check_single \<C> (Return) ts = (case (return \<C>) of
                                   None \<Rightarrow> Bot
                                 | Some tls \<Rightarrow> type_update ts (to_ct_list tls) (TopType []))"
  (* call *)
| "check_single \<C> (Call i) ts = (if i < length (func_t \<C>)
                                    then (case ((func_t \<C>)!i) of
                                            (tn _> tm) \<Rightarrow> type_update ts (to_ct_list tn) (Type tm))
                                    else Bot)"
  (* call_indirect *)
| "check_single \<C> (Call_indirect i) ts = (if (table \<C>) \<noteq> None \<and> i < length (types_t \<C>)
                                            then (case ((types_t \<C>)!i) of
                                                    (tn _> tm) \<Rightarrow> type_update ts (to_ct_list (tn@[T_i32])) (Type tm))
                                            else Bot)"
  (* get_local *)
| "check_single \<C> (Get_local i) ts = (if i < length (local \<C>)
                                        then type_update ts [] (Type [(local \<C>)!i])
                                        else Bot)"
  (* set_local *)
| "check_single \<C> (Set_local i) ts = (if i < length (local \<C>)
                                        then type_update ts [TSome ((local \<C>)!i)] (Type [])
                                        else Bot)"
  (* tee_local *)
| "check_single \<C> (Tee_local i) ts = (if i < length (local \<C>)
                                 then type_update ts [TSome ((local \<C>)!i)] (Type [(local \<C>)!i])
                                 else Bot)"
  (* get_global *)
| "check_single \<C> (Get_global i) ts = (if i < length (global \<C>)
                                         then type_update ts [] (Type [tg_t ((global \<C>)!i)])
                                         else Bot)"
  (* set_global *)
| "check_single \<C> (Set_global i) ts = (if i < length (global \<C>) \<and> is_mut (global \<C> ! i)
                                         then type_update ts [TSome (tg_t ((global \<C>)!i))] (Type [])
                                         else Bot)"
  (* load *)
| "check_single \<C> (Load t tp_sx a off) ts = (if (memory \<C>) \<noteq> None \<and> load_store_t_bounds a (option_projl tp_sx) t
                                 then type_update ts [TSome T_i32] (Type [t])
                                 else Bot)"
  (* store *)
| "check_single \<C> (Store t tp a off) ts = (if (memory \<C>) \<noteq> None \<and> load_store_t_bounds a tp t
                                             then type_update ts [TSome T_i32,TSome t] (Type [])
                                             else Bot)"
  (* current_memory *)
| "check_single \<C> Current_memory ts = (if (memory \<C>) \<noteq> None
                                         then type_update ts [] (Type [T_i32])
                                         else Bot)"
  (* grow_memory *)
| "check_single \<C> Grow_memory ts = (if (memory \<C>) \<noteq> None
                                      then type_update ts [TSome T_i32] (Type [T_i32])
                                      else Bot)"

end
