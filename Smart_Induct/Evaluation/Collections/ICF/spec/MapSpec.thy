(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section \<open>\isaheader{Specification of Maps}\<close>
theory MapSpec
imports ICF_Spec_Base
begin
text_raw\<open>\label{thy:MapSpec}\<close>

(*@intf Map
  @abstype 'k\<rightharpoonup>'v
  This interface specifies maps from keys to values.
*)

text \<open>
  This theory specifies map operations by means of mapping to
  HOL's map type, i.e. @{typ "'k \<rightharpoonup> 'v"}.
\<close>

type_synonym ('k,'v,'s) map_\<alpha> = "'s \<Rightarrow> 'k \<rightharpoonup> 'v"
type_synonym ('k,'v,'s) map_invar = "'s \<Rightarrow> bool"
locale map = 
  fixes \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"                 \<comment> \<open>Abstraction to map datatype\<close>
  fixes invar :: "'s \<Rightarrow> bool"                 \<comment> \<open>Invariant\<close>

locale map_no_invar = map +
  assumes invar[simp, intro!]: "\<And>s. invar s"

subsection "Basic Map Functions"

subsubsection "Empty Map"
type_synonym ('k,'v,'s) map_empty = "unit \<Rightarrow> 's"
locale map_empty = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes empty :: "unit \<Rightarrow> 's"
  assumes empty_correct:
    "\<alpha> (empty ()) = Map.empty"
    "invar (empty ())"

subsubsection "Lookup"
type_synonym ('k,'v,'s) map_lookup = "'k \<Rightarrow> 's \<Rightarrow> 'v option"
locale map_lookup = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes lookup :: "'u \<Rightarrow> 's \<Rightarrow> 'v option"
  assumes lookup_correct:
    "invar m \<Longrightarrow> lookup k m = \<alpha> m k"

subsubsection "Update"
type_synonym ('k,'v,'s) map_update = "'k \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's"
locale map_update = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes update :: "'u \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's"
  assumes update_correct:
    "invar m \<Longrightarrow> \<alpha> (update k v m) = (\<alpha> m)(k \<mapsto> v)"
    "invar m \<Longrightarrow> invar (update k v m)"

subsubsection "Disjoint Update"
type_synonym ('k,'v,'s) map_update_dj = "'k \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's"
locale map_update_dj = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes update_dj :: "'u \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's"
  assumes update_dj_correct: 
    "\<lbrakk>invar m; k\<notin>dom (\<alpha> m)\<rbrakk> \<Longrightarrow> \<alpha> (update_dj k v m) = (\<alpha> m)(k \<mapsto> v)"
    "\<lbrakk>invar m; k\<notin>dom (\<alpha> m)\<rbrakk> \<Longrightarrow> invar (update_dj k v m)"

 
subsubsection "Delete"
type_synonym ('k,'v,'s) map_delete = "'k \<Rightarrow> 's \<Rightarrow> 's"
locale map_delete = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes delete :: "'u \<Rightarrow> 's \<Rightarrow> 's"
  assumes delete_correct: 
    "invar m \<Longrightarrow> \<alpha> (delete k m) = (\<alpha> m) |` (-{k})"
    "invar m \<Longrightarrow> invar (delete k m)"

subsubsection "Add"
type_synonym ('k,'v,'s) map_add = "'s \<Rightarrow> 's \<Rightarrow> 's"
locale map_add = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes add :: "'s \<Rightarrow> 's \<Rightarrow> 's"
  assumes add_correct:
    "invar m1 \<Longrightarrow> invar m2 \<Longrightarrow> \<alpha> (add m1 m2) = \<alpha> m1 ++ \<alpha> m2"
    "invar m1 \<Longrightarrow> invar m2 \<Longrightarrow> invar (add m1 m2)"

type_synonym ('k,'v,'s) map_add_dj = "'s \<Rightarrow> 's \<Rightarrow> 's"
locale map_add_dj = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes add_dj :: "'s \<Rightarrow> 's \<Rightarrow> 's"
  assumes add_dj_correct:
    "\<lbrakk>invar m1; invar m2; dom (\<alpha> m1) \<inter> dom (\<alpha> m2) = {}\<rbrakk> \<Longrightarrow> \<alpha> (add_dj m1 m2) = \<alpha> m1 ++ \<alpha> m2"
    "\<lbrakk>invar m1; invar m2; dom (\<alpha> m1) \<inter> dom (\<alpha> m2) = {} \<rbrakk> \<Longrightarrow> invar (add_dj m1 m2)"

subsubsection "Emptiness Check"
type_synonym ('k,'v,'s) map_isEmpty = "'s \<Rightarrow> bool"
locale map_isEmpty = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes isEmpty :: "'s \<Rightarrow> bool"
  assumes isEmpty_correct : "invar m \<Longrightarrow> isEmpty m \<longleftrightarrow> \<alpha> m = Map.empty"

subsubsection "Singleton Maps"
type_synonym ('k,'v,'s) map_sng = "'k \<Rightarrow> 'v \<Rightarrow> 's"
locale map_sng = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes sng :: "'u \<Rightarrow> 'v \<Rightarrow> 's"
  assumes sng_correct : 
    "\<alpha> (sng k v) = [k \<mapsto> v]"
    "invar (sng k v)"

type_synonym ('k,'v,'s) map_isSng = "'s \<Rightarrow> bool"
locale map_isSng = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'k \<rightharpoonup> 'v"
  fixes isSng :: "'s \<Rightarrow> bool"
  assumes isSng_correct:
    "invar s \<Longrightarrow> isSng s \<longleftrightarrow> (\<exists>k v. \<alpha> s = [k \<mapsto> v])"
begin
  lemma isSng_correct_exists1 :
    "invar s \<Longrightarrow> (isSng s \<longleftrightarrow> (\<exists>!k. \<exists>v. (\<alpha> s k = Some v)))"
    apply (auto simp add: isSng_correct split: if_split_asm)
    apply (rule_tac x=k in exI)
    apply (rule_tac x=v in exI)
    apply (rule ext)
    apply (case_tac "\<alpha> s x")
    apply auto
    apply force
    done

  lemma isSng_correct_card :
    "invar s \<Longrightarrow> (isSng s \<longleftrightarrow> (card (dom (\<alpha> s)) = 1))"
    by (auto simp add: isSng_correct card_Suc_eq dom_eq_singleton_conv)

end

subsubsection "Finite Maps"
locale finite_map = map +
  assumes finite[simp, intro!]: "invar m \<Longrightarrow> finite (dom (\<alpha> m))"

subsubsection "Size"
type_synonym ('k,'v,'s) map_size = "'s \<Rightarrow> nat"
locale map_size = finite_map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes size :: "'s \<Rightarrow> nat"
  assumes size_correct: "invar s \<Longrightarrow> size s = card (dom (\<alpha> s))"
  
type_synonym ('k,'v,'s) map_size_abort = "nat \<Rightarrow> 's \<Rightarrow> nat"
locale map_size_abort = finite_map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes size_abort :: "nat \<Rightarrow> 's \<Rightarrow> nat"
  assumes size_abort_correct: "invar s \<Longrightarrow> size_abort m s = min m (card (dom (\<alpha> s)))"

subsubsection "Iterators"
text \<open>
  An iteration combinator over a map applies a function to a state for each 
  map entry, in arbitrary order.
  Proving of properties is done by invariant reasoning.
  An iterator can also contain a continuation condition. Iteration is
  interrupted if the condition becomes false.
\<close>

(* Deprecated *)
(*locale map_iteratei = finite_map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes iteratei :: "'s \<Rightarrow> ('u \<times> 'v,'\<sigma>) set_iterator"

  assumes iteratei_rule: "invar m \<Longrightarrow> map_iterator (iteratei m) (\<alpha> m)"
begin
  lemma iteratei_rule_P:
    assumes "invar m"
        and I0: "I (dom (\<alpha> m)) \<sigma>0"
        and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> it; \<alpha> m k = Some v; it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
                    \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
        and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
        and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom (\<alpha> m); it \<noteq> {}; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iteratei m c f \<sigma>0)"
    using map_iterator_rule_P [OF iteratei_rule, of m I \<sigma>0 c f P]
    by (simp_all add: assms)

  lemma iteratei_rule_insert_P:
    assumes  
      "invar m" 
      "I {} \<sigma>0"
      "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> (dom (\<alpha> m) - it); \<alpha> m k = Some v; it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
          \<Longrightarrow> I (insert k it) (f (k, v) \<sigma>)"
      "!!\<sigma>. I (dom (\<alpha> m)) \<sigma> \<Longrightarrow> P \<sigma>"
      "!!\<sigma> it. \<lbrakk> it \<subseteq> dom (\<alpha> m); it \<noteq> dom (\<alpha> m); 
               \<not> (c \<sigma>); 
               I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iteratei m c f \<sigma>0)"
    using map_iterator_rule_insert_P [OF iteratei_rule, of m I \<sigma>0 c f P]
    by (simp_all add: assms)

  lemma iterate_rule_P:
    "\<lbrakk>
      invar m;
      I (dom (\<alpha> m)) \<sigma>0;
      !!k v it \<sigma>. \<lbrakk> k \<in> it; \<alpha> m k = Some v; it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
                  \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>);
      !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei m (\<lambda>_. True) f \<sigma>0)"
    using iteratei_rule_P [of m I \<sigma>0 "\<lambda>_. True" f P]
    by fast

  lemma iterate_rule_insert_P:
    "\<lbrakk>
      invar m;
      I {} \<sigma>0;
      !!k v it \<sigma>. \<lbrakk> k \<in> (dom (\<alpha> m) - it); \<alpha> m k = Some v; it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
                  \<Longrightarrow> I (insert k it) (f (k, v) \<sigma>);
      !!\<sigma>. I (dom (\<alpha> m)) \<sigma> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei m (\<lambda>_. True) f \<sigma>0)"
    using iteratei_rule_insert_P [of m I \<sigma>0 "\<lambda>_. True" f P]
    by fast
end

lemma map_iteratei_I :
  assumes "\<And>m. invar m \<Longrightarrow> map_iterator (iti m) (\<alpha> m)"
  shows "map_iteratei \<alpha> invar iti"
proof
  fix m 
  assume invar_m: "invar m"
  from assms(1)[OF invar_m] show it_OK: "map_iterator (iti m) (\<alpha> m)" .
  
  from set_iterator_genord.finite_S0 [OF it_OK[unfolded set_iterator_def]]
  show "finite (dom (\<alpha> m))" by (simp add: finite_map_to_set) 
qed
*)

type_synonym ('k,'v,'s) map_list_it
  = "'s \<Rightarrow> ('k\<times>'v,('k\<times>'v) list) set_iterator"
locale poly_map_iteratei_defs =
  fixes list_it :: "'s \<Rightarrow> ('u\<times>'v,('u\<times>'v) list) set_iterator"
begin
  definition iteratei :: "'s \<Rightarrow> ('u\<times>'v,'\<sigma>) set_iterator"
    where "iteratei S \<equiv> it_to_it (list_it S)"

  abbreviation "iterate m \<equiv> iteratei m (\<lambda>_. True)"
end

locale poly_map_iteratei =
  finite_map + poly_map_iteratei_defs list_it
  for list_it :: "'s \<Rightarrow> ('u\<times>'v,('u\<times>'v) list) set_iterator" +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  assumes list_it_correct: "invar m \<Longrightarrow> map_iterator (list_it m) (\<alpha> m)"
begin
  lemma iteratei_correct: "invar S \<Longrightarrow> map_iterator (iteratei S) (\<alpha> S)"
    unfolding iteratei_def
    apply (rule it_to_it_correct)
    by (rule list_it_correct)

  lemma pi_iteratei[icf_proper_iteratorI]: 
    "proper_it (iteratei S) (iteratei S)"
    unfolding iteratei_def 
    by (intro icf_proper_iteratorI)

  lemma iteratei_rule_P:
    assumes "invar m"
    and I0: "I (map_to_set (\<alpha> m)) \<sigma>0"
    and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; (k,v) \<in> it; it \<subseteq> map_to_set (\<alpha> m); I it \<sigma> \<rbrakk> 
      \<Longrightarrow> I (it - {(k,v)}) (f (k, v) \<sigma>)"
    and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> map_to_set (\<alpha> m); it \<noteq> {}; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iteratei m c f \<sigma>0)"
    apply (rule set_iterator_rule_P[OF iteratei_correct])
    apply fact
    apply fact
    apply (case_tac x, simp add: IP)
    apply fact
    apply fact
    done

  lemma iteratei_rule_insert_P:
    assumes "invar m" 
    and "I {} \<sigma>0"
    and "!!k v it \<sigma>. \<lbrakk> c \<sigma>; (k,v) \<in> (map_to_set (\<alpha> m) - it); 
                       it \<subseteq> map_to_set (\<alpha> m); I it \<sigma> \<rbrakk> 
      \<Longrightarrow> I (insert (k,v) it) (f (k, v) \<sigma>)"
    and "!!\<sigma>. I (map_to_set (\<alpha> m)) \<sigma> \<Longrightarrow> P \<sigma>"
    and "!!\<sigma> it. \<lbrakk> it \<subseteq> map_to_set (\<alpha> m); it \<noteq> map_to_set (\<alpha> m); 
                  \<not> (c \<sigma>); 
                  I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iteratei m c f \<sigma>0)"
    apply (rule set_iterator_rule_insert_P[OF iteratei_correct])
    apply fact
    apply fact
    apply (case_tac x, simp add: assms)
    apply fact
    apply fact
    done

  lemma iterate_rule_P:
    assumes "invar m"
    and I0: "I (map_to_set (\<alpha> m)) \<sigma>0"
    and IP: "!!k v it \<sigma>. \<lbrakk> (k,v) \<in> it; it \<subseteq> map_to_set (\<alpha> m); I it \<sigma> \<rbrakk> 
      \<Longrightarrow> I (it - {(k,v)}) (f (k, v) \<sigma>)"
    and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    shows "P (iterate m f \<sigma>0)"
    apply (rule iteratei_rule_P)
    apply fact
    apply (rule I0)
    apply (rule IP, assumption+) []
    apply (rule IF, assumption)
    apply simp
    done

  lemma iterate_rule_insert_P:
    assumes "invar m" 
    and I0: "I {} \<sigma>0"
    and "!!k v it \<sigma>. \<lbrakk> (k,v) \<in> (map_to_set (\<alpha> m) - it); 
                       it \<subseteq> map_to_set (\<alpha> m); I it \<sigma> \<rbrakk> 
      \<Longrightarrow> I (insert (k,v) it) (f (k, v) \<sigma>)"
    and "!!\<sigma>. I (map_to_set (\<alpha> m)) \<sigma> \<Longrightarrow> P \<sigma>"
    shows "P (iterate m f \<sigma>0)"
    apply (rule iteratei_rule_insert_P)
    apply fact
    apply (rule I0)
    apply (rule assms, assumption+) []
    apply (rule assms, assumption)
    apply simp
    done
    
  lemma old_iteratei_rule_P:
    assumes "invar m"
    and I0: "I (dom (\<alpha> m)) \<sigma>0"
    and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> it; \<alpha> m k = Some v; it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
      \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
    and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom (\<alpha> m); it \<noteq> {}; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iteratei m c f \<sigma>0)"
    using assms
    by (rule map_iterator_rule_P[OF iteratei_correct])

  lemma old_iteratei_rule_insert_P:
    assumes "invar m" 
    and "I {} \<sigma>0"
    and "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> (dom (\<alpha> m) - it); \<alpha> m k = Some v; 
                       it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
      \<Longrightarrow> I (insert k it) (f (k, v) \<sigma>)"
    and "!!\<sigma>. I (dom (\<alpha> m)) \<sigma> \<Longrightarrow> P \<sigma>"
    and "!!\<sigma> it. \<lbrakk> it \<subseteq> dom (\<alpha> m); it \<noteq> dom (\<alpha> m); 
                  \<not> (c \<sigma>); 
                  I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iteratei m c f \<sigma>0)"
    using assms by (rule map_iterator_rule_insert_P[OF iteratei_correct])

  lemma old_iterate_rule_P:
    "\<lbrakk>
      invar m;
      I (dom (\<alpha> m)) \<sigma>0;
      !!k v it \<sigma>. \<lbrakk> k \<in> it; \<alpha> m k = Some v; it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
                  \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>);
      !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iterate m f \<sigma>0)"
    using old_iteratei_rule_P [of m I \<sigma>0 "\<lambda>_. True" f P]
    by blast

  lemma old_iterate_rule_insert_P:
    "\<lbrakk>
      invar m;
      I {} \<sigma>0;
      !!k v it \<sigma>. \<lbrakk> k \<in> (dom (\<alpha> m) - it); \<alpha> m k = Some v; 
                    it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
                  \<Longrightarrow> I (insert k it) (f (k, v) \<sigma>);
      !!\<sigma>. I (dom (\<alpha> m)) \<sigma> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei m (\<lambda>_. True) f \<sigma>0)"
    using old_iteratei_rule_insert_P [of m I \<sigma>0 "\<lambda>_. True" f P]
    by blast

  end


subsubsection "Bounded Quantification"
type_synonym ('k,'v,'s) map_ball = "'s \<Rightarrow> ('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> bool"
locale map_ball = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes ball :: "'s \<Rightarrow> ('u \<times> 'v \<Rightarrow> bool) \<Rightarrow> bool"
  assumes ball_correct: "invar m \<Longrightarrow> ball m P \<longleftrightarrow> (\<forall>u v. \<alpha> m u = Some v \<longrightarrow> P (u, v))"

type_synonym ('k,'v,'s) map_bex = "'s \<Rightarrow> ('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> bool"
locale map_bex = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes bex :: "'s \<Rightarrow> ('u \<times> 'v \<Rightarrow> bool) \<Rightarrow> bool"
  assumes bex_correct: 
    "invar m \<Longrightarrow> bex m P \<longleftrightarrow> (\<exists>u v. \<alpha> m u = Some v \<and> P (u, v))"


subsubsection "Selection of Entry"
type_synonym ('k,'v,'s,'r) map_sel = "'s \<Rightarrow> ('k \<times> 'v \<Rightarrow> 'r option) \<Rightarrow> 'r option"
locale map_sel = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes sel :: "'s \<Rightarrow> ('u \<times> 'v \<Rightarrow> 'r option) \<Rightarrow> 'r option"
  assumes selE: 
  "\<lbrakk> invar m; \<alpha> m u = Some v; f (u, v) = Some r; 
     !!u v r. \<lbrakk> sel m f = Some r; \<alpha> m u = Some v; f (u, v) = Some r \<rbrakk> \<Longrightarrow> Q 
   \<rbrakk> \<Longrightarrow> Q"
  assumes selI: 
    "\<lbrakk> invar m; \<forall>u v. \<alpha> m u = Some v \<longrightarrow> f (u, v) = None \<rbrakk> \<Longrightarrow> sel m f = None"

begin
  lemma sel_someE: 
    "\<lbrakk> invar m; sel m f = Some r; 
       !!u v. \<lbrakk> \<alpha> m u = Some v; f (u, v) = Some r \<rbrakk> \<Longrightarrow> P
     \<rbrakk> \<Longrightarrow> P"
    apply (cases "\<exists>u v r. \<alpha> m u = Some v \<and> f (u, v) = Some r")
    apply safe
    apply (erule_tac u=u and v=v and r=ra in selE)
    apply assumption
    apply assumption
    apply simp
    apply (auto)
    apply (drule (1) selI)
    apply simp
    done

  lemma sel_noneD: "\<lbrakk>invar m; sel m f = None; \<alpha> m u = Some v\<rbrakk> \<Longrightarrow> f (u, v) = None"
    apply (rule ccontr)
    apply simp
    apply (erule exE)
    apply (erule_tac f=f and u=u and v=v and r=y in selE)
    apply auto
    done

end

  \<comment> \<open>Equivalent description of sel-map properties\<close>
lemma map_sel_altI:
  assumes S1: 
    "!!s f r P. \<lbrakk> invar s; sel s f = Some r; 
                  !!u v. \<lbrakk>\<alpha> s u = Some v; f (u, v) = Some r\<rbrakk> \<Longrightarrow> P
                \<rbrakk> \<Longrightarrow> P"
  assumes S2: 
    "!!s f u v. \<lbrakk>invar s; sel s f = None; \<alpha> s u = Some v\<rbrakk> \<Longrightarrow> f (u, v) = None"
  shows "map_sel \<alpha> invar sel"
proof -
  show ?thesis
    apply (unfold_locales)
    apply (case_tac "sel m f")
    apply (force dest: S2)
    apply (force elim: S1)
    apply (case_tac "sel m f")
    apply assumption
    apply (force elim: S1)
    done
qed


subsubsection "Selection of Entry (without mapping)"
type_synonym ('k,'v,'s) map_sel' = "'s \<Rightarrow> ('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> ('k\<times>'v) option"
locale map_sel' = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes sel' :: "'s \<Rightarrow> ('u \<times> 'v \<Rightarrow> bool) \<Rightarrow> ('u\<times>'v) option"
  assumes sel'E: 
  "\<lbrakk> invar m; \<alpha> m u = Some v; P (u, v); 
     !!u v. \<lbrakk> sel' m P = Some (u,v); \<alpha> m u = Some v; P (u, v)\<rbrakk> \<Longrightarrow> Q 
   \<rbrakk> \<Longrightarrow> Q"
  assumes sel'I: 
    "\<lbrakk> invar m; \<forall>u v. \<alpha> m u = Some v \<longrightarrow> \<not> P (u, v) \<rbrakk> \<Longrightarrow> sel' m P = None"

begin
  lemma sel'_someE: 
    "\<lbrakk> invar m; sel' m P = Some (u,v); 
       !!u v. \<lbrakk> \<alpha> m u = Some v; P (u, v) \<rbrakk> \<Longrightarrow> thesis
     \<rbrakk> \<Longrightarrow> thesis"
    apply (cases "\<exists>u v. \<alpha> m u = Some v \<and> P (u, v)")
    apply safe
    apply (erule_tac u=ua and v=va in sel'E)
    apply assumption
    apply assumption
    apply simp
    apply (auto)
    apply (drule (1) sel'I)
    apply simp
    done

  lemma sel'_noneD: "\<lbrakk>invar m; sel' m P = None; \<alpha> m u = Some v\<rbrakk> \<Longrightarrow> \<not> P (u, v)"
    apply (rule ccontr)
    apply simp
    apply (erule (2) sel'E[where P=P])
    apply auto
    done

  lemma sel'_SomeD:
    "\<lbrakk> sel' m P = Some (u, v); invar m \<rbrakk> \<Longrightarrow> \<alpha> m u = Some v \<and> P (u, v)"
    apply(cases "\<exists>u' v'. \<alpha> m u' = Some v' \<and> P (u', v')")
     apply clarsimp
     apply(erule (2) sel'E[where P=P])
     apply simp
    apply(clarsimp)
    apply(drule (1) sel'I)
    apply simp
    done
end

subsubsection "Map to List Conversion"
type_synonym ('k,'v,'s) map_to_list = "'s \<Rightarrow> ('k\<times>'v) list"
locale map_to_list = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes to_list :: "'s \<Rightarrow> ('u\<times>'v) list"
  assumes to_list_correct: 
    "invar m \<Longrightarrow> map_of (to_list m) = \<alpha> m"
    "invar m \<Longrightarrow> distinct (map fst (to_list m))"


subsubsection "List to Map Conversion"
type_synonym ('k,'v,'s) list_to_map = "('k\<times>'v) list \<Rightarrow> 's"
locale list_to_map = map +
  constrains \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes to_map :: "('u\<times>'v) list \<Rightarrow> 's"
  assumes to_map_correct:
    "\<alpha> (to_map l) = map_of l"
    "invar (to_map l)"

subsubsection "Image of a Map"

text \<open>This locale allows to apply a function to both the keys and
 the values of a map while at the same time filtering entries.\<close>

definition transforms_to_unique_keys ::
  "('u1 \<rightharpoonup> 'v1) \<Rightarrow> ('u1 \<times> 'v1 \<rightharpoonup> ('u2 \<times> 'v2)) \<Rightarrow> bool"
  where
  "transforms_to_unique_keys m f \<equiv> (\<forall>k1 k2 v1 v2 k' v1' v2'. ( 
         m k1 = Some v1 \<and>
         m k2 = Some v2 \<and>
         f (k1, v1) = Some (k', v1') \<and>
         f (k2, v2) = Some (k', v2')) -->
       (k1 = k2))"

type_synonym ('k1,'v1,'m1,'k2,'v2,'m2) map_image_filter  
  = "('k1 \<times> 'v1 \<Rightarrow> ('k2 \<times> 'v2) option) \<Rightarrow> 'm1 \<Rightarrow> 'm2"

locale map_image_filter = m1: map \<alpha>1 invar1 + m2: map \<alpha>2 invar2
  for \<alpha>1 :: "'m1 \<Rightarrow> 'u1 \<rightharpoonup> 'v1" and invar1
  and \<alpha>2 :: "'m2 \<Rightarrow> 'u2 \<rightharpoonup> 'v2" and invar2
  +
  fixes map_image_filter :: "('u1 \<times> 'v1 \<Rightarrow> ('u2 \<times> 'v2) option) \<Rightarrow> 'm1 \<Rightarrow> 'm2"
  assumes map_image_filter_correct_aux1:
    "\<And>k' v'. 
     \<lbrakk>invar1 m; transforms_to_unique_keys (\<alpha>1 m) f\<rbrakk> \<Longrightarrow> 
     (invar2 (map_image_filter f m) \<and>
      ((\<alpha>2 (map_image_filter f m) k' = Some v') \<longleftrightarrow>
       (\<exists>k v. (\<alpha>1 m k = Some v) \<and> f (k, v) = Some (k', v'))))"
begin

  (*Let's use a definition for the precondition *)

  lemma map_image_filter_correct_aux2 :
    assumes "invar1 m" 
      and "transforms_to_unique_keys (\<alpha>1 m) f"
    shows "(\<alpha>2 (map_image_filter f m) k' = None) \<longleftrightarrow>
      (\<forall>k v v'. \<alpha>1 m k = Some v \<longrightarrow> f (k, v) \<noteq> Some (k', v'))"
  proof -
    note map_image_filter_correct_aux1 [OF assms]
    have Some_eq: "\<And>v'. (\<alpha>2 (map_image_filter f m) k' = Some v') =
          (\<exists>k v. \<alpha>1 m k = Some v \<and> f (k, v) = Some (k', v'))"
      by (simp add: map_image_filter_correct_aux1 [OF assms])
    
    have intro_some: "(\<alpha>2 (map_image_filter f m) k' = None) \<longleftrightarrow>
                      (\<forall>v'. \<alpha>2 (map_image_filter f m) k' \<noteq> Some v')" by auto
    
    from intro_some Some_eq show ?thesis by auto
  qed

  lemmas map_image_filter_correct = 
     conjunct1 [OF map_image_filter_correct_aux1] 
     conjunct2 [OF map_image_filter_correct_aux1] 
     map_image_filter_correct_aux2
end
    

text \<open>Most of the time the mapping function is only applied to values. Then,
  the precondition disapears.\<close>
type_synonym ('k,'v1,'m1,'k2,'v2,'m2) map_value_image_filter  
  = "('k \<Rightarrow> 'v1 \<Rightarrow> 'v2 option) \<Rightarrow> 'm1 \<Rightarrow> 'm2"

locale map_value_image_filter = m1: map \<alpha>1 invar1 + m2: map \<alpha>2 invar2
  for \<alpha>1 :: "'m1 \<Rightarrow> 'u \<rightharpoonup> 'v1" and invar1
  and \<alpha>2 :: "'m2 \<Rightarrow> 'u \<rightharpoonup> 'v2" and invar2
  +
  fixes map_value_image_filter :: "('u \<Rightarrow> 'v1 \<Rightarrow> 'v2 option) \<Rightarrow> 'm1 \<Rightarrow> 'm2"
  assumes map_value_image_filter_correct_aux:
    "invar1 m \<Longrightarrow> 
     invar2 (map_value_image_filter f m) \<and>
     (\<alpha>2 (map_value_image_filter f m) = 
      (\<lambda>k. Option.bind (\<alpha>1 m k) (f k)))"
begin

  lemmas map_value_image_filter_correct =
    conjunct1[OF map_value_image_filter_correct_aux]
    conjunct2[OF map_value_image_filter_correct_aux]


  lemma map_value_image_filter_correct_alt :
    "invar1 m \<Longrightarrow> 
     invar2 (map_value_image_filter f m)"
    "invar1 m \<Longrightarrow>
     (\<alpha>2 (map_value_image_filter f m) k = Some v') \<longleftrightarrow>
     (\<exists>v. (\<alpha>1 m k = Some v) \<and> f k v = Some v')"
    "invar1 m \<Longrightarrow>
     (\<alpha>2 (map_value_image_filter f m) k = None) \<longleftrightarrow>
     (\<forall>v. (\<alpha>1 m k = Some v) --> f k v = None)"
  proof -
    assume invar_m : "invar1 m"
    note aux = map_value_image_filter_correct_aux [OF invar_m]

    from aux show "invar2 (map_value_image_filter f m)" by simp
    from aux show "(\<alpha>2 (map_value_image_filter f m) k = Some v') \<longleftrightarrow>
     (\<exists>v. (\<alpha>1 m k = Some v) \<and> f k v = Some v')" 
      by (cases "\<alpha>1 m k", simp_all)
    from aux show "(\<alpha>2 (map_value_image_filter f m) k = None) \<longleftrightarrow>
     (\<forall>v. (\<alpha>1 m k = Some v) --> f k v = None)" 
      by (cases "\<alpha>1 m k", simp_all)
  qed
end

type_synonym ('k,'v,'m1,'m2) map_restrict = "('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> 'm1 \<Rightarrow> 'm2"
locale map_restrict = m1: map \<alpha>1 invar1 + m2: map \<alpha>2 invar2 
  for \<alpha>1 :: "'m1 \<Rightarrow> 'u \<rightharpoonup> 'v" and invar1
  and \<alpha>2 :: "'m2 \<Rightarrow> 'u \<rightharpoonup> 'v" and invar2
  +
  fixes restrict :: "('u \<times> 'v \<Rightarrow> bool) \<Rightarrow> 'm1 \<Rightarrow> 'm2"
  assumes restrict_correct_aux1 :
    "invar1 m \<Longrightarrow> \<alpha>2 (restrict P m) = \<alpha>1 m |` {k. \<exists>v. \<alpha>1 m k = Some v \<and> P (k, v)}"
    "invar1 m \<Longrightarrow> invar2 (restrict P m)"
begin
  lemma restrict_correct_aux2 :
    "invar1 m \<Longrightarrow> \<alpha>2 (restrict (\<lambda>(k,_). P k) m) = \<alpha>1 m |` {k. P k}"
  proof -
    assume invar_m : "invar1 m"
    have "\<alpha>1 m |` {k. (\<exists>v. \<alpha>1 m k = Some v) \<and> P k} = \<alpha>1 m |` {k. P k}"
      (is "\<alpha>1 m |` ?A1 = \<alpha>1 m |` ?A2")
    proof
      fix k
      show "(\<alpha>1 m |` ?A1) k = (\<alpha>1 m |` ?A2) k"
      proof (cases "k \<in> ?A2")
        case False thus ?thesis by simp
      next
        case True
        hence P_k : "P k" by simp

        show ?thesis
          by (cases "\<alpha>1 m k", simp_all add: P_k)
      qed
    qed
    with invar_m show "\<alpha>2 (restrict (\<lambda>(k, _). P k) m) = \<alpha>1 m |` {k. P k}"
      by (simp add: restrict_correct_aux1)
  qed

  lemmas restrict_correct = 
     restrict_correct_aux1
     restrict_correct_aux2
end


subsection "Ordered Maps"
  locale ordered_map = map \<alpha> invar 
    for \<alpha> :: "'s \<Rightarrow> ('u::linorder) \<rightharpoonup> 'v" and invar

  locale ordered_finite_map = finite_map \<alpha> invar + ordered_map \<alpha> invar
    for \<alpha> :: "'s \<Rightarrow> ('u::linorder) \<rightharpoonup> 'v" and invar

subsubsection \<open>Ordered Iteration\<close>
  (* Deprecated *)
(*
  locale map_iterateoi = ordered_finite_map \<alpha> invar
    for \<alpha> :: "'s \<Rightarrow> ('u::linorder) \<rightharpoonup> 'v" and invar
    +
    fixes iterateoi :: "'s \<Rightarrow> ('u \<times> 'v,'\<sigma>) set_iterator"
    assumes iterateoi_rule: "
      invar m \<Longrightarrow> map_iterator_linord (iterateoi m) (\<alpha> m)"
  begin
    lemma iterateoi_rule_P[case_names minv inv0 inv_pres i_complete i_inter]:
      assumes MINV: "invar m"
      assumes I0: "I (dom (\<alpha> m)) \<sigma>0"
      assumes IP: "!!k v it \<sigma>. \<lbrakk> 
        c \<sigma>; 
        k \<in> it; 
        \<forall>j\<in>it. k\<le>j; 
        \<forall>j\<in>dom (\<alpha> m) - it. j\<le>k; 
        \<alpha> m k = Some v; 
        it \<subseteq> dom (\<alpha> m); 
        I it \<sigma> 
      \<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      assumes II: "!!\<sigma> it. \<lbrakk> 
        it \<subseteq> dom (\<alpha> m); 
        it \<noteq> {}; 
        \<not> c \<sigma>; 
        I it \<sigma>; 
        \<forall>k\<in>it. \<forall>j\<in>dom (\<alpha> m) - it. j\<le>k 
      \<rbrakk> \<Longrightarrow> P \<sigma>"
      shows "P (iterateoi m c f \<sigma>0)"
    using map_iterator_linord_rule_P [OF iterateoi_rule, of m I \<sigma>0 c f P] assms
    by simp

    lemma iterateo_rule_P[case_names minv inv0 inv_pres i_complete]: 
      assumes MINV: "invar m"
      assumes I0: "I (dom (\<alpha> m)) \<sigma>0"
      assumes IP: "!!k v it \<sigma>. \<lbrakk> k \<in> it; \<forall>j\<in>it. k\<le>j; \<forall>j\<in>dom (\<alpha> m) - it. j\<le>k; \<alpha> m k = Some v; it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
                  \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      shows "P (iterateoi m (\<lambda>_. True) f \<sigma>0)"
    using map_iterator_linord_rule_P [OF iterateoi_rule, of m I \<sigma>0 "\<lambda>_. True" f P] assms
    by simp
  end

  lemma map_iterateoi_I :
  assumes "\<And>m. invar m \<Longrightarrow> map_iterator_linord (itoi m) (\<alpha> m)"
  shows "map_iterateoi \<alpha> invar itoi"
  proof
    fix m 
    assume invar_m: "invar m"
    from assms(1)[OF invar_m] show it_OK: "map_iterator_linord (itoi m) (\<alpha> m)" .
  
    from set_iterator_genord.finite_S0 [OF it_OK[unfolded set_iterator_map_linord_def]]
    show "finite (dom (\<alpha> m))" by (simp add: finite_map_to_set) 
  qed

  locale map_reverse_iterateoi = ordered_finite_map \<alpha> invar 
    for \<alpha> :: "'s \<Rightarrow> ('u::linorder) \<rightharpoonup> 'v" and invar
    +
    fixes reverse_iterateoi :: "'s \<Rightarrow> ('u \<times> 'v,'\<sigma>) set_iterator"
    assumes reverse_iterateoi_rule: "
      invar m \<Longrightarrow> map_iterator_rev_linord (reverse_iterateoi m) (\<alpha> m)"
  begin
    lemma reverse_iterateoi_rule_P[case_names minv inv0 inv_pres i_complete i_inter]:
      assumes MINV: "invar m"
      assumes I0: "I (dom (\<alpha> m)) \<sigma>0"
      assumes IP: "!!k v it \<sigma>. \<lbrakk> 
        c \<sigma>; 
        k \<in> it; 
        \<forall>j\<in>it. k\<ge>j; 
        \<forall>j\<in>dom (\<alpha> m) - it. j\<ge>k; 
        \<alpha> m k = Some v; 
        it \<subseteq> dom (\<alpha> m); 
        I it \<sigma> 
      \<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      assumes II: "!!\<sigma> it. \<lbrakk> 
        it \<subseteq> dom (\<alpha> m); 
        it \<noteq> {}; 
        \<not> c \<sigma>; 
        I it \<sigma>; 
        \<forall>k\<in>it. \<forall>j\<in>dom (\<alpha> m) - it. j\<ge>k 
      \<rbrakk> \<Longrightarrow> P \<sigma>"
      shows "P (reverse_iterateoi m c f \<sigma>0)"
    using map_iterator_rev_linord_rule_P [OF reverse_iterateoi_rule, of m I \<sigma>0 c f P] assms
    by simp

    lemma reverse_iterateo_rule_P[case_names minv inv0 inv_pres i_complete]:
      assumes MINV: "invar m"
      assumes I0: "I (dom (\<alpha> m)) \<sigma>0"
      assumes IP: "!!k v it \<sigma>. \<lbrakk> 
        k \<in> it; 
        \<forall>j\<in>it. k\<ge>j; 
        \<forall>j\<in>dom (\<alpha> m) - it. j\<ge>k; 
        \<alpha> m k = Some v; 
        it \<subseteq> dom (\<alpha> m); 
        I it \<sigma> 
      \<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      shows "P (reverse_iterateoi m (\<lambda>_. True) f \<sigma>0)"
    using map_iterator_rev_linord_rule_P[OF reverse_iterateoi_rule, of m I \<sigma>0 "\<lambda>_. True" f P] assms
    by simp
  end

  lemma map_reverse_iterateoi_I :
  assumes "\<And>m. invar m \<Longrightarrow> map_iterator_rev_linord (ritoi m) (\<alpha> m)"
  shows "map_reverse_iterateoi \<alpha> invar ritoi"
  proof
    fix m 
    assume invar_m: "invar m"
    from assms(1)[OF invar_m] show it_OK: "map_iterator_rev_linord (ritoi m) (\<alpha> m)" .
  
    from set_iterator_genord.finite_S0 [OF it_OK[unfolded set_iterator_map_rev_linord_def]]
    show "finite (dom (\<alpha> m))" by (simp add: finite_map_to_set) 
  qed
*)

locale poly_map_iterateoi_defs =
  fixes olist_it :: "'s \<Rightarrow> ('u\<times>'v,('u\<times>'v) list) set_iterator"
begin
  definition iterateoi :: "'s \<Rightarrow> ('u\<times>'v,'\<sigma>) set_iterator"
    where "iterateoi S \<equiv> it_to_it (olist_it S)"

  abbreviation "iterateo m \<equiv> iterateoi m (\<lambda>_. True)"
end

locale poly_map_iterateoi =
  finite_map \<alpha> invar + poly_map_iterateoi_defs list_ordered_it
  for \<alpha> :: "'s \<Rightarrow> ('u::linorder) \<rightharpoonup> 'v" 
  and invar 
  and list_ordered_it :: "'s \<Rightarrow> ('u\<times>'v,('u\<times>'v) list) set_iterator" +
  assumes list_ordered_it_correct: "invar m 
    \<Longrightarrow> map_iterator_linord (list_ordered_it m) (\<alpha> m)"
begin
  lemma iterateoi_correct: "invar S \<Longrightarrow> map_iterator_linord (iterateoi S) (\<alpha> S)"
    unfolding iterateoi_def
    apply (rule it_to_it_map_linord_correct)
    by (rule list_ordered_it_correct)

  lemma pi_iterateoi[icf_proper_iteratorI]: 
    "proper_it (iterateoi S) (iterateoi S)"
    unfolding iterateoi_def 
    by (intro icf_proper_iteratorI)


  lemma iterateoi_rule_P[case_names minv inv0 inv_pres i_complete i_inter]:
    assumes MINV: "invar m"
    assumes I0: "I (dom (\<alpha> m)) \<sigma>0"
    assumes IP: "!!k v it \<sigma>. \<lbrakk> 
      c \<sigma>; 
      k \<in> it; 
      \<alpha> m k = Some v; 
      it \<subseteq> dom (\<alpha> m); 
      I it \<sigma>;
      \<And>j. j\<in>it \<Longrightarrow> k\<le>j; 
      \<And>j. j\<in>dom (\<alpha> m) - it \<Longrightarrow> j\<le>k
    \<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
    assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    assumes II: "!!\<sigma> it. \<lbrakk> 
      it \<subseteq> dom (\<alpha> m); 
      it \<noteq> {}; 
      \<not> c \<sigma>; 
      I it \<sigma>; 
      \<And>k j. \<lbrakk>k\<in>it; j\<in>dom (\<alpha> m) - it\<rbrakk> \<Longrightarrow> j\<le>k 
    \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iterateoi m c f \<sigma>0)"
    using assms by (rule map_iterator_linord_rule_P[OF iterateoi_correct])

  lemma iterateo_rule_P[case_names minv inv0 inv_pres i_complete]: 
    assumes MINV: "invar m"
    assumes I0: "I (dom (\<alpha> m)) \<sigma>0"
    assumes IP: "!!k v it \<sigma>. \<lbrakk> 
      k \<in> it; 
      \<alpha> m k = Some v; 
      it \<subseteq> dom (\<alpha> m); 
      I it \<sigma>;
      \<And>j. j\<in>it \<Longrightarrow> k\<le>j; 
      \<And>j. j\<in>dom (\<alpha> m) - it \<Longrightarrow> j\<le>k
    \<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
    assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    shows "P (iterateo m f \<sigma>0)"
    using assms 
      map_iterator_linord_rule_P[OF iterateoi_correct, of m I \<sigma>0 "\<lambda>_. True" f P]
    by blast

end
  
type_synonym ('k,'v,'s) map_list_rev_it
  = "'s \<Rightarrow> ('k\<times>'v,('k\<times>'v) list) set_iterator"

locale poly_map_rev_iterateoi_defs =
  fixes list_rev_it :: "'s \<Rightarrow> ('u\<times>'v,('u\<times>'v) list) set_iterator"
begin
  definition rev_iterateoi :: "'s \<Rightarrow> ('u\<times>'v,'\<sigma>) set_iterator"
    where "rev_iterateoi S \<equiv> it_to_it (list_rev_it S)"

  abbreviation "rev_iterateo m \<equiv> rev_iterateoi m (\<lambda>_. True)"
  abbreviation "reverse_iterateoi \<equiv> rev_iterateoi"
  abbreviation "reverse_iterateo \<equiv> rev_iterateo"
end

locale poly_map_rev_iterateoi =
  finite_map \<alpha> invar + poly_map_rev_iterateoi_defs list_rev_it
  for \<alpha> :: "'s \<Rightarrow> ('u::linorder) \<rightharpoonup> 'v" 
  and invar
  and list_rev_it :: "'s \<Rightarrow> ('u\<times>'v,('u\<times>'v) list) set_iterator" +
  assumes list_rev_it_correct: 
    "invar m \<Longrightarrow> map_iterator_rev_linord (list_rev_it m) (\<alpha> m)"
begin
  lemma rev_iterateoi_correct: 
    "invar S \<Longrightarrow> map_iterator_rev_linord (rev_iterateoi S) (\<alpha> S)"
    unfolding rev_iterateoi_def
    apply (rule it_to_it_map_rev_linord_correct)
    by (rule list_rev_it_correct)

  lemma pi_rev_iterateoi[icf_proper_iteratorI]: 
    "proper_it (rev_iterateoi S) (rev_iterateoi S)"
    unfolding rev_iterateoi_def 
    by (intro icf_proper_iteratorI)


  lemma rev_iterateoi_rule_P[case_names minv inv0 inv_pres i_complete i_inter]:
    assumes MINV: "invar m"
    assumes I0: "I (dom (\<alpha> m)) \<sigma>0"
    assumes IP: "!!k v it \<sigma>. \<lbrakk> 
      c \<sigma>; 
      k \<in> it; 
      \<alpha> m k = Some v; 
      it \<subseteq> dom (\<alpha> m); 
      I it \<sigma>;
      \<And>j. j\<in>it \<Longrightarrow> k\<ge>j; 
      \<And>j. j\<in>dom (\<alpha> m) - it \<Longrightarrow> j\<ge>k
    \<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
    assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    assumes II: "!!\<sigma> it. \<lbrakk> 
      it \<subseteq> dom (\<alpha> m); 
      it \<noteq> {}; 
      \<not> c \<sigma>; 
      I it \<sigma>; 
      \<And>k j. \<lbrakk>k\<in>it; j\<in>dom (\<alpha> m) - it\<rbrakk> \<Longrightarrow> j\<ge>k 
    \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (rev_iterateoi m c f \<sigma>0)"
    using assms by (rule map_iterator_rev_linord_rule_P[OF rev_iterateoi_correct])

  lemma rev_iterateo_rule_P[case_names minv inv0 inv_pres i_complete]: 
    assumes MINV: "invar m"
    assumes I0: "I (dom (\<alpha> m)) \<sigma>0"
    assumes IP: "!!k v it \<sigma>. \<lbrakk> 
      k \<in> it; 
      \<alpha> m k = Some v; 
      it \<subseteq> dom (\<alpha> m); 
      I it \<sigma>;
      \<And>j. j\<in>it \<Longrightarrow> k\<ge>j; 
      \<And>j. j\<in>dom (\<alpha> m) - it \<Longrightarrow> j\<ge>k
    \<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
    assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    shows "P (rev_iterateo m f \<sigma>0)"
    using assms 
      map_iterator_rev_linord_rule_P[OF rev_iterateoi_correct, 
        of m I \<sigma>0 "\<lambda>_. True" f P]
    by blast

end

subsubsection \<open>Minimal and Maximal Elements\<close>

  type_synonym ('k,'v,'s) map_min 
    = "'s \<Rightarrow> ('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> ('k \<times> 'v) option"
  locale map_min = ordered_map +
    constrains \<alpha> :: "'s \<Rightarrow> 'u::linorder \<rightharpoonup> 'v"
    fixes min :: "'s \<Rightarrow> ('u \<times> 'v \<Rightarrow> bool) \<Rightarrow> ('u \<times> 'v) option"
    assumes min_correct:
      "\<lbrakk> invar s; rel_of (\<alpha> s) P \<noteq> {} \<rbrakk> \<Longrightarrow> min s P \<in> Some ` rel_of (\<alpha> s) P"
      "\<lbrakk> invar s; (k,v) \<in> rel_of (\<alpha> s) P \<rbrakk> \<Longrightarrow> fst (the (min s P)) \<le> k"
      "\<lbrakk> invar s; rel_of (\<alpha> s) P = {} \<rbrakk> \<Longrightarrow> min s P = None"
  begin
   lemma minE: 
     assumes A: "invar s" "rel_of (\<alpha> s) P \<noteq> {}"
     obtains k v where
     "min s P = Some (k,v)" "(k,v)\<in>rel_of (\<alpha> s) P" "\<forall>(k',v')\<in>rel_of (\<alpha> s) P. k \<le> k'"
   proof -
     from min_correct(1)[OF A] have MIS: "min s P \<in> Some ` rel_of (\<alpha> s) P" .
     then obtain k v where KV: "min s P = Some (k,v)" "(k,v)\<in>rel_of (\<alpha> s) P"
       by auto
     show thesis 
       apply (rule that[OF KV])
       apply (clarify)
       apply (drule min_correct(2)[OF \<open>invar s\<close>])
       apply (simp add: KV(1))
       done
   qed

   lemmas minI = min_correct(3)

   lemma min_Some:
     "\<lbrakk> invar s; min s P = Some (k,v) \<rbrakk> \<Longrightarrow> (k,v)\<in>rel_of (\<alpha> s) P"
     "\<lbrakk> invar s; min s P = Some (k,v); (k',v')\<in>rel_of (\<alpha> s) P \<rbrakk> \<Longrightarrow> k\<le>k'"
     apply -
     apply (cases "rel_of (\<alpha> s) P = {}")
     apply (drule (1) min_correct(3))
     apply simp
     apply (erule (1) minE)
     apply auto [1]
     apply (drule (1) min_correct(2))
     apply auto
     done
     
   lemma min_None:
     "\<lbrakk> invar s; min s P = None \<rbrakk> \<Longrightarrow> rel_of (\<alpha> s) P = {}"
     apply (cases "rel_of (\<alpha> s) P = {}")
     apply simp
     apply (drule (1) min_correct(1))
     apply auto
     done

  end

  type_synonym ('k,'v,'s) map_max
    = "'s \<Rightarrow> ('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> ('k \<times> 'v) option"
  locale map_max = ordered_map +
    constrains \<alpha> :: "'s \<Rightarrow> 'u::linorder \<rightharpoonup> 'v"
    fixes max :: "'s \<Rightarrow> ('u \<times> 'v \<Rightarrow> bool) \<Rightarrow> ('u \<times> 'v) option"
    assumes max_correct:
      "\<lbrakk> invar s; rel_of (\<alpha> s) P \<noteq> {} \<rbrakk> \<Longrightarrow> max s P \<in> Some ` rel_of (\<alpha> s) P"
      "\<lbrakk> invar s; (k,v) \<in> rel_of (\<alpha> s) P \<rbrakk> \<Longrightarrow> fst (the (max s P)) \<ge> k"
      "\<lbrakk> invar s; rel_of (\<alpha> s) P = {} \<rbrakk> \<Longrightarrow> max s P = None"
  begin
   lemma maxE: 
     assumes A: "invar s" "rel_of (\<alpha> s) P \<noteq> {}"
     obtains k v where
     "max s P = Some (k,v)" "(k,v)\<in>rel_of (\<alpha> s) P" "\<forall>(k',v')\<in>rel_of (\<alpha> s) P. k \<ge> k'"
   proof -
     from max_correct(1)[OF A] have MIS: "max s P \<in> Some ` rel_of (\<alpha> s) P" .
     then obtain k v where KV: "max s P = Some (k,v)" "(k,v)\<in>rel_of (\<alpha> s) P"
       by auto
     show thesis 
       apply (rule that[OF KV])
       apply (clarify)
       apply (drule max_correct(2)[OF \<open>invar s\<close>])
       apply (simp add: KV(1))
       done
   qed

   lemmas maxI = max_correct(3)

   lemma max_Some:
     "\<lbrakk> invar s; max s P = Some (k,v) \<rbrakk> \<Longrightarrow> (k,v)\<in>rel_of (\<alpha> s) P"
     "\<lbrakk> invar s; max s P = Some (k,v); (k',v')\<in>rel_of (\<alpha> s) P \<rbrakk> \<Longrightarrow> k\<ge>k'"
     apply -
     apply (cases "rel_of (\<alpha> s) P = {}")
     apply (drule (1) max_correct(3))
     apply simp
     apply (erule (1) maxE)
     apply auto [1]
     apply (drule (1) max_correct(2))
     apply auto
     done
     
   lemma max_None:
     "\<lbrakk> invar s; max s P = None \<rbrakk> \<Longrightarrow> rel_of (\<alpha> s) P = {}"
     apply (cases "rel_of (\<alpha> s) P = {}")
     apply simp
     apply (drule (1) max_correct(1))
     apply auto
     done

  end


subsubsection "Conversion to List"
  type_synonym ('k,'v,'s) map_to_sorted_list 
    = "'s \<Rightarrow> ('k \<times> 'v) list"
  locale map_to_sorted_list = ordered_map +
    constrains \<alpha> :: "'s \<Rightarrow> 'u::linorder \<rightharpoonup> 'v"
    fixes to_sorted_list :: "'s \<Rightarrow> ('u\<times>'v) list"
    assumes to_sorted_list_correct: 
    "invar m \<Longrightarrow> map_of (to_sorted_list m) = \<alpha> m"
    "invar m \<Longrightarrow> distinct (map fst (to_sorted_list m))"
    "invar m \<Longrightarrow> sorted (map fst (to_sorted_list m))"

  type_synonym ('k,'v,'s) map_to_rev_list 
    = "'s \<Rightarrow> ('k \<times> 'v) list"
  locale map_to_rev_list = ordered_map +
    constrains \<alpha> :: "'s \<Rightarrow> 'u::linorder \<rightharpoonup> 'v"
    fixes to_rev_list :: "'s \<Rightarrow> ('u\<times>'v) list"
    assumes to_rev_list_correct: 
    "invar m \<Longrightarrow> map_of (to_rev_list m) = \<alpha> m"
    "invar m \<Longrightarrow> distinct (map fst (to_rev_list m))"
    "invar m \<Longrightarrow> sorted (rev (map fst (to_rev_list m)))"

subsection "Record Based Interface"

  record ('k,'v,'s) map_ops = 
    map_op_\<alpha> :: "('k,'v,'s) map_\<alpha>"
    map_op_invar :: "('k,'v,'s) map_invar"
    map_op_empty :: "('k,'v,'s) map_empty"
    map_op_lookup :: "('k,'v,'s) map_lookup"
    map_op_update :: "('k,'v,'s) map_update"
    map_op_update_dj :: "('k,'v,'s) map_update_dj"
    map_op_delete :: "('k,'v,'s) map_delete"
    map_op_list_it :: "('k,'v,'s) map_list_it"
    map_op_sng :: "('k,'v,'s) map_sng"
    map_op_restrict :: "('k,'v,'s,'s) map_restrict"
    map_op_add :: "('k,'v,'s) map_add"
    map_op_add_dj :: "('k,'v,'s) map_add_dj"
    map_op_isEmpty :: "('k,'v,'s) map_isEmpty"
    map_op_isSng :: "('k,'v,'s) map_isSng"
    map_op_ball :: "('k,'v,'s) map_ball"
    map_op_bex :: "('k,'v,'s) map_bex"
    map_op_size :: "('k,'v,'s) map_size"
    map_op_size_abort :: "('k,'v,'s) map_size_abort"
    map_op_sel :: "('k,'v,'s) map_sel'"
    map_op_to_list :: "('k,'v,'s) map_to_list"
    map_op_to_map :: "('k,'v,'s) list_to_map"

  locale StdMapDefs = poly_map_iteratei_defs "map_op_list_it ops" 
    for ops :: "('k,'v,'s,'more) map_ops_scheme"
  begin
    abbreviation \<alpha> where "\<alpha> == map_op_\<alpha> ops" 
    abbreviation invar where "invar == map_op_invar ops" 
    abbreviation empty where "empty == map_op_empty ops" 
    abbreviation lookup where "lookup == map_op_lookup ops" 
    abbreviation update where "update == map_op_update ops" 
    abbreviation update_dj where "update_dj == map_op_update_dj ops" 
    abbreviation delete where "delete == map_op_delete ops" 
    abbreviation list_it where "list_it == map_op_list_it ops" 
    abbreviation sng where "sng == map_op_sng ops" 
    abbreviation restrict where "restrict == map_op_restrict ops" 
    abbreviation add where "add == map_op_add ops" 
    abbreviation add_dj where "add_dj == map_op_add_dj ops" 
    abbreviation isEmpty where "isEmpty == map_op_isEmpty ops" 
    abbreviation isSng where "isSng == map_op_isSng ops" 
    abbreviation ball where "ball == map_op_ball ops" 
    abbreviation bex where "bex == map_op_bex ops" 
    abbreviation size where "size == map_op_size ops" 
    abbreviation size_abort where "size_abort == map_op_size_abort ops" 
    abbreviation sel where "sel == map_op_sel ops" 
    abbreviation to_list where "to_list == map_op_to_list ops" 
    abbreviation to_map where "to_map == map_op_to_map ops"
  end

  locale StdMap = StdMapDefs ops +
    map \<alpha> invar +
    map_empty \<alpha> invar empty +
    map_lookup \<alpha> invar lookup  +
    map_update \<alpha> invar update  +
    map_update_dj \<alpha> invar update_dj +
    map_delete \<alpha> invar delete  +
    poly_map_iteratei \<alpha> invar list_it +
    map_sng \<alpha> invar sng  +
    map_restrict \<alpha> invar \<alpha> invar restrict +
    map_add \<alpha> invar add  +
    map_add_dj \<alpha> invar add_dj +
    map_isEmpty \<alpha> invar isEmpty  +
    map_isSng \<alpha> invar isSng  +
    map_ball \<alpha> invar ball  +
    map_bex \<alpha> invar bex  +
    map_size \<alpha> invar size +
    map_size_abort \<alpha> invar size_abort +
    map_sel' \<alpha> invar sel  +
    map_to_list \<alpha> invar to_list  +
    list_to_map \<alpha> invar to_map 
    for ops :: "('k,'v,'s,'more) map_ops_scheme"
  begin
    lemmas correct =
      empty_correct
      sng_correct
      lookup_correct
      update_correct
      update_dj_correct
      delete_correct
      restrict_correct
      add_correct
      add_dj_correct
      isEmpty_correct
      isSng_correct
      ball_correct
      bex_correct
      size_correct
      size_abort_correct
      to_list_correct
      to_map_correct
  end

  lemmas StdMap_intro = StdMap.intro[rem_dup_prems]

  locale StdMap_no_invar = StdMap + map_no_invar \<alpha> invar

  record ('k,'v,'s) omap_ops = "('k,'v,'s) map_ops" + 
    map_op_ordered_list_it :: "'s \<Rightarrow> ('k,'v,('k\<times>'v) list) map_iterator"
    map_op_rev_list_it :: "'s \<Rightarrow> ('k,'v,('k\<times>'v) list) map_iterator"
    map_op_min :: "'s \<Rightarrow> ('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> ('k \<times> 'v) option"
    map_op_max :: "'s \<Rightarrow> ('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> ('k \<times> 'v) option"
    map_op_to_sorted_list :: "'s \<Rightarrow> ('k \<times> 'v) list"
    map_op_to_rev_list :: "'s \<Rightarrow> ('k \<times> 'v) list"

  locale StdOMapDefs = StdMapDefs ops
    + poly_map_iterateoi_defs "map_op_ordered_list_it ops"
    + poly_map_rev_iterateoi_defs "map_op_rev_list_it ops"
    for ops :: "('k::linorder,'v,'s,'more) omap_ops_scheme"
  begin
    abbreviation ordered_list_it where "ordered_list_it 
      \<equiv> map_op_ordered_list_it ops"
    abbreviation rev_list_it where "rev_list_it 
      \<equiv> map_op_rev_list_it ops"
    abbreviation min where "min == map_op_min ops"
    abbreviation max where "max == map_op_max ops"
    abbreviation to_sorted_list where 
      "to_sorted_list \<equiv> map_op_to_sorted_list ops"
    abbreviation to_rev_list where "to_rev_list \<equiv> map_op_to_rev_list ops"
  end

  locale StdOMap = 
    StdOMapDefs ops +
    StdMap ops +
    poly_map_iterateoi \<alpha> invar ordered_list_it +
    poly_map_rev_iterateoi \<alpha> invar rev_list_it +
    map_min \<alpha> invar min +
    map_max \<alpha> invar max +
    map_to_sorted_list \<alpha> invar to_sorted_list +
    map_to_rev_list \<alpha> invar to_rev_list
    for ops :: "('k::linorder,'v,'s,'more) omap_ops_scheme"
  begin
  end

  lemmas StdOMap_intro = 
    StdOMap.intro[OF StdMap_intro, rem_dup_prems]

end
