section Substitution

text \<open>This theory introduces the substitution operation using a locale, and provides two models.\<close>

theory Substitution
  imports Renaming
begin

subsection Definition

locale substitution =
  fixes subst :: "('r,'l,'v) expr \<Rightarrow> 'v \<Rightarrow> ('r,'l,'v) expr \<Rightarrow> ('r,'l,'v) expr"
  assumes 
    renaming_distr_subst: "\<R>\<^sub>E \<alpha> \<beta> (subst e x e') = subst (\<R>\<^sub>E \<alpha> \<beta> e) x (\<R>\<^sub>E \<alpha> \<beta> e')" and (* needed in mimicking *)
    subst_introduces_no_rids: "RID\<^sub>E (subst e x e') \<subseteq> RID\<^sub>E e \<union> RID\<^sub>E e'" and
    subst_introduces_no_lids: "LID\<^sub>E (subst e x e') \<subseteq> LID\<^sub>E e \<union> LID\<^sub>E e'"
begin

lemma rid_substE [dest]: "r \<in> RID\<^sub>E (subst (VE v) x e) \<Longrightarrow> r \<notin> RID\<^sub>E e \<Longrightarrow> r \<in> RID\<^sub>V v"
  using subst_introduces_no_rids by fastforce

lemma lid_substE [dest]: "l \<in> LID\<^sub>E (subst (VE v) x e) \<Longrightarrow> l \<notin> LID\<^sub>E e \<Longrightarrow> l \<in> LID\<^sub>V v"
  using subst_introduces_no_lids by fastforce

end (* substitution locale *)

subsection \<open>Trivial model\<close>

fun constant_function :: "('r,'l,'v) expr \<Rightarrow> 'v \<Rightarrow> ('r,'l,'v) expr \<Rightarrow> ('r,'l,'v) expr" where 
  "constant_function e x e' = VE (CV Unit)"

lemma constant_function_models_substitution: 
  "substitution constant_function" by (auto simp add: substitution_def)

subsection \<open>Example model\<close>

subsubsection Preliminaries

notation set3_val ("\<V>\<^sub>V")
notation set3_expr ("\<V>\<^sub>E")

abbreviation rename_vars_val :: "('v \<Rightarrow> 'v) \<Rightarrow> ('r,'l,'v) val \<Rightarrow> ('r,'l,'v) val" ("\<R>\<V>\<^sub>V") where
  "\<R>\<V>\<^sub>V \<zeta> \<equiv> map_val id id \<zeta>"

abbreviation rename_vars_expr :: "('v \<Rightarrow> 'v) \<Rightarrow> ('r,'l,'v) expr \<Rightarrow> ('r,'l,'v) expr" ("\<R>\<V>\<^sub>E") where
  "\<R>\<V>\<^sub>E \<zeta> \<equiv> map_expr id id \<zeta>"

lemma var_renaming_preserves_size: (* for termination proof *)
  fixes 
    v :: "('r,'l,'v) val" and
    e :: "('r,'l,'v) expr" and
    \<alpha> :: "'r \<Rightarrow> 'r'" and
    \<beta> :: "'l \<Rightarrow> 'l'" and
    \<zeta> :: "'v \<Rightarrow> 'v'"
  shows
  "size (map_val \<alpha> \<beta> \<zeta> v) = size v"
  "size (map_expr \<alpha> \<beta> \<zeta> e) = size e"
proof -
  have "(\<forall>(\<alpha> :: 'r \<Rightarrow> 'r') (\<beta> :: 'l \<Rightarrow> 'l') (\<zeta> :: 'v \<Rightarrow> 'v'). size (map_val \<alpha> \<beta> \<zeta> v) = size v) \<and> 
        (\<forall>(\<alpha> :: 'r \<Rightarrow> 'r') (\<beta> :: 'l \<Rightarrow> 'l') (\<zeta> :: 'v \<Rightarrow> 'v'). size (map_expr \<alpha> \<beta> \<zeta> e) = size e)"
    by (induct rule: val_expr.induct) auto
  thus 
    "size (map_val \<alpha> \<beta> \<zeta> v) = size v" 
    "size (map_expr \<alpha> \<beta> \<zeta> e) = size e" 
    by auto
qed

subsubsection Definition

function
  nat_subst\<^sub>V :: "('r,'l,nat) expr \<Rightarrow> nat \<Rightarrow> ('r,'l,nat) val \<Rightarrow> ('r,'l,nat) expr" and
  nat_subst\<^sub>E :: "('r,'l,nat) expr \<Rightarrow> nat \<Rightarrow> ('r,'l,nat) expr \<Rightarrow> ('r,'l,nat) expr"
  where
  "nat_subst\<^sub>V e x (CV const) = VE (CV const)"
| "nat_subst\<^sub>V e x (Var x') = (if x = x' then e else VE (Var x'))"
| "nat_subst\<^sub>V e x (Loc l) = VE (Loc l)"
| "nat_subst\<^sub>V e x (Rid r) = VE (Rid r)"
| "nat_subst\<^sub>V e x (Lambda y e') = VE (
  if x = y then 
    Lambda y e' 
  else 
    let z = Suc (Max (\<V>\<^sub>E e' \<union> \<V>\<^sub>E e)) in
    Lambda z (nat_subst\<^sub>E e x (\<R>\<V>\<^sub>E (id(y := z)) e')))"
| "nat_subst\<^sub>E e x (VE v') = nat_subst\<^sub>V e x v'"
| "nat_subst\<^sub>E e x (Apply l r) = Apply (nat_subst\<^sub>E e x l) (nat_subst\<^sub>E e x r)"
| "nat_subst\<^sub>E e x (Ite e1 e2 e3) = Ite (nat_subst\<^sub>E e x e1) (nat_subst\<^sub>E e x e2) (nat_subst\<^sub>E e x e3)"
| "nat_subst\<^sub>E e x (Ref e') = Ref (nat_subst\<^sub>E e x e')"
| "nat_subst\<^sub>E e x (Read e') = Read (nat_subst\<^sub>E e x e')"
| "nat_subst\<^sub>E e x (Assign l r) = Assign (nat_subst\<^sub>E e x l) (nat_subst\<^sub>E e x r)"
| "nat_subst\<^sub>E e x (Rfork e') = Rfork (nat_subst\<^sub>E e x e')"
| "nat_subst\<^sub>E e x (Rjoin e')  = Rjoin (nat_subst\<^sub>E e x e')"
  by pat_completeness auto
termination 
  by (relation "measure (\<lambda>x. case x of Inl (e,x,v) \<Rightarrow> size v | Inr (e,x,e') \<Rightarrow> size e')")
     (auto simp add: var_renaming_preserves_size(2))

subsubsection \<open>Proof obligations\<close>

lemma nat_subst\<^sub>E_distr:
  fixes e :: "('r,'l,nat) expr"
  shows "\<R>\<^sub>E \<alpha> \<beta> (nat_subst\<^sub>E e x e') = nat_subst\<^sub>E (\<R>\<^sub>E \<alpha> \<beta> e) x (\<R>\<^sub>E \<alpha> \<beta> e')"
proof -
  fix v' :: "('r,'l,nat) val"
  have
    "(\<forall>\<alpha> \<beta> x e \<zeta>. \<R>\<^sub>E \<alpha> \<beta> (nat_subst\<^sub>V e x (\<R>\<V>\<^sub>V \<zeta> v')) = nat_subst\<^sub>V (\<R>\<^sub>E \<alpha> \<beta> e) x (\<R>\<^sub>V \<alpha> \<beta> (\<R>\<V>\<^sub>V \<zeta> v'))) \<and>
     (\<forall>\<alpha> \<beta> x e \<zeta>. \<R>\<^sub>E \<alpha> \<beta> (nat_subst\<^sub>E e x (\<R>\<V>\<^sub>E \<zeta> e')) = nat_subst\<^sub>E (\<R>\<^sub>E \<alpha> \<beta> e) x (\<R>\<^sub>E \<alpha> \<beta> (\<R>\<V>\<^sub>E \<zeta> e')))"
    by (induct rule: val_expr.induct) (auto simp add: expr.set_map(3) fun.map_ident)
  hence "\<R>\<^sub>E \<alpha> \<beta> (nat_subst\<^sub>E e x (\<R>\<V>\<^sub>E id e')) = nat_subst\<^sub>E (\<R>\<^sub>E \<alpha> \<beta> e) x (\<R>\<^sub>E \<alpha> \<beta> (\<R>\<V>\<^sub>E id e'))" by blast
  thus ?thesis by simp
qed

lemma nat_subst\<^sub>E_introduces_no_rids:
  fixes e' :: "('r,'l,nat) expr"
  shows "RID\<^sub>E (nat_subst\<^sub>E e x e') \<subseteq> RID\<^sub>E e \<union> RID\<^sub>E e'"
proof -
  fix v' :: "('r,'l,nat) val"
  have 
    "(\<forall>x e. \<forall>\<zeta>. RID\<^sub>E (nat_subst\<^sub>V e x (\<R>\<V>\<^sub>V \<zeta> v')) \<subseteq> RID\<^sub>E e \<union> RID\<^sub>V (\<R>\<V>\<^sub>V \<zeta> v')) \<and>
     (\<forall>x e. \<forall>\<zeta>. RID\<^sub>E (nat_subst\<^sub>E e x (\<R>\<V>\<^sub>E \<zeta> e')) \<subseteq> RID\<^sub>E e \<union> RID\<^sub>E (\<R>\<V>\<^sub>E \<zeta> e'))"
    by (induct rule: val_expr.induct) (auto 0 4 simp add: expr.set_map(1))
  hence "RID\<^sub>E (nat_subst\<^sub>E e x (\<R>\<V>\<^sub>E id e')) \<subseteq> RID\<^sub>E e \<union> RID\<^sub>E (\<R>\<V>\<^sub>E id e')" by blast
  thus ?thesis by simp
qed

lemma nat_subst\<^sub>E_introduces_no_lids: 
  fixes e' :: "('r,'l,nat) expr"
  shows "LID\<^sub>E (nat_subst\<^sub>E e x e') \<subseteq> LID\<^sub>E e \<union> LID\<^sub>E e'"
proof -
  fix v' :: "('r,'l,nat) val"
  have 
    "(\<forall>x e. \<forall>\<zeta>. LID\<^sub>E (nat_subst\<^sub>V e x (\<R>\<V>\<^sub>V \<zeta> v')) \<subseteq> LID\<^sub>E e \<union> LID\<^sub>V (\<R>\<V>\<^sub>V \<zeta> v')) \<and>
     (\<forall>x e. \<forall>\<zeta>. LID\<^sub>E (nat_subst\<^sub>E e x (\<R>\<V>\<^sub>E \<zeta> e')) \<subseteq> LID\<^sub>E e \<union> LID\<^sub>E (\<R>\<V>\<^sub>E \<zeta> e'))"
    by (induct rule: val_expr.induct) (auto 0 4 simp add: expr.set_map(2))
  hence "LID\<^sub>E (nat_subst\<^sub>E e x (\<R>\<V>\<^sub>E id e')) \<subseteq> LID\<^sub>E e \<union> LID\<^sub>E (\<R>\<V>\<^sub>E id e')" by blast
  thus ?thesis by simp
qed

lemma nat_subst\<^sub>E_models_substitution: "substitution nat_subst\<^sub>E"
  by (simp add: nat_subst\<^sub>E_distr nat_subst\<^sub>E_introduces_no_lids nat_subst\<^sub>E_introduces_no_rids substitution_def)

end