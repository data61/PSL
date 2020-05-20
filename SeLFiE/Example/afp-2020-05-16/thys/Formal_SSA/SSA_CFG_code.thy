(*  Title:      SSA_CFG_code.thy
    Author:     Denis Lohner, Sebastian Ullrich
*)

theory SSA_CFG_code imports
  SSA_CFG
  Mapping_Exts
  "HOL-Library.Product_Lexorder"
begin

definition Union_of :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> 'b set"
  where "Union_of f A \<equiv> \<Union>(f ` A)"

lemma Union_of_alt_def: "Union_of f A = (\<Union>x \<in> A. f x)"
  unfolding Union_of_def by simp

type_synonym ('node, 'val) phis_code = "('node \<times> 'val, 'val list) mapping"

context CFG_base begin
  definition addN :: "'g \<Rightarrow> 'node \<Rightarrow> ('var, 'node set) mapping \<Rightarrow> ('var, 'node set) mapping"
    where "addN g n \<equiv> fold (\<lambda>v. Mapping.map_default v {} (insert n)) (sorted_list_of_set (uses g n))"
  definition "addN' g n = fold (\<lambda>v m. m(v \<mapsto> case_option {n} (insert n) (m v))) (sorted_list_of_set (uses g n))"

  lemma addN_transfer [transfer_rule]:
    "rel_fun (=) (rel_fun (=) (rel_fun (pcr_mapping (=) (=)) (pcr_mapping (=) (=)))) addN' addN"
    unfolding addN_def [abs_def] addN'_def [abs_def]
      Mapping.map_default_def [abs_def] Mapping.default_def
  apply (auto simp: mapping.pcr_cr_eq rel_fun_def cr_mapping_def)
  apply transfer
  apply (rule fold_cong)
    apply simp
   apply simp
  apply (intro ext)
  by auto

  definition "useNodes_of g = fold (addN g) (\<alpha>n g) Mapping.empty"
  lemmas useNodes_of_code = useNodes_of_def [unfolded addN_def [abs_def]]
  declare useNodes_of_code [code]

  lemma lookup_useNodes_of':
    assumes [simp]: "\<And>n. finite (uses g n)"
    shows "Mapping.lookup (useNodes_of g) v =
    (if (\<exists>n \<in> set (\<alpha>n g). v \<in> uses g n) then Some {n \<in> set (\<alpha>n g). v \<in> uses g n} else None)"
  proof -
    { fix m n xs v
      have "Mapping.lookup (fold (\<lambda>v. Mapping.map_default (v::'var) {} (insert (n::'node))) xs m) v=
        (case Mapping.lookup m v of None \<Rightarrow> (if v \<in> set xs then Some {n} else None)
          | Some N \<Rightarrow> (if v \<in> set xs then Some (insert n N) else Some N))"
      by (induction xs arbitrary: m) (auto simp: Mapping_lookup_map_default split: option.splits)
    }
    note addN_conv = this [of n "sorted_list_of_set (uses g n)" for g n, folded addN_def, simplified]
    { fix xs m v
      have "Mapping.lookup (fold (addN g) xs m) v = (case Mapping.lookup m v of None \<Rightarrow> if (\<exists>n\<in>set xs. v \<in> uses g n) then Some {n\<in>set xs. v \<in> uses g n} else None
        | Some N \<Rightarrow> Some ({n\<in>set xs. v \<in> uses g n} \<union> N))"
      by (induction xs arbitrary: m) (auto split: option.splits simp: addN_conv)
    }
    note this [of "\<alpha>n g" Mapping.empty, simp]
    show ?thesis unfolding useNodes_of_def
      by (auto split: option.splits simp: lookup_empty)
  qed
end

context CFG begin
  lift_definition useNodes_of' :: "'g \<Rightarrow> ('var, 'node set) mapping"
  is "\<lambda>g v. if (\<exists>n \<in> set (\<alpha>n g). v \<in> uses g n) then Some {n \<in> set (\<alpha>n g). v \<in> uses g n} else None" .

  lemma useNodes_of': "useNodes_of' = useNodes_of"
  proof
    fix g
    { fix m n xs
      have "fold (\<lambda>v m. m(v::'var \<mapsto> case m v of None \<Rightarrow> {n::'node} | Some x \<Rightarrow> insert n x)) xs m =
        (\<lambda>v. case m v of None \<Rightarrow> (if v \<in> set xs then Some {n} else None)
          | Some N \<Rightarrow> (if v \<in> set xs then Some (insert n N) else Some N))"
      by (induction xs arbitrary: m)(auto split: option.splits)
    }
    note addN'_conv = this [of n "sorted_list_of_set (uses g n)" for g n, folded addN'_def, simplified]
    { fix xs m
      have "fold (addN' g) xs m = (\<lambda>v. case m v of None \<Rightarrow> if (\<exists>n\<in>set xs. v \<in> uses g n) then Some {n\<in>set xs. v \<in> uses g n} else None
        | Some N \<Rightarrow> Some ({n\<in>set xs. v \<in> uses g n} \<union> N))"
      by (induction xs arbitrary: m) (auto 4 4 split: option.splits if_splits simp: addN'_conv intro!: ext)
    }
    note this [of "\<alpha>n g" Map.empty, simp]
    show "useNodes_of' g = useNodes_of g"
    unfolding mmap_def useNodes_of_def
    by (transfer fixing: g) auto
  qed

  declare useNodes_of'.transfer [unfolded useNodes_of', transfer_rule]

  lemma lookup_useNodes_of: "Mapping.lookup (useNodes_of g) v =
    (if (\<exists>n \<in> set (\<alpha>n g). v \<in> uses g n) then Some {n \<in> set (\<alpha>n g). v \<in> uses g n} else None)"
  by clarsimp (transfer'; auto)

end

context CFG_SSA_base begin
  definition phis_addN
  where "phis_addN g n = fold (\<lambda>v. Mapping.map_default v {} (insert n)) (case_option [] id (phis g n))"

  definition phidefNodes where [code]:
    "phidefNodes g = fold (\<lambda>(n,v). Mapping.update v n) (sorted_list_of_set (dom (phis g))) Mapping.empty"

  lemma keys_phidefNodes:
    assumes "finite (dom (phis g))"
    shows "Mapping.keys (phidefNodes g) = snd ` dom (phis g)"
  proof -
    { fix xs m x
      have "fold (\<lambda>(a,b) m. m(b \<mapsto> a)) (xs::('node \<times> 'val) list) m x = (if x \<in> snd ` set xs then (Some \<circ> fst) (last [(b,a)\<leftarrow>xs. a = x]) else m x)"
      by (induction xs arbitrary: m) (auto split: if_splits simp: filter_empty_conv intro: rev_image_eqI)
    }
    from this [of "sorted_list_of_set (dom (phis g))" Map.empty] assms
    show ?thesis
    unfolding phidefNodes_def keys_dom_lookup
    by (transfer fixing: g phis) (auto simp: dom_def intro: rev_image_eqI)
  qed

  definition phiNodes_of :: "'g \<Rightarrow> ('val, ('node \<times> 'val) set) mapping"
  where "phiNodes_of g = fold (phis_addN g) (sorted_list_of_set (dom (phis g))) Mapping.empty"

  lemma lookup_phiNodes_of:
  assumes [simp]: "finite (dom (phis g))"
  shows "Mapping.lookup (phiNodes_of g) v =
    (if (\<exists>n \<in> dom (phis g). v \<in> set (the (phis g n))) then Some {n \<in> dom (phis g). v \<in> set (the (phis g n))} else None)"
  proof -
  {
    fix m n xs v
    have "Mapping.lookup (fold (\<lambda>v. Mapping.map_default v {} (insert (n::'node \<times> 'val))) xs (m::('val, ('node \<times> 'val) set) mapping)) v =
      (case Mapping.lookup m v of None \<Rightarrow> (if v \<in> set xs then Some {n} else None)
        | Some N \<Rightarrow> (if v \<in> set xs then Some (insert n N) else Some N))"
    by (induction xs arbitrary: m) (auto simp: Mapping_lookup_map_default split: option.splits)
  }
  note phis_addN_conv = this [of n "case_option [] id (phis g n)" for n, folded phis_addN_def]
  {
    fix xs m v
    have "Mapping.lookup (fold (phis_addN g) xs m) v =
      (case Mapping.lookup m v of None \<Rightarrow> if (\<exists>n \<in> set xs. v \<in> set (case_option [] id (phis g n))) then Some {n \<in> set xs. v \<in> set (case_option [] id (phis g n))} else None
        | Some N \<Rightarrow> Some ({n \<in> set xs. v \<in> set (case_option [] id (phis g n))} \<union> N))"
    by (induction xs arbitrary: m) (auto simp: phis_addN_conv split: option.splits if_splits)+
  }
  note this [of "sorted_list_of_set (dom (phis g))", simp]
  show ?thesis
    unfolding phiNodes_of_def
  by (force split: option.splits simp: lookup_empty)
  qed

  lemmas phiNodes_of_code = phiNodes_of_def [unfolded phis_addN_def [abs_def]]
  declare phiNodes_of_code [code]

lemma phis_transfer [transfer_rule]:
  includes lifting_syntax
  shows "((=) ===> pcr_mapping (=) (=)) phis (\<lambda>g. Mapping.Mapping (phis g))"
  by (auto simp: mapping.pcr_cr_eq rel_fun_def cr_mapping_def Mapping.Mapping_inverse)

end

context CFG_SSA begin
  declare lookup_phiNodes_of [OF phis_finite, simp]
  declare keys_phidefNodes [OF phis_finite, simp]
end

locale CFG_SSA_ext_base = CFG_SSA_base \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
  for \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set"
    and \<alpha>n :: "'g \<Rightarrow> 'node list"
    and invar :: "'g \<Rightarrow> bool"
    and inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list"
    and Entry :: "'g \<Rightarrow> 'node"
    and "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set"
    and "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val set"
    and phis :: "'g \<Rightarrow> ('node, 'val) phis"
begin
  abbreviation "cache g f \<equiv> Mapping.tabulate (\<alpha>n g) f"

  lemma lookup_cache[simp]: "n \<in> set (\<alpha>n g) \<Longrightarrow> Mapping.lookup (cache g f) n = Some (f n)"
  by transfer (auto simp: Map.map_of_map_restrict)

  lemma lookup_cacheD [dest]: "Mapping.lookup (cache g f) x = Some y \<Longrightarrow> y = f x"
  by transfer (auto simp: Map.map_of_map_restrict restrict_map_def split: if_splits)

  lemma lookup_cache_usesD: "Mapping.lookup (cache g (uses g)) n = Some vs \<Longrightarrow> vs = uses g n"
  by blast
end

definition[simp]: "usesOf m n \<equiv> case_option {} id (Mapping.lookup m n)"

locale CFG_SSA_ext = CFG_SSA_ext_base  \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
  + CFG_SSA \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
  for \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set"
    and \<alpha>n :: "'g \<Rightarrow> 'node list"
    and invar :: "'g \<Rightarrow> bool"
    and inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list"
    and Entry :: "'g \<Rightarrow> 'node"
    and "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set"
    and "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val set"
    and phis :: "'g \<Rightarrow> ('node, 'val) phis"
begin
  lemma usesOf_cache[abs_def, simp]: "usesOf (cache g (uses g)) n = uses g n"
  by (auto simp: uses_in_\<alpha>n dest: lookup_cache_usesD split: option.split)
end

locale CFG_SSA_base_code = CFG_SSA_ext_base \<alpha>e \<alpha>n invar inEdges' Entry "defs" "usesOf \<circ> uses" "\<lambda>g. Mapping.lookup (phis g)"
  for \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set"
    and \<alpha>n :: "'g \<Rightarrow> 'node list"
    and invar :: "'g \<Rightarrow> bool"
    and inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list"
    and Entry :: "'g \<Rightarrow> 'node"
    and "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set"
    and "uses" :: "'g \<Rightarrow> ('node, 'val set) mapping"
    and phis :: "'g \<Rightarrow> ('node, 'val) phis_code"
begin
  declare phis_transfer [simplified, transfer_rule]

  lemma phiDefs_code [code]:
  "phiDefs g n = snd ` Set.filter (\<lambda>(n',v). n' = n) (Mapping.keys (phis g))"
    unfolding phiDefs_def
    by transfer (auto 4 3 intro: rev_image_eqI simp: Set.filter_def)

  lemmas phiUses_code [code] = phiUses_def [folded Union_of_alt_def]
  declare allUses_def [code]
  lemmas allVars_code [code] = allVars_def [folded Union_of_alt_def]
end

locale CFG_SSA_code = CFG_SSA_base_code  \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
  + CFG_SSA_ext \<alpha>e \<alpha>n invar inEdges' Entry "defs" "usesOf \<circ> uses" "\<lambda>g. Mapping.lookup (phis g)"
  for \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set"
    and \<alpha>n :: "'g \<Rightarrow> 'node list"
    and invar :: "'g \<Rightarrow> bool"
    and inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list"
    and Entry :: "'g \<Rightarrow> 'node"
    and "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set"
    and "uses" :: "'g \<Rightarrow> ('node, 'val set) mapping"
    and phis :: "'g \<Rightarrow> ('node, 'val) phis_code"


definition "the_trivial v vs = (case (foldl (\<lambda>(good,v') w. if w = v then (good,v')
      else case v' of Some v' \<Rightarrow> (good \<and> w = v', Some v')
        | None \<Rightarrow> (good, Some w))
    (True, None) vs)
  of (False, _) \<Rightarrow> None | (True,v) \<Rightarrow> v)"

lemma the_trivial_Nil [simp]: "the_trivial x [] = None"
  unfolding the_trivial_def by simp

lemma the_trivialI:
  assumes "set vs \<subseteq> {v, v'}"
    and "v' \<noteq> v"
  shows "the_trivial v vs = (if set vs \<subseteq> {v} then None else Some v')"
proof -
  { fix vx
    have "\<lbrakk> set vs \<subseteq> {v, v'}; v' \<noteq> v; vx \<in> {None, Some v'} \<rbrakk>
    \<Longrightarrow> (case foldl (\<lambda>(good, v') w.
                    if w = v then (good, v')
                    else case v' of None \<Rightarrow> (good, Some w) | Some v' \<Rightarrow> (good \<and> w = v', Some v'))
           (True, vx) vs of
     (True, x) \<Rightarrow> x | (False, x) \<Rightarrow> None) = (if set vs \<subseteq> {v} then vx else Some v')"
    by (induction vs arbitrary: vx; case_tac vx; auto)
  }
  with assms show ?thesis unfolding the_trivial_def by simp
qed

lemma the_trivial_conv:
  shows "the_trivial v vs = (if \<exists>v' \<in> set vs. v' \<noteq> v \<and> set vs - {v'} \<subseteq> {v} then Some (THE v'. v' \<in> set vs \<and> v' \<noteq> v \<and> set vs - {v'} \<subseteq> {v}) else None)"
proof -
  { fix b a vs
    have "a \<noteq> v
       \<Longrightarrow> foldl (\<lambda>(good, v') w.
                     if w = v then (good, v')
                     else case v' of None \<Rightarrow> (good, Some w) | Some v' \<Rightarrow> (good \<and> w = v', Some v'))
            (b, Some a) vs =
           (b \<and> set vs \<subseteq> {v, a}, Some a)"
     by (induction vs arbitrary: b; clarsimp)
  }
  note this[simp]
  { fix b vx
    have "\<lbrakk> vx \<in> insert None (Some ` set vs); case_option True (\<lambda>vx. vx \<noteq> v) vx \<rbrakk>
    \<Longrightarrow> foldl (\<lambda>(good, v') w.
                    if w = v then (good, v')
                    else case v' of None \<Rightarrow> (good, Some w) | Some v' \<Rightarrow> (good \<and> w = v', Some v'))
        (b, vx) vs = (b \<and> (case vx of Some w \<Rightarrow> set vs \<subseteq> {v, w} | None \<Rightarrow> \<exists>w. set vs \<subseteq> {v, w}),
        (case vx of Some w \<Rightarrow> Some w | None \<Rightarrow> if (\<exists>v'\<in>set vs. v' \<noteq> v) then Some (hd (filter (\<lambda>v'. v' \<noteq> v) vs)) else None))"
    by (induction vs arbitrary: b vx; auto)
  }
  hence "the_trivial v vs = (if \<exists>v' \<in> set vs. v' \<noteq> v \<and> set vs - {v'} \<subseteq> {v} then Some (hd (filter (\<lambda>v'. v' \<noteq> v) vs)) else None)"
    unfolding the_trivial_def by (auto split: bool.splits)
  thus ?thesis
  apply (auto split: if_splits)
  apply (rule the_equality [THEN sym])
   by (thin_tac "P" for P, (induction vs; auto))+
qed

lemma the_trivial_SomeE:
  assumes "the_trivial v vs = Some v'"
  obtains "v \<noteq> v'" and "set vs = {v'}" | "v \<noteq> v'" and "set vs = {v,v'}"
using assms
apply atomize_elim
apply (subst(asm) the_trivial_conv)
apply (split if_splits; simp)
by (subgoal_tac "(THE v'. v' \<in> set vs \<and> v' \<noteq> v \<and> set vs - {v'} \<subseteq> {v}) = hd (filter (\<lambda>v'. v' \<noteq> v) vs)")
  (fastforce simp: set_double_filter_hd set_single_hd set_minus_one)+

locale CFG_SSA_wf_base_code = CFG_SSA_base_code \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
  + CFG_SSA_wf_base \<alpha>e \<alpha>n invar inEdges' Entry "defs" "usesOf \<circ> uses" "\<lambda>g. Mapping.lookup (phis g)"
  for \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set"
    and \<alpha>n :: "'g \<Rightarrow> 'node list"
    and invar :: "'g \<Rightarrow> bool"
    and inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list"
    and Entry :: "'g \<Rightarrow> 'node"
    and "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set"
    and "uses" :: "'g \<Rightarrow> ('node, 'val set) mapping"
    and phis :: "'g \<Rightarrow> ('node, 'val) phis_code"
begin
  definition [code]:
    "trivial_code (v::'val) vs = (the_trivial v vs \<noteq> None)"
  definition[code]: "trivial_phis g = Set.filter (\<lambda>(n,v). trivial_code v (the (Mapping.lookup (phis g) (n,v)))) (Mapping.keys (phis g))"
  definition [code]: "redundant_code g = (trivial_phis g \<noteq> {})"
end

locale CFG_SSA_wf_code = CFG_SSA_code \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
  + CFG_SSA_wf_base_code \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
  + CFG_SSA_wf \<alpha>e \<alpha>n invar inEdges' Entry "defs" "usesOf \<circ> uses" "\<lambda>g. Mapping.lookup (phis g)"
  for \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set"
    and \<alpha>n :: "'g \<Rightarrow> 'node list"
    and invar :: "'g \<Rightarrow> bool"
    and inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list"
    and Entry :: "'g \<Rightarrow> 'node"
    and "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set"
    and "uses" :: "'g \<Rightarrow> ('node, 'val set) mapping"
    and phis :: "'g \<Rightarrow> ('node, 'val) phis_code"
begin
  lemma trivial_code:
    "phi g v = Some vs \<Longrightarrow> trivial g v = trivial_code v vs"
  unfolding trivial_def trivial_code_def
  apply (auto split: option.splits simp: isTrivialPhi_def)
    apply (clarsimp simp: the_trivial_conv split: if_splits)
   apply (clarsimp simp: the_trivial_conv split: if_splits)
  apply (erule the_trivial_SomeE)
   apply simp
   apply (rule phiArg_in_allVars; auto simp: phiArg_def)
  apply (rename_tac v')
  apply (rule_tac x=v' in bexI)
   apply simp
  apply (rule phiArg_in_allVars; auto simp: phiArg_def)
  done

  lemma trivial_phis:
    "trivial_phis g = {(n,v). Mapping.lookup (phis g) (n,v) \<noteq> None \<and> trivial g v}"
  unfolding trivial_phis_def Set.filter_def
  apply (auto simp add: phi_def keys_dom_lookup)
   apply (subst trivial_code)
    apply (auto simp: image_def trivial_in_allVars phis_phi)
  apply (frule trivial_phi)
  apply (auto simp add: trivial_code phi_def[symmetric] phis_phi)
  done

  lemma redundant_code:
    "redundant g = redundant_code g"
  unfolding redundant_def redundant_code_def trivial_phis[of g]
  apply (auto simp: image_def trivial_in_allVars)
  apply (frule trivial_phi)
  apply (auto simp: phi_def)
  done

  lemma trivial_code_mapI:
  "\<lbrakk> trivial_code v vs; f ` (set vs - {v}) \<noteq> {v} ; f v = v \<rbrakk> \<Longrightarrow> trivial_code v (map f vs)"
  unfolding trivial_code_def the_trivial_conv
    by (auto split: if_splits)

  lemma trivial_code_map_conv:
    "f v = v \<Longrightarrow> trivial_code v (map f vs) \<longleftrightarrow> (\<exists>v'\<in>set vs. f v' \<noteq> v \<and> (f ` set vs) - {f v'} \<subseteq> {v})"
    unfolding trivial_code_def the_trivial_conv
    by auto

end

locale CFG_SSA_Transformed_code = ssa: CFG_SSA_wf_code \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
   +
   CFG_SSA_Transformed \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "usesOf \<circ> uses" "\<lambda>g. Mapping.lookup (phis g)" var
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  oldDefs :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set" and
  oldUses :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'g \<Rightarrow> ('node, 'val set) mapping" and
  phis :: "'g \<Rightarrow> ('node, 'val) phis_code" and
  var :: "'g \<Rightarrow> 'val \<Rightarrow> 'var"
+
assumes dom_uses_in_graph: "Mapping.keys (uses g) \<subseteq> set (\<alpha>n g)"

end
