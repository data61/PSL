section \<open>Executable compilation chain\<close>

theory Compiler
imports Composition
begin

definition term_to_exp :: "C_info \<Rightarrow> rule fset \<Rightarrow> term \<Rightarrow> exp" where
"term_to_exp C_info rs t =
  cakeml.mk_con C_info (heads_of rs |\<union>| constructors.C C_info)
    (pterm_to_sterm (nterm_to_pterm (fresh_frun (term_to_nterm [] t) (heads_of rs |\<union>| constructors.C C_info))))"

lemma (in rules) "Compiler.term_to_exp C_info rs = term_to_cake"
  unfolding term_to_exp_def by (simp add: all_consts_def)

primrec compress_pterm :: "pterm \<Rightarrow> pterm" where
"compress_pterm (Pabs cs) = Pabs (fcompress (map_prod id compress_pterm |`| cs))" |
"compress_pterm (Pconst name) = Pconst name" |
"compress_pterm (Pvar name) = Pvar name" |
"compress_pterm (t $\<^sub>p u) = compress_pterm t $\<^sub>p compress_pterm u"

lemma compress_pterm_eq[simp]: "compress_pterm t = t"
by (induction t) (auto simp: subst_pabs_id fset_map_snd_id map_prod_def fmember.rep_eq)

definition compress_crule_set :: "crule_set \<Rightarrow> crule_set" where
"compress_crule_set = fcompress \<circ> fimage (map_prod id fcompress)"

definition compress_irule_set :: "irule_set \<Rightarrow> irule_set" where
"compress_irule_set = fcompress \<circ> fimage (map_prod id (fcompress \<circ> fimage (map_prod id compress_pterm)))"

definition compress_prule_set :: "prule fset \<Rightarrow> prule fset" where
"compress_prule_set = fcompress \<circ> fimage (map_prod id compress_pterm)"

lemma compress_crule_set_eq[simp]: "compress_crule_set rs = rs"
unfolding compress_crule_set_def by force

lemma compress_irule_set_eq[simp]: "compress_irule_set rs = rs"
unfolding compress_irule_set_def map_prod_def by simp

lemma compress_prule_set[simp]: "compress_prule_set rs = rs"
unfolding compress_prule_set_def by force

definition transform_irule_set_iter :: "irule_set \<Rightarrow> irule_set" where
"transform_irule_set_iter rs = ((transform_irule_set \<circ> compress_irule_set) ^^ max_arity rs) rs"

definition as_sem_env :: "C_info \<Rightarrow> srule list \<Rightarrow> v sem_env \<Rightarrow> v sem_env" where
"as_sem_env C_info rs env =
  \<lparr> sem_env.v =
      build_rec_env (cakeml.mk_letrec_body C_info (fset_of_list (map fst rs) |\<union>| constructors.C C_info) rs) env nsEmpty,
    sem_env.c =
      nsEmpty \<rparr>"

definition empty_sem_env :: "C_info \<Rightarrow> v sem_env" where
"empty_sem_env C_info = \<lparr> sem_env.v = nsEmpty, sem_env.c = constructors.as_static_cenv C_info \<rparr>"

definition sem_env :: "C_info \<Rightarrow> srule list \<Rightarrow> v sem_env" where
"sem_env C_info rs = extend_dec_env (as_sem_env C_info rs (empty_sem_env C_info)) (empty_sem_env C_info)"

definition compile :: "C_info \<Rightarrow> rule fset \<Rightarrow> Ast.prog" where
"compile C_info =
  CakeML_Backend.compile' C_info \<circ>
  Rewriting_Sterm.compile \<circ>
  compress_prule_set \<circ>
  Rewriting_Pterm.compile \<circ>
  transform_irule_set_iter \<circ>
  compress_irule_set \<circ>
  Rewriting_Pterm_Elim.compile \<circ>
  compress_crule_set \<circ>
  Rewriting_Nterm.consts_of \<circ>
  fcompress \<circ>
  Rewriting_Nterm.compile' C_info \<circ>
  fcompress"

definition compile_to_env :: "C_info \<Rightarrow> rule fset \<Rightarrow> v sem_env" where
"compile_to_env C_info =
  sem_env C_info \<circ>
  Rewriting_Sterm.compile \<circ>
  compress_prule_set \<circ>
  Rewriting_Pterm.compile \<circ>
  transform_irule_set_iter \<circ>
  compress_irule_set \<circ>
  Rewriting_Pterm_Elim.compile \<circ>
  compress_crule_set \<circ>
  Rewriting_Nterm.consts_of \<circ>
  fcompress \<circ>
  Rewriting_Nterm.compile' C_info \<circ>
  fcompress"

lemma (in rules) "Compiler.compile_to_env C_info rs = rules.cake_sem_env C_info rs"
unfolding Compiler.compile_to_env_def Compiler.sem_env_def Compiler.as_sem_env_def Compiler.empty_sem_env_def
unfolding rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.sem_env_def
unfolding rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.as_sem_env_def
unfolding empty_sem_env_def
by (auto simp:
        Compiler.compress_irule_set_eq[abs_def]
        Composition.transform_irule_set_iter_def[abs_def]
        Compiler.transform_irule_set_iter_def[abs_def] comp_def pre_constants.all_consts_def)

export_code
  term_to_exp compile compile_to_env
  checking Scala

end