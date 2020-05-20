section \<open>Hoare-Triples\<close>
theory Hoare_Triple
imports Run Assertions
begin

text \<open>In this theory, we define Hoare-Triples, which are our basic tool
  for specifying properties of Imperative HOL programs.\<close>

subsection \<open>Definition\<close>

text \<open>Analyze the heap before and after executing a command, to add
  the allocated addresses to the covered address range.\<close>
definition new_addrs :: "heap \<Rightarrow> addr set \<Rightarrow> heap \<Rightarrow> addr set" where
  "new_addrs h as h' = as \<union> {a. lim h \<le> a \<and> a < lim h'}"

lemma new_addr_refl[simp]: "new_addrs h as h = as"
  unfolding new_addrs_def by auto

text \<open>
  Apart from correctness of the program wrt. the pre- and post condition,
  a Hoare-triple also encodes some well-formedness conditions of the command:
  The command must not change addresses outside the address range of the 
  precondition, and it must not decrease the heap limit. 

  Note that we do not require that the command only reads from heap locations
  inside the precondition's address range, as this condition would be quite
  complicated to express with the heap model of Imperative/HOL, and is not 
  necessary in our formalization of partial heaps, that always contain the 
  information for all addresses.
\<close>
definition hoare_triple 
  :: "assn \<Rightarrow> 'a Heap \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> bool" ("<_>/ _/ <_>")
  where
  "<P> c <Q> \<equiv> \<forall>h as \<sigma> r. (h,as)\<Turnstile>P \<and> run c (Some h) \<sigma> r 
  \<longrightarrow> (let h'=the_state \<sigma>; as'=new_addrs h as h' in  
    \<not>is_exn \<sigma> \<and> (h',as')\<Turnstile>Q r \<and> relH ({a . a<lim h \<and> a\<notin>as}) h h' 
    \<and> lim h \<le> lim h')"

text \<open>Sanity checking theorems for Hoare-Triples\<close>  
lemma
  assumes "<P> c <Q>"
  assumes "(h,as)\<Turnstile>P"
  shows hoare_triple_success: "success c h" 
    and hoare_triple_effect: "\<exists>h' r. effect c h h' r \<and> (h',new_addrs h as h')\<Turnstile>Q r"
  using assms 
  unfolding hoare_triple_def success_def effect_def
  apply -
  apply (auto simp: Let_def run.simps) apply fastforce
  by (metis is_exn.simps(2) not_Some_eq2 the_state.simps)

    
lemma hoare_tripleD:
  fixes h h' as as' \<sigma> r
  assumes "<P> c <Q>"
  assumes "(h,as)\<Turnstile>P"
  assumes "run c (Some h) \<sigma> r"
  defines "h'\<equiv>the_state \<sigma>" and "as'\<equiv>new_addrs h as h'"
  shows "\<not>is_exn \<sigma>" 
  and "(h',as')\<Turnstile>Q r"
  and "relH ({a . a<lim h \<and> a\<notin>as}) h h'"
  and "lim h \<le> lim h'"
  using assms 
  unfolding hoare_triple_def h'_def as'_def 
  by (auto simp: Let_def)

text \<open>For garbage-collected languages, specifications usually allow for some
  arbitrary heap parts in the postcondition. The following abbreviation defines
  a handy shortcut notation for such specifications.\<close>
abbreviation hoare_triple' 
  :: "assn \<Rightarrow> 'r Heap \<Rightarrow> ('r \<Rightarrow> assn) \<Rightarrow> bool" ("<_> _ <_>\<^sub>t") 
  where "<P> c <Q>\<^sub>t \<equiv> <P> c <\<lambda>r. Q r * true>"

subsection \<open>Rules\<close>
text \<open>
  In this section, we provide a set of rules to prove Hoare-Triples correct.
\<close>
subsubsection \<open>Basic Rules\<close>

lemma hoare_triple_preI: 
  assumes "\<And>h. h\<Turnstile>P \<Longrightarrow> <P> c <Q>"
  shows "<P> c <Q>"
  using assms
  unfolding hoare_triple_def
  by auto


lemma frame_rule: 
  assumes A: "<P> c <Q>"
  shows "<P*R> c <\<lambda>x. Q x * R>"
  unfolding hoare_triple_def Let_def
  apply (intro allI impI)
  apply (elim conjE)
  apply (intro conjI)
proof -
  fix h as
  assume "(h,as) \<Turnstile> P * R"
  then obtain as1 as2 where [simp]: "as=as1\<union>as2" and DJ: "as1\<inter>as2={}"
    and M1: "(h,as1)\<Turnstile>P" and M2: "(h,as2)\<Turnstile>R"
    unfolding times_assn_def
    by (auto simp: Abs_assn_inverse)

  fix \<sigma> r
  assume RUN: "run c (Some h) \<sigma> r"
  from hoare_tripleD(1)[OF A M1 RUN] show "\<not> is_exn \<sigma>" .
  from hoare_tripleD(4)[OF A M1 RUN] 
  show "lim h \<le> lim (the_state \<sigma>)" .

  from hoare_tripleD(3)[OF A M1 RUN] have 
    RH1: "relH {a. a < lim h \<and> a \<notin> as1} h (the_state \<sigma>)" .
  moreover have "{a. a < lim h \<and> a \<notin> as} \<subseteq> {a. a < lim h \<and> a \<notin> as1}"
    by auto
  ultimately show "relH {a. a < lim h \<and> a \<notin> as} h (the_state \<sigma>)" 
    by (blast intro: relH_subset)
    
  from hoare_tripleD(2)[OF A M1 RUN] have 
    "(the_state \<sigma>, new_addrs h as1 (the_state \<sigma>)) \<Turnstile> Q r" .
  moreover have DJN: "new_addrs h as1 (the_state \<sigma>) \<inter> as2 = {}"
    using DJ models_in_range[OF M2]
    by (auto simp: in_range.simps new_addrs_def)
  moreover have "as2 \<subseteq> {a. a < lim h \<and> a \<notin> as1}" 
    using DJ models_in_range[OF M2]
    by (auto simp: in_range.simps)
  hence "relH as2 h (the_state \<sigma>)" using RH1
    by (blast intro: relH_subset)
  with M2 have "(the_state \<sigma>, as2)\<Turnstile>R"
    by (metis mem_Collect_eq Rep_assn  
      proper_iff relH_in_rangeI(2))
  moreover have "new_addrs h as (the_state \<sigma>) 
    = new_addrs h as1 (the_state \<sigma>) \<union> as2"
    by (auto simp: new_addrs_def)
  ultimately show 
    "(the_state \<sigma>, new_addrs h as (the_state \<sigma>)) \<Turnstile> Q r * R"
    unfolding times_assn_def
    apply (simp add: Abs_assn_inverse)
    apply blast
    done
qed


lemma false_rule[simp, intro!]: "<false> c <Q>"
  unfolding hoare_triple_def by simp

  
lemma cons_rule:
  assumes CPRE: "P \<Longrightarrow>\<^sub>A P'"
  assumes CPOST: "\<And>x. Q x \<Longrightarrow>\<^sub>A Q' x"
  assumes R: "<P'> c <Q>"
  shows "<P> c <Q'>"
  unfolding hoare_triple_def Let_def
  using hoare_tripleD[OF R entailsD[OF CPRE]] entailsD[OF CPOST]
  by blast

lemmas cons_pre_rule = cons_rule[OF _ ent_refl]
lemmas cons_post_rule = cons_rule[OF ent_refl, rotated]

lemma cons_rulet: "\<lbrakk>P\<Longrightarrow>\<^sub>tP'; \<And>x. Q x \<Longrightarrow>\<^sub>t Q' x; <P'> c <Q>\<^sub>t \<rbrakk> \<Longrightarrow> <P> c <Q'>\<^sub>t"
  unfolding entailst_def
  apply (rule cons_pre_rule)
  apply assumption
  apply (rule cons_post_rule)
  apply (erule frame_rule)
  by (simp add: enttD enttI)  

lemmas cons_pre_rulet = cons_rulet[OF _ entt_refl]
lemmas cons_post_rulet = cons_rulet[OF entt_refl, rotated]

  
  
lemma norm_pre_ex_rule:
  assumes A: "\<And>x. <P x> f <Q>"
  shows "<\<exists>\<^sub>Ax. P x> f <Q>"
  unfolding hoare_triple_def Let_def
  apply (intro allI impI, elim conjE mod_exE)
  using hoare_tripleD[OF A]
  by blast

lemma norm_pre_pure_iff[simp]:
  "<P*\<up>b> f <Q> \<longleftrightarrow> (b \<longrightarrow> <P> f <Q>)"
  unfolding hoare_triple_def Let_def
  by auto

lemma norm_pre_pure_iff_sng[simp]:
  "<\<up>b> f <Q> \<longleftrightarrow> (b \<longrightarrow> <emp> f <Q>)"
  using norm_pre_pure_iff[where P=emp]
  by simp

lemma norm_pre_pure_rule1: 
  "\<lbrakk>b \<Longrightarrow> <P> f <Q>\<rbrakk> \<Longrightarrow> <P*\<up>b> f <Q>" by simp

lemma norm_pre_pure_rule2:
  "\<lbrakk> b \<Longrightarrow> <emp> f <Q> \<rbrakk> \<Longrightarrow> <\<up>b> f <Q>" by simp

lemmas norm_pre_pure_rule = norm_pre_pure_rule1 norm_pre_pure_rule2

lemma post_exI_rule: "<P> c <\<lambda>r. Q r x> \<Longrightarrow> <P> c <\<lambda>r. \<exists>\<^sub>Ax. Q r x>"
  by (blast intro: cons_post_rule ent_ex_postI ent_refl)


subsubsection \<open>Rules for Atomic Commands\<close>
lemma ref_rule:
  "<emp> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>"
  unfolding one_assn_def sngr_assn_def hoare_triple_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (intro allI impI)
  apply (elim conjE run_elims)
  apply simp
  apply (auto 
    simp: new_addrs_def Ref.alloc_def Let_def
    Ref.set_def Ref.get_def relH_def in_range.simps)
  done

lemma lookup_rule:
  "<p \<mapsto>\<^sub>r x> !p <\<lambda>r. p \<mapsto>\<^sub>r x * \<up>(r = x)>"
  unfolding hoare_triple_def sngr_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto elim: run_elims simp add: relH_refl in_range.simps new_addrs_def)
  done

lemma update_rule:
  "<p \<mapsto>\<^sub>r y> p := x <\<lambda>r. p \<mapsto>\<^sub>r x>"
  unfolding hoare_triple_def sngr_assn_def
  apply (auto elim!: run_update 
    simp: Let_def Abs_assn_inverse new_addrs_def in_range.simps 
    intro!: relH_set_ref)
  done

lemma update_wp_rule:
  "<r \<mapsto>\<^sub>r y * ((r \<mapsto>\<^sub>r x) -* (Q ()))> r := x <Q>"
  apply (rule cons_post_rule)
  apply (rule frame_rule[OF update_rule[where p=r and x=x], 
    where R="((r \<mapsto>\<^sub>r x) -* (Q ()))"])
  apply (rule ent_trans)
  apply (rule ent_mp)
  by simp

lemma new_rule:
  "<emp> Array.new n x <\<lambda>r. r \<mapsto>\<^sub>a replicate n x>"
  unfolding hoare_triple_def snga_assn_def one_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps
  )
  done

lemma make_rule: "<emp> Array.make n f <\<lambda>r. r \<mapsto>\<^sub>a (map f [0 ..< n])>"
  unfolding hoare_triple_def snga_assn_def one_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps
  )
  done
    
lemma of_list_rule: "<emp> Array.of_list xs <\<lambda>r. r \<mapsto>\<^sub>a xs>"
  unfolding hoare_triple_def snga_assn_def one_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps
  )
  done

lemma length_rule:
  "<a \<mapsto>\<^sub>a xs> Array.len a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = length xs)>"
  unfolding hoare_triple_def snga_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps Array.length_def
  )
  done

text \<open>Note that the Boolean expression is placed at meta level and not 
  inside the precondition. This makes frame inference simpler.\<close>
lemma nth_rule:
  "\<lbrakk>i < length xs\<rbrakk> \<Longrightarrow> <a \<mapsto>\<^sub>a xs> Array.nth a i <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs ! i)>"
  unfolding hoare_triple_def snga_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps Array.length_def
  )
  done

lemma upd_rule:
  "\<lbrakk>i < length xs\<rbrakk> \<Longrightarrow> 
  <a \<mapsto>\<^sub>a xs> 
  Array.upd i x a 
  <\<lambda>r. (a \<mapsto>\<^sub>a (list_update xs i x)) * \<up>(r = a)>"
  unfolding hoare_triple_def snga_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps Array.length_def Array.update_def comp_def
  )
  done

lemma freeze_rule:
  "<a \<mapsto>\<^sub>a xs> Array.freeze a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs)>"
  unfolding hoare_triple_def snga_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps Array.length_def Array.update_def
  )
  done
  
lemma return_wp_rule:
  "<Q x> return x <Q>"
  unfolding hoare_triple_def Let_def
  apply (auto elim!: run_elims)
  apply (rule relH_refl)
  apply (simp add: in_range.simps)
  done

lemma return_sp_rule:
  "<P> return x <\<lambda>r. P * \<up>(r = x)>"
  unfolding hoare_triple_def Let_def
  apply (simp add: Abs_assn_inverse)
  apply (auto elim!: run_elims intro!: relH_refl intro: models_in_range)
  apply (simp add: in_range.simps)
  done

lemma raise_iff: 
  "<P> raise s <Q> \<longleftrightarrow> P = false"
  unfolding hoare_triple_def Let_def
  apply (rule iffI)
  apply (unfold bot_assn_def) []
  apply rule
  apply (auto simp add: run_raise_iff) []

  apply (auto simp add: run_raise_iff) []
  done

lemma raise_rule: "<false> raise s <Q>"
  by (simp add: raise_iff)

subsubsection \<open>Rules for Composed Commands\<close>
lemma bind_rule: 
  assumes T1: "<P> f <R>"
  assumes T2: "\<And>x. <R x> g x <Q>"
  shows "<P> bind f g <Q>"
  unfolding hoare_triple_def Let_def
  apply (intro allI impI)
  apply (elim conjE run_elims)
  apply (intro conjI)
proof -
  fix h as \<sigma>'' r'' \<sigma>' r'
  assume M: "(h,as) \<Turnstile> P" 
    and R1: "run f (Some h) \<sigma>' r'" 
    and R2: "run (g r') \<sigma>' \<sigma>'' r''"

  from hoare_tripleD[OF T1 M R1] have NO_E: "\<not> is_exn \<sigma>'" 
    and M': "(the_state \<sigma>', new_addrs h as (the_state \<sigma>')) \<Turnstile> R r'"
    and RH': "relH {a. a < lim h \<and> a \<notin> as} h (the_state \<sigma>')"
    and LIM: "lim h \<le> lim (the_state \<sigma>')"
    by auto

  from NO_E have [simp]: "Some (the_state \<sigma>') = \<sigma>'" by (cases \<sigma>') auto

  from hoare_tripleD[OF T2 M', simplified, OF R2] have 
    NO_E'': "\<not> is_exn \<sigma>''"
    and M'': "(the_state \<sigma>'',
      new_addrs (the_state \<sigma>') 
        (new_addrs h as (the_state \<sigma>')) (the_state \<sigma>'')) 
      \<Turnstile> Q r''"
    and RH'': 
    "relH 
      {a. a < lim (the_state \<sigma>') 
        \<and> a \<notin> new_addrs h as (the_state \<sigma>')
      }
      (the_state \<sigma>') (the_state \<sigma>'')"
    and LIM': "lim (the_state \<sigma>') \<le> lim (the_state \<sigma>'')" by auto
  
  show "\<not> is_exn \<sigma>''" by fact

  have  
    "new_addrs 
      (the_state \<sigma>') 
      (new_addrs h as (the_state \<sigma>')) 
      (the_state \<sigma>'') 
    = new_addrs h as (the_state \<sigma>'')" 
    using LIM LIM' 
    by (auto simp add: new_addrs_def)
  with M'' show 
    "(the_state \<sigma>'', new_addrs h as (the_state \<sigma>'')) \<Turnstile> Q r''"
    by simp

  note RH'
  also have "relH {a. a < lim h \<and> a \<notin> as} (the_state \<sigma>') (the_state \<sigma>'')"
    apply (rule relH_subset[OF RH''])
    using LIM LIM'
    by (auto simp: new_addrs_def)
  finally show "relH {a. a < lim h \<and> a \<notin> as} h (the_state \<sigma>'')" .

  note LIM
  also note LIM'
  finally show "lim h \<le> lim (the_state \<sigma>'')" .
qed

lemma if_rule:
  assumes  "b \<Longrightarrow> <P> f <Q>"
  assumes  "\<not>b \<Longrightarrow> <P> g <Q>"
  shows "<P> if b then f else g <Q>"
  using assms by auto

lemma if_rule_split:
  assumes  B: "b \<Longrightarrow> <P> f <Q1>"
  assumes  NB: "\<not>b \<Longrightarrow> <P> g <Q2>"
  assumes M: "\<And>x. (Q1 x * \<up>b) \<or>\<^sub>A (Q2 x * \<up>(\<not>b)) \<Longrightarrow>\<^sub>A Q x"
  shows "<P> if b then f else g <Q>"
  apply (cases b)
  apply simp_all
  apply (rule cons_post_rule)
  apply (erule B)
  apply (rule ent_trans[OF _ ent_disjI1[OF M]])
  apply simp

  apply (rule cons_post_rule)
  apply (erule NB)
  apply (rule ent_trans[OF _ ent_disjI2[OF M]])
  apply simp
  done

lemma split_rule: 
  assumes P: "<P> c <R>"
  assumes Q: "<Q> c <R>"
  shows "<P \<or>\<^sub>A Q> c <R>"
  unfolding hoare_triple_def
  apply (intro allI impI)
  apply (elim conjE)
  apply simp
  apply (erule disjE)
  using hoare_tripleD[OF P] apply simp
  using hoare_tripleD[OF Q] apply simp
  done

lemmas decon_if_split = if_rule_split split_rule
  \<comment> \<open>Use with care: Complete splitting of if statements\<close>

lemma case_prod_rule: 
  "(\<And>a b. x = (a, b) \<Longrightarrow> <P> f a b <Q>) \<Longrightarrow> <P> case x of (a, b) \<Rightarrow> f a b <Q>"
  by (auto split: prod.split)

lemma case_list_rule:
  "\<lbrakk> l=[] \<Longrightarrow> <P> fn <Q>; \<And>x xs. l=x#xs \<Longrightarrow> <P> fc x xs <Q> \<rbrakk> \<Longrightarrow> 
  <P> case_list fn fc l <Q>"
  by (auto split: list.split)

lemma case_option_rule:
  "\<lbrakk> v=None \<Longrightarrow> <P> fn <Q>; \<And>x. v=Some x \<Longrightarrow> <P> fs x <Q> \<rbrakk> 
  \<Longrightarrow> <P> case_option fn fs v <Q>"
  by (auto split: option.split)

lemma case_sum_rule:
  "\<lbrakk> \<And>x. v=Inl x \<Longrightarrow> <P> fl x <Q>; 
     \<And>x. v=Inr x \<Longrightarrow> <P> fr x <Q> \<rbrakk> 
  \<Longrightarrow> <P> case_sum fl fr v <Q>"
  by (auto split: sum.split)

lemma let_rule: "(\<And>x. x = t \<Longrightarrow> <P> f x <Q>) \<Longrightarrow> <P> Let t f <Q>"
  by (auto)

end
