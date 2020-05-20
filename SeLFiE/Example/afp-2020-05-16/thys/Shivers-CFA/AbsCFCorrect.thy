section \<open>The abstract semantics is correct\<close>

theory AbsCFCorrect
  imports AbsCF ExCF "HOL-Library.Adhoc_Overloading"
begin

default_sort type

text \<open>
The intention of the abstract semantics is to safely approximate the real control flow. This means that every call recorded by the exact semantics must occur in the result provided by the abstract semantics, which in turn is allowed to predict more calls than actually done.
\<close>

subsection \<open>Abstraction functions\<close>

text \<open>
This relation is expressed by abstraction functions and approximation relations. For each of our data types, there is an abstraction function \<open>abs_<type>\<close>, mapping the a value from the exact setup to the corresponding value in the abstract view. The approximation relation then expresses the fact that one abstract value of such a type is safely approximated by another.

Because we need an abstraction function for contours, we extend the \<open>contour\<close> type class by the abstraction functions and two equations involving the \<open>nb\<close> and \<open>\<binit>\<close> symbols.
\<close>

class contour_a = contour +
  fixes abs_cnt :: "contour \<Rightarrow> 'a"
  assumes abs_cnt_nb[simp]: "abs_cnt (nb b lab) = \<anb> (abs_cnt b) lab"
     and abs_cnt_initial[simp]: "abs_cnt(\<binit>) = \<abinit>"

instantiation unit :: contour_a
begin
definition "abs_cnt _ = ()"
instance by standard auto
end

text \<open>
It would be unwieldly to always write out \<open>abs_<type> x\<close>. We would rather like to write \<open>|x|\<close> if the type of \<open>x\<close> is known, as Shivers does it as well. Isabelle allows one to use the same syntax for different symbols. In that case, it generates more than one parse tree and picks the (hopefully unique) tree that typechecks.

Unfortunately, this does not work well in our case: There are eight \<open>abs_<type>\<close> functions and some expressions later have multiple occurrences of these, causing an exponential blow-up of combinations.

Therefore, we use a module by Christian Sternagel and Alexander Krauss for ad-hoc overloading, where the choice of the concrete function is done at parse time and immediately. This is used in the following to set up the the symbol \<open>|_|\<close> for the family of abstraction functions.
\<close>

consts abs :: "'a \<Rightarrow> 'b" ("|_|")

adhoc_overloading
  abs abs_cnt

definition abs_benv :: "benv \<Rightarrow> 'c::contour_a \<abenv>"
  where "abs_benv \<beta> = map_option abs_cnt \<circ> \<beta>"

adhoc_overloading
  abs abs_benv

primrec abs_closure :: "closure \<Rightarrow> 'c::contour_a \<aclosure>"
  where "abs_closure (l,\<beta>) = (l,|\<beta>| )"

adhoc_overloading
  abs abs_closure

primrec abs_d :: "d \<Rightarrow> 'c::contour_a \<ad>"
  where "abs_d (DI i) = {}"
      | "abs_d (DP p) = {PP p}"
      | "abs_d (DC cl) = {PC |cl|}"
      | "abs_d (Stop) = {AStop}"

adhoc_overloading
  abs abs_d  

definition abs_venv :: "venv \<Rightarrow> 'c::contour_a \<avenv>"
  where "abs_venv ve = (\<lambda>(v,b_a). \<Union>{(case ve (v,b) of Some d \<Rightarrow> |d| | None \<Rightarrow> {}) | b. |b| = b_a })"

adhoc_overloading
  abs abs_venv

definition abs_ccache :: "ccache \<Rightarrow> 'c::contour_a \<accache>"
  where "abs_ccache cc = (\<Union>((c,\<beta>),d) \<in> cc . {((c,abs_benv \<beta>), p) | p . p\<in>abs_d d})"
(* equivalent, but I already have cont2cont for UNION
  where "abs_ccache cc = { ((c,abs_benv \<beta>),p) | c \<beta> p d . ((c,\<beta>),d) \<in> cc \<and> p \<in> abs_d d}" *)

adhoc_overloading
  abs abs_ccache

fun abs_fstate :: "fstate \<Rightarrow> 'c::contour_a \<afstate>"
  where "abs_fstate (d,ds,ve,b) = (the_elem |d|, map abs_d ds, |ve|, |b| )"

adhoc_overloading
  abs abs_fstate

fun abs_cstate :: "cstate \<Rightarrow> 'c::contour_a \<acstate>"
  where "abs_cstate (c,\<beta>,ve,b) = (c, |\<beta>|, |ve|, |b| )"

adhoc_overloading
  abs abs_cstate

subsection \<open>Lemmas about abstraction functions\<close>

text \<open>
Some results about the abstractions functions.
\<close>

lemma abs_benv_empty[simp]: "|Map.empty| = Map.empty"
unfolding abs_benv_def by simp

lemma abs_benv_upd[simp]: "|\<beta>(c\<mapsto>b)| = |\<beta>| (c \<mapsto> |b| )"
  unfolding abs_benv_def by simp

lemma the_elem_is_Proc:
  assumes "isProc cnt"
  shows "the_elem |cnt| \<in> |cnt|"
using assms by (cases cnt)auto

lemma [simp]: "|{}| = {}" unfolding abs_ccache_def by auto

lemma abs_cache_singleton [simp]: "|{((c,\<beta>),d)}| = {((c, |\<beta>| ), p) |p. p \<in> |d|}"
  unfolding abs_ccache_def by simp

lemma abs_venv_empty[simp]: "|Map.empty| = {}."
  apply (rule ext) by (auto simp add: abs_venv_def smap_empty_def)


subsection \<open>Approximation relation\<close>

text \<open>
The family of relations defined here capture the notion of safe approximation.
\<close>

consts approx :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<lessapprox> _")

definition venv_approx :: "'c \<avenv> \<Rightarrow>'c \<avenv> \<Rightarrow> bool"
  where "venv_approx = smap_less"

adhoc_overloading
  approx venv_approx

definition ccache_approx :: "'c \<accache> \<Rightarrow>'c \<accache> \<Rightarrow> bool"
  where "ccache_approx = less_eq"

adhoc_overloading
  approx ccache_approx

definition d_approx :: "'c \<ad> \<Rightarrow>'c \<ad> \<Rightarrow> bool"
  where "d_approx = less_eq"

adhoc_overloading
  approx d_approx

definition ds_approx :: "'c \<ad> list \<Rightarrow>'c \<ad> list \<Rightarrow> bool"
  where "ds_approx = list_all2 d_approx"

adhoc_overloading
  approx ds_approx

inductive fstate_approx :: "'c \<afstate> \<Rightarrow>'c \<afstate> \<Rightarrow> bool"
  where "\<lbrakk> ve \<lessapprox> ve' ; ds \<lessapprox> ds' \<rbrakk>
         \<Longrightarrow> fstate_approx (proc,ds,ve,b) (proc,ds',ve',b)"

adhoc_overloading
  approx fstate_approx

inductive cstate_approx :: "'c \<acstate> \<Rightarrow>'c \<acstate> \<Rightarrow> bool"
  where "\<lbrakk> ve \<lessapprox> ve' \<rbrakk> \<Longrightarrow> cstate_approx (c,\<beta>,ve,b) (c,\<beta>,ve',b)"

adhoc_overloading
  approx cstate_approx

subsection \<open>Lemmas about the approximation relation\<close>

text \<open>
Most of the following lemmas reduce an approximation statement about larger structures, as they are occurring the semantics functions, to statements about the components.
\<close>

lemma venv_approx_trans[trans]:
  fixes ve1 ve2 ve3 :: "'c \<avenv>"
  shows "\<lbrakk> ve1 \<lessapprox> ve2; ve2 \<lessapprox> ve3 \<rbrakk> \<Longrightarrow> (ve1 \<lessapprox> ve3)"
  unfolding venv_approx_def by (rule smap_less_trans)

lemma abs_venv_union: "|ve1 ++ ve2| \<lessapprox> |ve1| \<union>. |ve2|"
  by (auto simp add: venv_approx_def smap_less_def abs_venv_def smap_union_def, split option.split_asm, auto)

lemma abs_venv_map_of_rev: "|map_of (rev l)| \<lessapprox> \<Union>. (map (\<lambda>(v,k). |[v \<mapsto> k]| ) l)"
proof (induct l)
  case Nil show ?case unfolding abs_venv_def by (auto simp: venv_approx_def smap_less_def ) next
  case (Cons a l)
    obtain v k where "a=(v,k)" by (rule prod.exhaust)
    hence "|map_of (rev (a#l))| \<lessapprox> ( |[v \<mapsto> k]| \<union>. |map_of (rev l)| ):: 'a \<avenv>"
      by (auto intro: abs_venv_union)
    also
    have "\<dots> \<lessapprox> |[v \<mapsto> k]| \<union>. (\<Union>. (map (\<lambda>(v,k). |[v  \<mapsto> k]| ) l))"
      by (auto intro!:smap_union_mono[OF smap_less_refl Cons[unfolded venv_approx_def]] simp:venv_approx_def)
    also
    have "\<dots> = \<Union>. ( |[v \<mapsto> k]| # map (\<lambda>(v,k). |[v \<mapsto> k]| ) l)"
      by (rule smap_Union_union)
    also
    have "\<dots> = \<Union>. (map (\<lambda>(v,k). |[v \<mapsto> k]| ) (a#l))"
      using \<open>a = (v,k)\<close>
      by auto
    finally
    show ?case .
qed

lemma abs_venv_map_of: "|map_of l| \<lessapprox> \<Union>. (map (\<lambda>(v,k). |[v \<mapsto> k]| ) l)"
  using abs_venv_map_of_rev[of "rev l"] by simp

lemma abs_venv_singleton: "|[(v,b) \<mapsto> d]| = {(v,|b| ) := |d|}."
  by (rule ext, auto simp add:abs_venv_def smap_singleton_def smap_empty_def)

lemma ccache_approx_empty[simp]:
  fixes x :: "'c \<accache>"
  shows "{} \<lessapprox> x"
  unfolding ccache_approx_def by simp

lemmas ccache_approx_trans[trans] = subset_trans[where 'a = "((label \<times> 'c \<abenv>) \<times> 'c \<aproc>)", folded ccache_approx_def]
lemmas Un_mono_approx = Un_mono[where 'a = "((label \<times> 'c \<abenv>) \<times> 'c \<aproc>)", folded ccache_approx_def]
lemmas Un_upper1_approx = Un_upper1[where 'a = "((label \<times> 'c \<abenv>) \<times> 'c \<aproc>)", folded ccache_approx_def]
lemmas Un_upper2_approx = Un_upper2[where 'a = "((label \<times> 'c \<abenv>) \<times> 'c \<aproc>)", folded ccache_approx_def]

lemma abs_ccache_union: "|c1 \<union> c2| \<lessapprox> |c1| \<union> |c2|"
  unfolding ccache_approx_def abs_ccache_def by auto

lemma d_approx_empty[simp]: "{} \<lessapprox> (d::'c \<ad>)"
  unfolding d_approx_def by simp

lemma ds_approx_empty[simp]: "[] \<lessapprox> []"
  unfolding ds_approx_def by simp

subsection \<open>Lemma 7\<close>

text \<open>
Shivers' lemma 7 says that \<open>\<aA>\<close> safely approximates \<open>\<A>\<close>.
\<close>

lemma lemma7:
  assumes "|ve::venv| \<lessapprox> ve_a"
  shows "|\<A> f \<beta> ve| \<lessapprox> \<aA> f |\<beta>| ve_a"
proof(cases f)
case (R _ v)
  from assms have assm': "\<And>v b. case_option {} abs_d (ve (v,b)) \<lessapprox> ve_a (v,|b| )"
    by (auto simp add:d_approx_def abs_venv_def venv_approx_def smap_less_def elim!:allE)
  show ?thesis
    proof(cases "\<beta> (binder v)")
    case None thus ?thesis using R by auto next
    case (Some b)
      thus ?thesis using R assm'[of v b]
         by (auto simp add:abs_benv_def split:option.split)
  qed
qed (auto simp add:d_approx_def)


subsection \<open>Lemmas 8 and 9\<close>

text \<open>
The main goal of this section is to show that \<open>\<aF>\<close> safely approximates \<open>\<F>\<close> and that \<open>\<aC>\<close> safely approximates \<open>\<C>\<close>. This has to be shown at once, as the functions are mutually recursive and requires a fixed point induction. To that end, we have to augment the set of continuity lemmas.
\<close>

lemma cont2cont_abs_ccache[cont2cont,simp]:
  assumes "cont f"
  shows "cont (\<lambda>x. abs_ccache(f x))"
unfolding abs_ccache_def
using assms
by (rule cont2cont)(rule cont_const)

text \<open>
Shivers proves these lemmas using parallel fixed point induction over the two fixed points (the one from the exact semantics and the one from the abstract semantics). But it is simpler and equivalent to just do induction over the exact semantics and keep the abstract semantics functions fixed, so this is what I am doing.
\<close>


lemma lemma89:
 fixes fstate_a :: "'c::contour_a \<afstate>" and cstate_a :: "'c::contour_a \<acstate>"
 shows "|fstate| \<lessapprox> fstate_a \<Longrightarrow> |\<F>\<cdot>(Discr fstate)| \<lessapprox> \<aF>\<cdot>(Discr fstate_a)"
   and "|cstate| \<lessapprox> cstate_a \<Longrightarrow> |\<C>\<cdot>(Discr cstate)| \<lessapprox> \<aC>\<cdot>(Discr cstate_a)"
proof(induct arbitrary: fstate fstate_a cstate cstate_a rule: evalF_evalC_induct)
case Admissibility show ?case
  unfolding ccache_approx_def 
  by (intro adm_lemmas adm_subset adm_prod_split adm_not_conj adm_not_mem adm_single_valued cont2cont)
next
case Bottom {
  case 1 show ?case by simp next
  case 2 show ?case by simp next
}
next
case (Next evalF evalC) {
case 1
  obtain d ds ve b where fstate: "fstate = (d,ds,ve,b)"
    by (cases fstate, auto)
  moreover
  obtain proc ds_a ve_a b_a where fstate_a: "fstate_a = (proc,ds_a,ve_a,b_a)"
    by (cases fstate_a, auto)
  ultimately
  have abs_d: "the_elem |d| = proc"
   and abs_ds: "map abs_d ds \<lessapprox> ds_a"
   and abs_ve: "|ve| \<lessapprox> ve_a"
   and abs_b: "|b| = b_a"
  using 1 by (auto elim:fstate_approx.cases)

  from abs_ds have dslength: "length ds = length ds_a"
    by (auto simp add:ds_approx_def dest!:list_all2_lengthD)

  from fstate fstate_a abs_d abs_ds abs_ve abs_ds dslength
  show ?case
  proof(cases fstate rule:fstate_case, auto simp del:a_evalF.simps a_evalC.simps set_map)

  txt \<open>Case Lambda\<close>
  fix \<beta> and lab and vs:: "var list" and c
  assume ds_a_length: "length vs = length ds_a"

  have "|\<beta>(lab \<mapsto> b)| = |\<beta>| (lab \<mapsto> b_a)"
    unfolding below_fun_def using abs_b by simp
  moreover

  { have "|ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds)|
          \<lessapprox> |ve| \<union>. |map_of (rev (zip (map (\<lambda>v. (v, b)) vs) ds))|"
      unfolding map_upds_def by (intro abs_venv_union)
    also
    have "\<dots> \<lessapprox> ve_a  \<union>. (\<Union>. (map (\<lambda>(v,k). |[v \<mapsto> k]| ) (zip (map (\<lambda>v. (v, b)) vs) ds)))"
      using abs_ve abs_venv_map_of_rev
      by (auto intro:smap_union_mono simp add:venv_approx_def)
    also
    have "\<dots> = ve_a \<union>. (\<Union>. (map (\<lambda>(v,y). |[(v,b) \<mapsto> y]| ) (zip vs ds)))"
      by (auto simp add: zip_map1 o_def split_def)
    also
    have "\<dots> \<lessapprox> ve_a \<union>. (\<Union>. (map (\<lambda>(v,y). {(v,b_a) := y}.) (zip vs ds_a)))"
    proof-
      from abs_b abs_ds
      have "list_all2 venv_approx (map (\<lambda>(v, y). |[(v, b) \<mapsto> y]| ) (zip vs ds))
                                  (map (\<lambda>(v, y). {(v,b_a) := y}.) (zip vs ds_a))"
        by (auto simp add: ds_approx_def d_approx_def venv_approx_def abs_venv_singleton list_all2_conv_all_nth intro:smap_singleton_mono list_all2I)
      thus ?thesis
        by (auto simp add:venv_approx_def intro: smap_union_mono[OF smap_less_refl smap_Union_mono])
    qed
    finally
    have "|ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds)|
          \<lessapprox> ve_a \<union>. (\<Union>. (map (\<lambda>(v,y). {(v, b_a) := y}.) (zip vs ds_a)))".
  }
  ultimately
  have prem: "|(c, \<beta>(lab \<mapsto> b), ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds), b)|
        \<lessapprox> (c,  |\<beta>|(lab \<mapsto> b_a), ve_a \<union>. (\<Union>.(map (\<lambda>(v, y). {(v, b_a) := y}.) (zip vs ds_a))), b_a)"
    using abs_b
    by(auto intro:cstate_approx.intros simp add: abs_cstate.simps)

  show "|evalC\<cdot>(Discr (c, \<beta>(lab \<mapsto> b), ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds), b))|
        \<lessapprox> \<aF>\<cdot>(Discr (PC (Lambda lab vs c, |\<beta>| ), ds_a, ve_a, b_a))"
  using Next.hyps(2)[OF prem] ds_a_length
  by (subst a_evalF.simps, simp del:a_evalF.simps a_evalC.simps)

  next
  txt \<open>Case Plus\<close>
  fix lab a1 a2 cnt
  assume "isProc cnt"
  assume abs_ds': "[{}, {}, |cnt| ] \<lessapprox> ds_a"
  then obtain a1_a a2_a cnt_a where ds_a: "ds_a = [a1_a, a2_a, cnt_a]" and abs_cnt: "|cnt| \<lessapprox> cnt_a"
    unfolding ds_approx_def
    by (cases ds_a rule:list.exhaust[OF _ list.exhaust[OF _ list.exhaust, of _ _ "\<lambda>_ x. x"],  of _ _ "\<lambda>_ x. x"])
       (auto simp add:ds_approx_def)

  have new_elem: "|{((lab, [lab \<mapsto> b]), cnt)}| \<lessapprox> {((lab, [lab \<mapsto> b_a]), cont) |cont. cont \<in> cnt_a}"
    using abs_cnt and abs_b
    by (auto simp add:ccache_approx_def d_approx_def)

  have prem: "|(cnt, [DI (a1 + a2)], ve, nb b lab)| \<lessapprox>
              (the_elem |cnt|, [{}], ve_a, \<anb> b_a lab)"
    using abs_ve and abs_b
    by (auto intro:fstate_approx.intros simp add:ds_approx_def)

  have "|(evalF\<cdot>(Discr (cnt, [DI (a1 + a2)], ve, nb b lab)))|
       \<lessapprox> \<aF>\<cdot>(Discr (the_elem |cnt|, [{}], ve_a, \<anb> b_a lab))"
    by (rule Next.hyps(1)[OF prem])
  also have "\<dots> \<lessapprox> (\<Union>cnt\<in>cnt_a. \<aF>\<cdot>(Discr (cnt, [{}], ve_a, \<anb> b_a lab)))"
    using abs_cnt
    by (auto intro: the_elem_is_Proc[OF \<open>isProc cnt\<close>] simp del: a_evalF.simps simp add:ccache_approx_def d_approx_def)
  finally
  have old_elems: "|(evalF\<cdot>(Discr (cnt, [DI (a1 + a2)], ve, nb b lab)))|
       \<lessapprox> (\<Union>cnt\<in>cnt_a. \<aF>\<cdot>(Discr (cnt, [{}], ve_a, \<anb> b_a lab)))".

  have "|((evalF\<cdot>(Discr (cnt, [DI (a1 + a2)], ve, nb b lab)))
          \<union> {((lab, [lab \<mapsto> b]), cnt)})|
        \<lessapprox> |(evalF\<cdot>(Discr (cnt, [DI (a1 + a2)], ve, nb b lab)))|
          \<union> |{((lab, [lab \<mapsto> b]), cnt)}|"
    by (rule abs_ccache_union)
  also
  have "\<dots> \<lessapprox>
        (\<Union>cnt\<in>cnt_a. \<aF>\<cdot>(Discr (cnt, [{}], ve_a, \<anb> b_a lab)))
        \<union> {((lab, [lab \<mapsto> b_a]), cont) |cont. cont \<in> cnt_a}"
    by (rule Un_mono_approx[OF old_elems new_elem])
  finally
  show "|insert ((lab, [lab \<mapsto> b]), cnt)
                (evalF\<cdot>(Discr (cnt, [DI (a1 + a2)], ve, nb b lab)))|
        \<lessapprox> \<aF>\<cdot>(Discr (PP (prim.Plus lab), ds_a, ve_a, b_a))"
    using ds_a by (subst a_evalF.simps)(auto simp del:a_evalF.simps)
  next

  txt \<open>Case If (true branch)\<close>
  fix ct cf v cntt cntf
  assume "isProc cntt"
  assume "isProc cntf"
  assume abs_ds': "[{}, |cntt|, |cntf| ] \<lessapprox> ds_a"
  then obtain v_a cntt_a cntf_a where ds_a: "ds_a = [v_a, cntt_a, cntf_a]"
                              and abs_cntt: "|cntt| \<lessapprox> cntt_a"
                              and abs_cntf: "|cntf| \<lessapprox> cntf_a"
    by (cases ds_a rule:list.exhaust[OF _ list.exhaust[OF _ list.exhaust, of _ _ "\<lambda>_ x. x"],  of _ _ "\<lambda>_ x. x"])
       (auto simp add:ds_approx_def)

  let ?c = "ct::label" and ?cnt = cntt and ?cnt_a = cntt_a

  have new_elem: "|{((?c, [?c \<mapsto> b]), ?cnt)}| \<lessapprox> {((?c, [?c \<mapsto> b_a]), cont) |cont. cont \<in> ?cnt_a}"
    using abs_cntt and abs_cntf and abs_b 
    by (auto simp add:ccache_approx_def d_approx_def)

  have prem: "|(?cnt, [], ve, nb b ?c)| \<lessapprox>
              (the_elem |?cnt|, [], ve_a, \<anb> b_a ?c)"
    using abs_ve and abs_b
    by (auto intro:fstate_approx.intros)

  have "|evalF\<cdot>(Discr (?cnt, [], ve, nb b ?c))|
       \<lessapprox> \<aF>\<cdot>(Discr (the_elem |?cnt|, [], ve_a, \<anb> b_a ?c))"
    by (rule Next.hyps(1)[OF prem])
  also have "\<dots> \<lessapprox> (\<Union>cnt\<in>?cnt_a. \<aF>\<cdot>(Discr (cnt, [], ve_a, \<anb> b_a ?c)))"
    using abs_cntt and abs_cntf
    by (auto intro: the_elem_is_Proc[OF \<open>isProc ?cnt\<close>] simp del: a_evalF.simps simp add:ccache_approx_def d_approx_def)

  finally
  have old_elems: "|evalF\<cdot>(Discr (?cnt, [], ve, nb b ?c))|
       \<lessapprox> (\<Union>cnt\<in>?cnt_a. \<aF>\<cdot>(Discr (cnt, [], ve_a, \<anb> b_a ?c)))".

  have "|evalF\<cdot>(Discr (?cnt, [], ve, nb b ?c))
          \<union> {((?c, [?c \<mapsto> b]), ?cnt)}|
        \<lessapprox> |evalF\<cdot>(Discr (?cnt, [], ve, nb b ?c))|
          \<union> |{((?c, [?c \<mapsto> b]), ?cnt)}|"
    by (rule abs_ccache_union)
  also
  have "\<dots> \<lessapprox>
        (\<Union>cnt\<in>?cnt_a. \<aF>\<cdot>(Discr (cnt, [], ve_a, \<anb> b_a ?c)))
        \<union> {((?c, [?c \<mapsto> b_a]), cont) |cont. cont \<in> ?cnt_a}"
    by (rule Un_mono_approx[OF old_elems new_elem])
  also
  have "\<dots> \<lessapprox>
        ((\<Union>cnt\<in>cntt_a. \<aF>\<cdot>(Discr (cnt, [], ve_a, \<anb> b_a ct)))
          \<union> {((ct, [ct \<mapsto> b_a]), cont) |cont. cont \<in> cntt_a})
      \<union> ((\<Union>cnt\<in>cntf_a. \<aF>\<cdot>(Discr (cnt, [], ve_a, \<anb> b_a cf)))
          \<union> {((cf, [cf \<mapsto> b_a]), cont) |cont. cont \<in> cntf_a})"
    by (rule Un_upper1_approx|rule Un_upper2_approx)
  finally
  show "|insert ((?c, [?c \<mapsto> b]), ?cnt)
                (evalF\<cdot>(Discr (?cnt, [], ve, nb b ?c)))| \<lessapprox>
          \<aF>\<cdot>(Discr (PP (prim.If ct cf), ds_a, ve_a, b_a))"
    using ds_a by (subst a_evalF.simps)(auto simp del:a_evalF.simps)
  next

  txt \<open>Case If (false branch). We use schematic variable to keep this similar to the true branch.\<close>
  fix ct cf v cntt cntf
  assume "isProc cntt"
  assume "isProc cntf"
  assume abs_ds': "[{}, |cntt|, |cntf| ] \<lessapprox> ds_a"
  then obtain v_a cntt_a cntf_a where ds_a: "ds_a = [v_a, cntt_a, cntf_a]"
                              and abs_cntt: "|cntt| \<lessapprox> cntt_a"
                              and abs_cntf: "|cntf| \<lessapprox> cntf_a"
    by (cases ds_a rule:list.exhaust[OF _ list.exhaust[OF _ list.exhaust, of _ _ "\<lambda>_ x. x"],  of _ _ "\<lambda>_ x. x"])
       (auto simp add:ds_approx_def)

  let ?c = "cf::label" and ?cnt = cntf and ?cnt_a = cntf_a

  have new_elem: "|{((?c, [?c \<mapsto> b]), ?cnt)}| \<lessapprox> {((?c, [?c \<mapsto> b_a]), cont) |cont. cont \<in> ?cnt_a}"
    using abs_cntt and abs_cntf and abs_b 
    by (auto simp add:ccache_approx_def d_approx_def)

  have prem: "|(?cnt, [], ve, nb b ?c)| \<lessapprox>
              (the_elem |?cnt|, [], ve_a, \<anb> b_a ?c)"
    using abs_ve and abs_b
    by (auto intro:fstate_approx.intros)

  have "|evalF\<cdot>(Discr (?cnt, [], ve, nb b ?c))|
       \<lessapprox> \<aF>\<cdot>(Discr (the_elem |?cnt|, [], ve_a, \<anb> b_a ?c))"
    by (rule Next.hyps(1)[OF prem])
  also have "\<dots> \<lessapprox> (\<Union>cnt\<in>?cnt_a. \<aF>\<cdot>(Discr (cnt, [], ve_a, \<anb> b_a ?c)))"
    using abs_cntt and abs_cntf
    by (auto intro: the_elem_is_Proc[OF \<open>isProc ?cnt\<close>] simp del: a_evalF.simps simp add:ccache_approx_def d_approx_def)

  finally
  have old_elems: "|evalF\<cdot>(Discr (?cnt, [], ve, nb b ?c))|
       \<lessapprox> (\<Union>cnt\<in>?cnt_a. \<aF>\<cdot>(Discr (cnt, [], ve_a, \<anb> b_a ?c)))".

  have "|evalF\<cdot>(Discr (?cnt, [], ve, nb b ?c))
          \<union> {((?c, [?c \<mapsto> b]), ?cnt)}|
        \<lessapprox> |evalF\<cdot>(Discr (?cnt, [], ve, nb b ?c))|
          \<union> |{((?c, [?c \<mapsto> b]), ?cnt)}|"
    by (rule abs_ccache_union)
  also
  have "\<dots> \<lessapprox>
        (\<Union>cnt\<in>?cnt_a. \<aF>\<cdot>(Discr (cnt, [], ve_a, \<anb> b_a ?c)))
        \<union> {((?c, [?c \<mapsto> b_a]), cont) |cont. cont \<in> ?cnt_a}"
    by (rule Un_mono_approx[OF old_elems new_elem])
  also
  have "\<dots> \<lessapprox>
        ((\<Union>cnt\<in>cntt_a. \<aF>\<cdot>(Discr (cnt, [], ve_a, \<anb> b_a ct)))
          \<union> {((ct, [ct \<mapsto> b_a]), cont) |cont. cont \<in> cntt_a})
      \<union> ((\<Union>cnt\<in>cntf_a. \<aF>\<cdot>(Discr (cnt, [], ve_a, \<anb> b_a cf)))
          \<union> {((cf, [cf \<mapsto> b_a]), cont) |cont. cont \<in> cntf_a})"
    by (rule Un_upper1_approx|rule Un_upper2_approx)
  finally
  show "|insert ((?c, [?c \<mapsto> b]), ?cnt)
                (evalF\<cdot>(Discr (?cnt, [], ve, nb b ?c)))| \<lessapprox>
          \<aF>\<cdot>(Discr (PP (prim.If ct cf), ds_a, ve_a, b_a))"
    using ds_a by (subst a_evalF.simps)(auto simp del:a_evalF.simps)
 qed
next
case 2
  obtain c \<beta> ve b where cstate: "cstate = (c,\<beta>,ve,b)"
    by (cases cstate, auto)
  moreover
  obtain c_a \<beta>_a ds_a ve_a b_a where cstate_a: "cstate_a = (c_a,\<beta>_a,ve_a,b_a)"
    by (cases cstate_a, auto)
  ultimately
  have abs_c: "c = c_a"
   and abs_\<beta>: "|\<beta>| = \<beta>_a"
   and abs_ve: "|ve| \<lessapprox> ve_a"
   and abs_b: "|b| = b_a"
  using 2 by (auto elim:cstate_approx.cases)

  from cstate cstate_a abs_c abs_\<beta> abs_b
  show ?case
  proof(cases c, auto simp add:HOL.Let_def simp del:a_evalF.simps a_evalC.simps set_map evalV.simps)

  txt \<open>Case App\<close>
  fix lab f vs
  let ?d = "\<A> f \<beta> ve"
  assume "isProc ?d"

  have "map (abs_d \<circ> (\<lambda>v. \<A> v \<beta> ve)) vs \<lessapprox> map (\<lambda>v. \<aA> v \<beta>_a ve_a) vs"
    using abs_\<beta> and lemma7[OF abs_ve, of _ \<beta>]
    by (auto intro!: list_all2I simp add:set_zip ds_approx_def)

  hence "|evalF\<cdot>(Discr (?d, map (\<lambda>v. \<A> v \<beta> ve) vs, ve, nb b lab))|
     \<lessapprox> \<aF>\<cdot>(Discr(the_elem |?d|, map (\<lambda>v. \<aA> v \<beta>_a ve_a) vs, ve_a, \<anb> |b| lab))"
    using abs_ve and abs_cnt_nb and abs_b
    by -(rule Next.hyps(1),auto intro:fstate_approx.intros)
  also have "\<dots> \<lessapprox> (\<Union>f'\<in>\<aA> f \<beta>_a ve_a.
              \<aF>\<cdot>(Discr(f', map (\<lambda>v. \<aA> v \<beta>_a ve_a) vs, ve_a, \<anb> |b| lab)))"
    using lemma7[OF abs_ve] the_elem_is_Proc[OF \<open>isProc ?d\<close>] abs_\<beta>
    by (auto simp del: a_evalF.simps simp add:d_approx_def ccache_approx_def)
  finally
  have old_elems: "
     |evalF\<cdot>(Discr (\<A> f \<beta> ve, map (\<lambda>v. \<A> v \<beta> ve) vs, ve, nb b lab))|
     \<lessapprox> (\<Union>f'\<in> \<aA> f \<beta>_a ve_a.
              \<aF>\<cdot>(Discr(f', map (\<lambda>v. \<aA> v \<beta>_a ve_a) vs, ve_a, \<anb> |b| lab)))"
    by auto

  have new_elem: "|{((lab, \<beta>), \<A> f \<beta> ve)}|
                  \<lessapprox> {((lab, \<beta>_a), f') |f'. f' \<in> \<aA> f \<beta>_a ve_a}"
    using abs_\<beta> and lemma7[OF abs_ve]
    by(auto simp add:ccache_approx_def d_approx_def)
 
  have "|evalF\<cdot>(Discr (\<A> f \<beta> ve, map (\<lambda>v. \<A> v \<beta> ve) vs, ve, nb b lab))
        \<union> {((lab, \<beta>), \<A> f \<beta> ve)}|
        \<lessapprox> |evalF\<cdot>(Discr (\<A> f \<beta> ve, map (\<lambda>v. \<A> v \<beta> ve) vs, ve, nb b lab))|
        \<union> |{((lab, \<beta>), \<A> f \<beta> ve)}|"
    by (rule abs_ccache_union)
  also have "\<dots>
        \<lessapprox> (\<Union>f'\<in>\<aA> f \<beta>_a ve_a.
              \<aF>\<cdot>(Discr(f', map (\<lambda>v. \<aA> v \<beta>_a ve_a) vs, ve_a, \<anb> |b| lab)))
        \<union> {((lab, \<beta>_a), f') |f'. f' \<in> \<aA> f \<beta>_a ve_a}"
    by (rule Un_mono_approx[OF old_elems new_elem])
  finally
  show "|insert ((lab, \<beta>), \<A> f \<beta> ve)
                (evalF\<cdot>(Discr (\<A> f \<beta> ve, map (\<lambda>v. \<A> v \<beta> ve) vs, ve, nb b lab)))|
        \<lessapprox> \<aC>\<cdot>(Discr (App lab f vs, |\<beta>|, ve_a, |b| ))"
    using abs_\<beta>
    by (subst a_evalC.simps)(auto simp add: HOL.Let_def simp del:a_evalF.simps)
  next

  txt \<open>Case Let\<close>
  fix lab binds c'

  have "|\<beta>(lab \<mapsto> nb b lab)| =
        \<beta>_a(lab \<mapsto> \<anb> |b| lab)"
    using abs_\<beta> and abs_b
    by simp
  moreover
  have "|map_of (map (\<lambda>(v, l). ((v, nb b lab),
                                 DC (l, \<beta>(lab \<mapsto> nb b lab))))
                     binds)|
    \<lessapprox> \<Union>. (map (\<lambda>(v, l).
              {(v, \<anb> |b| lab) :=  {PC (l, \<beta>_a(lab \<mapsto> \<anb> |b| lab))}}.)
              binds)"
    using abs_b and abs_\<beta>
    apply -
    apply (rule venv_approx_trans[OF abs_venv_map_of])
    apply (auto intro:smap_union_mono list_all2I
              simp add:venv_approx_def o_def set_zip abs_venv_singleton split_def smap_less_refl)
    done
  hence "|ve ++ map_of
            (map (\<lambda>(v, l).
                   ((v, nb b lab),
                    DC (l, \<beta>(lab \<mapsto> nb b lab))))
                  binds)| \<lessapprox>
        ve_a \<union>.
        (\<Union>.
          (map (\<lambda>(v, l).
            {(v, \<anb> |b| lab) :=  {PC (l, \<beta>_a(lab \<mapsto> \<anb> |b| lab))}}.)
            binds))"
    by (rule venv_approx_trans[OF abs_venv_union
      smap_union_mono[OF abs_ve[unfolded venv_approx_def], folded venv_approx_def]])
  ultimately
  have "|evalC\<cdot>(Discr(c', \<beta>(lab \<mapsto> nb b lab),
            ve ++ map_of
                  (map (\<lambda>(v, l). ((v, nb b lab), DC (l, \<beta>(lab \<mapsto> nb b lab)))) binds),
            nb b lab))|
    \<lessapprox> \<aC>\<cdot>(Discr (c', \<beta>_a(lab \<mapsto> \<anb> |b| lab),
            ve_a \<union>.
             (\<Union>. (map (\<lambda>(v, l).
                   {(v, \<anb> |b| lab) :=  {PC (l, \<beta>_a(lab \<mapsto> \<anb> |b| lab))}}.)
                   binds)),
         \<anb> |b| lab))"
    using abs_cnt_nb and abs_b
    by -(rule Next.hyps(2),auto intro: cstate_approx.intros)

  thus "|evalC\<cdot>(Discr (c', \<beta>(lab \<mapsto> nb b lab),
                      ve ++ map_of (map (\<lambda>(v, l).((v, nb b lab),\<A> (L l) (\<beta>(lab \<mapsto> nb b lab)) ve)) binds),
                      nb b lab))| \<lessapprox>
          \<aC>\<cdot>(Discr (call.Let lab binds c', |\<beta>|, ve_a, |b| ))"
    using abs_\<beta>
    by (subst a_evalC.simps)(auto simp add: HOL.Let_def simp del:a_evalC.simps)
  qed
}
qed

text \<open>
And finally, we lift this result to \<open>\<aPR>\<close> and \<open>\<PR>\<close>.
\<close>

lemma lemma6: "|\<PR> l| \<lessapprox> \<aPR> l"
  unfolding evalCPS_def evalCPS_a_def
  by (auto intro!:lemma89 fstate_approx.intros simp del:evalF.simps a_evalF.simps
      simp add: ds_approx_def d_approx_def venv_approx_def)
end
