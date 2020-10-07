section \<open>The abstract semantics is computable\<close>

theory AbsCFComp
imports AbsCF Computability FixTransform CPSUtils MapSets
begin

default_sort type

text \<open>
The point of the abstract semantics is that it is computable. To show this, we exploit the special structure of \<open>\<aF>\<close> and \<open>\<aC>\<close>: Each call adds some elements to the result set and joins this with the results from a number of recursive calls. So we separate these two actions into separate functions. These take as arguments the direct sum of \<open>\<afstate>\<close> and \<open>\<acstate>\<close>, i.e.\ we treat the two mutually recursive functions now as one.

\<open>abs_g\<close> gives the local result for the given argument.
\<close>

fixrec abs_g :: "('c::contour \<afstate> + 'c \<acstate>) discr \<rightarrow> 'c \<aans>"
  where "abs_g\<cdot>x = (case undiscr x of
              (Inl (PC (Lambda lab vs c, \<beta>), as, ve, b)) \<Rightarrow> {}
            | (Inl (PP (Plus c),[_,_,cnts],ve,b)) \<Rightarrow>
                     let b' = \<anb> b c;
                         \<beta>  = [c \<mapsto> b]
                     in {((c, \<beta>), cont) | cont . cont \<in> cnts}
            | (Inl (PP (prim.If ct cf),[_, cntts, cntfs],ve,b)) \<Rightarrow>
                  ((   let b' = \<anb> b ct;
                            \<beta> = [ct \<mapsto> b]
                        in {((ct, \<beta>), cnt) | cnt . cnt \<in> cntts}
                   )\<union>(
                       let b' = \<anb> b cf;
                            \<beta> = [cf \<mapsto> b]
                        in {((cf, \<beta>), cnt) | cnt . cnt \<in> cntfs}
                   ))
            | (Inl (AStop,[_],_,_)) \<Rightarrow> {}
            | (Inl _) \<Rightarrow> \<bottom>
            | (Inr (App lab f vs,\<beta>,ve,b)) \<Rightarrow>
                 let fs = \<aA> f \<beta> ve;
                     as = map (\<lambda>v. \<aA> v \<beta> ve) vs;
                     b' = \<anb> b lab
                  in {((lab, \<beta>),f') | f' . f'\<in> fs}
            | (Inr (Let lab ls c',\<beta>,ve,b)) \<Rightarrow> {}
        )"

text \<open>
\<open>abs_R\<close> gives the set of arguments passed to the recursive calls.
\<close>

fixrec abs_R :: "('c::contour \<afstate> + 'c \<acstate>) discr \<rightarrow> ('c::contour \<afstate> + 'c \<acstate>) discr set"
  where "abs_R\<cdot>x = (case undiscr x of
              (Inl (PC (Lambda lab vs c, \<beta>), as, ve, b)) \<Rightarrow>
               (if length vs = length as
                then let \<beta>' = \<beta> (lab \<mapsto> b);
                         ve' = ve \<union>. (\<Union>. (map (\<lambda>(v,a). {(v,b) := a}.) (zip vs as)))
                     in {Discr (Inr (c,\<beta>',ve',b))}
                else \<bottom>)
            | (Inl (PP (Plus c),[_,_,cnts],ve,b)) \<Rightarrow>
                     let b' = \<anb> b c;
                         \<beta>  = [c \<mapsto> b]
                     in (\<Union>cnt\<in>cnts. {Discr (Inl (cnt,[{}],ve,b'))})
            | (Inl (PP (prim.If ct cf),[_, cntts, cntfs],ve,b)) \<Rightarrow>
                  ((   let b' = \<anb> b ct;
                            \<beta> = [ct \<mapsto> b]
                        in (\<Union>cnt\<in>cntts . {Discr (Inl (cnt,[],ve,b'))})
                   )\<union>(
                       let b' = \<anb> b cf;
                            \<beta> = [cf \<mapsto> b]
                        in (\<Union>cnt\<in>cntfs . {Discr (Inl (cnt,[],ve,b'))})
                   ))
            | (Inl (AStop,[_],_,_)) \<Rightarrow> {}
            | (Inl _) \<Rightarrow> \<bottom>
            | (Inr (App lab f vs,\<beta>,ve,b)) \<Rightarrow>
                 let fs = \<aA> f \<beta> ve;
                     as = map (\<lambda>v. \<aA> v \<beta> ve) vs;
                     b' = \<anb> b lab
                  in (\<Union>f' \<in> fs. {Discr (Inl (f',as,ve,b'))})
            | (Inr (Let lab ls c',\<beta>,ve,b)) \<Rightarrow>
                 let b' = \<anb> b lab;
                     \<beta>' = \<beta> (lab \<mapsto> b');
                     ve' = ve \<union>. (\<Union>. (map (\<lambda>(v,l). {(v,b') := (\<aA> (L l) \<beta>' ve)}.) ls))
                 in {Discr (Inr (c',\<beta>',ve',b'))}
        )"

text \<open>
The initial argument vector, as created by \<open>\<aPR>\<close>.
\<close>

definition initial_r :: "prog \<Rightarrow> ('c::contour \<afstate> + 'c \<acstate>) discr"
  where "initial_r prog = Discr (Inl
     (the_elem (\<aA> (L prog) Map.empty {}.), [{AStop}], {}., \<abinit>))"

subsection \<open>Towards finiteness\<close>

text \<open>
We need to show that the set of possible arguments for a given program \<open>p\<close> is finite. Therefore, we define the set of possible procedures, of possible arguments to \<open>\<aF>\<close>, or possible arguments to \<open>\<aC>\<close> and of possible arguments.
\<close>

definition proc_poss :: "prog \<Rightarrow> 'c::contour proc set"
  where "proc_poss p = PC ` (lambdas p \<times> maps_over (labels p) UNIV) \<union> PP ` prims p \<union> {AStop}"

definition fstate_poss :: "prog \<Rightarrow> 'c::contour a_fstate set"
  where "fstate_poss p = (proc_poss p \<times> NList (Pow (proc_poss p)) (call_list_lengths p) \<times> smaps_over (vars p \<times> UNIV) (proc_poss p) \<times> UNIV)"

definition cstate_poss :: "prog \<Rightarrow> 'c::contour a_cstate set"
  where "cstate_poss p = (calls p \<times> maps_over (labels p) UNIV \<times> smaps_over (vars p \<times> UNIV) (proc_poss p) \<times> UNIV)"

definition arg_poss :: "prog \<Rightarrow> ('c::contour a_fstate + 'c a_cstate) discr set"
  where "arg_poss p = Discr ` (fstate_poss p <+> cstate_poss p)"

text \<open>
Using the auxiliary results from @{theory "Shivers-CFA.CPSUtils"}, we see that the argument space as defined here is finite.
\<close>

lemma finite_arg_space: "finite (arg_poss p)"
  unfolding arg_poss_def and cstate_poss_def and fstate_poss_def and proc_poss_def
  by (auto intro!: finite_cartesian_product finite_imageI maps_over_finite smaps_over_finite finite_UNIV finite_Nlist)


text \<open>
But is it closed? I.e.\ if we pass a member of \<open>arg_poss\<close> to \<open>abs_R\<close>, are the generated recursive call arguments also in \<open>arg_poss\<close>? This is shown in \<open>arg_space_complete\<close>, after proving an auxiliary result about the possible outcome of a call to \<open>\<aA>\<close> and an admissibility lemma.
\<close>

lemma evalV_possible:
  assumes f: "f \<in> \<aA> d \<beta> ve"
  and d: "d \<in> vals p"
  and ve: "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
  and \<beta>: "\<beta> \<in> maps_over (labels p) UNIV"
shows "f \<in> proc_poss p"
proof (cases "(d,\<beta>,ve)" rule: evalV_a.cases)
case (1 cl \<beta>' ve')
  thus ?thesis using f by auto next
case (2 prim \<beta>' ve')
  thus ?thesis using d f
    by (auto dest: vals1 simp add:proc_poss_def)
next
case (3 l var \<beta>' ve') 
  thus ?thesis using f d smaps_over_im[OF _ ve]
  by (auto split:option.split_asm dest: vals2)
next
case (4 l \<beta> ve)
  thus ?thesis using f d \<beta>
  by (auto dest!: vals3 simp add:proc_poss_def)
qed

lemma adm_subset: "cont (\<lambda>x. f x) \<Longrightarrow>  adm (\<lambda>x. f x \<subseteq> S)"
by (subst sqsubset_is_subset[THEN sym], intro adm_lemmas cont2cont)


lemma arg_space_complete:
  "state \<in> arg_poss p \<Longrightarrow> abs_R\<cdot>state \<subseteq> arg_poss p"
proof(induct rule: abs_R.induct[case_names Admissibility Bot Step])
case Admissibility show ?case
   by (intro adm_lemmas adm_subset cont2cont)
next
case Bot show ?case by simp next
case (Step abs_R) 
  note state = Step(2)
  show ?case
  proof (cases state)
  case (Discr state') show ?thesis
   proof (cases state')
     case (Inl fstate) show ?thesis
     using Inl Discr state
     proof (cases fstate rule: a_fstate_case, auto)
     txt \<open>Case Lambda\<close>
     fix l vs c \<beta> as ve b
     assume "Discr (Inl (PC (Lambda l vs c, \<beta>), as, ve, b)) \<in> arg_poss p"
       hence lam: "Lambda l vs c \<in> lambdas p"
       and  beta: "\<beta> \<in> maps_over (labels p) UNIV "
       and  ve: "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
       and  as: "as \<in> NList (Pow (proc_poss p)) (call_list_lengths p)"
       unfolding arg_poss_def fstate_poss_def proc_poss_def by auto

     from lam have "c \<in> calls p"
       by (rule lambdas1)

     moreover
     from lam have "l \<in> labels p"
       by (rule lambdas2)
     with beta have "\<beta>(l \<mapsto> b) \<in> maps_over (labels p) UNIV"
       by (rule maps_over_upd, auto)

     moreover
     from lam have vs: "set vs \<subseteq> vars p" by (rule lambdas3)
     from as have "\<forall> x \<in> set as. x \<in> Pow (proc_poss p)"
        unfolding NList_def nList_def by auto
     with vs have "ve \<union>. \<Union>.map (\<lambda>(v, y). { (v, b) := y}.) (zip vs as)
       \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)" (is "?ve' \<in> _")
       by (auto intro!: smaps_over_un[OF ve] smaps_over_Union smaps_over_singleton)
          (auto simp add:set_zip)

     ultimately
     have "(c, \<beta>(l \<mapsto> b), ?ve', b) \<in> cstate_poss p" (is "?cstate \<in> _")
       unfolding cstate_poss_def by simp
     thus "Discr (Inr ?cstate) \<in> arg_poss p"
       unfolding arg_poss_def by auto
     next

     txt \<open>Case Plus\<close>
     fix ve b l v1 v2 cnts cnt
     assume "Discr (Inl (PP (prim.Plus l), [v1, v2, cnts], ve, b)) \<in> arg_poss p"
         and "cnt \<in> cnts"
     hence "cnt \<in> proc_poss p" 
         and "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
       unfolding arg_poss_def fstate_poss_def NList_def nList_def
       by auto
     moreover
     have "[{}] \<in> NList (Pow (proc_poss p)) (call_list_lengths p)"
       unfolding call_list_lengths_def NList_def nList_def by auto
     ultimately
     have "(cnt, [{}], ve, \<anb> b l) \<in> fstate_poss p"
       unfolding fstate_poss_def by auto
     thus "Discr (Inl (cnt, [{}], ve, \<anb> b l)) \<in> arg_poss p"
       unfolding arg_poss_def by auto
     next
  
     txt \<open>Case If (true case)\<close>
     fix ve b l1 l2 v cntst cntsf cnt
     assume "Discr (Inl (PP (prim.If l1 l2), [v, cntst, cntsf], ve, b)) \<in> arg_poss p"
         and "cnt \<in> cntst"
     hence "cnt \<in> proc_poss p"
         and "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
       unfolding arg_poss_def fstate_poss_def NList_def nList_def
       by auto
     moreover
     have "[] \<in> NList (Pow (proc_poss p)) (call_list_lengths p)"
       unfolding call_list_lengths_def NList_def nList_def by auto
     ultimately
     have "(cnt, [], ve, \<anb> b l1) \<in> fstate_poss p"
       unfolding fstate_poss_def by auto
     thus "Discr (Inl (cnt, [], ve, \<anb> b l1)) \<in> arg_poss p"
       unfolding arg_poss_def by auto
     next
  
     txt \<open>Case If (false case)\<close>
     fix ve b l1 l2 v cntst cntsf cnt
     assume "Discr (Inl (PP (prim.If l1 l2), [v, cntst, cntsf], ve, b)) \<in> arg_poss p"
         and "cnt \<in> cntsf"
     hence "cnt \<in> proc_poss p"
         and "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
       unfolding arg_poss_def fstate_poss_def NList_def nList_def
       by auto
     moreover
     have "[] \<in> NList (Pow (proc_poss p)) (call_list_lengths p)"
       unfolding call_list_lengths_def NList_def nList_def by auto
     ultimately
     have "(cnt, [], ve, \<anb> b l2) \<in> fstate_poss p"
       unfolding fstate_poss_def by auto
     thus "Discr (Inl (cnt, [], ve, \<anb> b l2)) \<in> arg_poss p"
       unfolding arg_poss_def by auto
    qed
  next
  case (Inr cstate)
  show ?thesis proof(cases cstate rule: prod_cases4)
   case (fields c \<beta> ve b)
   show ?thesis using Discr Inr fields state proof(cases c, auto simp add:HOL.Let_def simp del:evalV_a.simps)

     txt \<open>Case App\<close>
     fix l d ds f
     assume arg: "Discr (Inr (App l d ds, \<beta>, ve, b)) \<in> arg_poss p"
       and f: "f \<in> \<aA> d \<beta> ve"
     hence c: "App l d ds \<in> calls p"
       and d: "d \<in> vals p"
       and ds: "set ds \<subseteq> vals p"
       and beta: "\<beta> \<in> maps_over (labels p) UNIV"
       and ve: "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
     by (auto simp add: arg_poss_def cstate_poss_def call_list_lengths_def dest: app1 app2)

     have len: "length ds \<in> call_list_lengths p"
       by (auto intro: rev_image_eqI[OF c] simp add: call_list_lengths_def)

     have "f \<in> proc_poss p"
       using f d ve beta by (rule evalV_possible)
     moreover
     have "map (\<lambda>v. \<aA> v \<beta> ve) ds \<in> NList (Pow (proc_poss p)) (call_list_lengths p)"
       using ds len
       unfolding NList_def by (auto simp add:nList_def intro!: evalV_possible[OF _ _ ve beta])
     ultimately 
     have "(f, map (\<lambda>v. \<aA> v \<beta> ve) ds, ve, \<anb> b l) \<in> fstate_poss p" (is "?fstate \<in> _")
       using ve 
       unfolding fstate_poss_def by simp
     thus "Discr (Inl ?fstate) \<in> arg_poss p"
       unfolding arg_poss_def by auto

   next
     txt \<open>Case Let\<close>
     fix l binds c'
     assume arg: "Discr (Inr (Let l binds c', \<beta>, ve, b)) \<in> arg_poss p"
     hence l: "l \<in> labels p"
       and c': "c' \<in> calls p"
       and vars: "fst ` set binds \<subseteq> vars p"
       and ls: "snd ` set binds \<subseteq> lambdas p"
       and beta: "\<beta> \<in> maps_over (labels p) UNIV"
       and ve: "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
     by (auto simp add: arg_poss_def cstate_poss_def call_list_lengths_def
              dest:let1 let2 let3 let4)

     have beta': "\<beta>(l \<mapsto> \<anb> b l) \<in> maps_over (labels p) UNIV" (is "?\<beta>' \<in> _")
       by (auto intro: maps_over_upd[OF beta l])

     moreover
     have "ve \<union>. \<Union>.map (\<lambda>(v, lam). { (v, \<anb> b l) := \<aA> (L lam) (\<beta>(l \<mapsto> \<anb> b l)) ve }.)
                binds
       \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)" (is "?ve' \<in> _")
       using vars ls beta'
       by (auto intro!: smaps_over_un[OF ve] smaps_over_Union)
          (auto intro!:smaps_over_singleton simp add: proc_poss_def)

     ultimately
     have "(c', ?\<beta>', ?ve', \<anb> b l) \<in> cstate_poss p" (is "?cstate \<in> _")
     using c' unfolding cstate_poss_def by simp
     thus "Discr (Inr ?cstate) \<in> arg_poss p"
       unfolding arg_poss_def by auto
   qed
 qed
qed
qed
qed

text \<open>
This result is now lifted to the powerset of \<open>abs_R\<close>.
\<close>

lemma arg_space_complete_ps: "states \<subseteq> arg_poss p \<Longrightarrow> (\<^ps>abs_R)\<cdot>states \<subseteq> arg_poss p"
using arg_space_complete unfolding powerset_lift_def by auto

text \<open>
We are not so much interested in the finiteness of the set of possible arguments but rather of the the set of occurring arguments, when we start with the initial argument. But as this is of course a subset of the set of possible arguments, this is not hard to show.
\<close>

lemma UN_iterate_less: 
  assumes start: "x \<in> S"
  and step: "\<And>y. y\<subseteq>S \<Longrightarrow> (f\<cdot>y) \<subseteq> S"
  shows "(\<Union>i. iterate i\<cdot>f\<cdot>{x}) \<subseteq> S"
proof- {
  fix i
  have "iterate i\<cdot>f\<cdot>{x} \<subseteq> S"
  proof(induct i)
    case 0 show ?case using \<open>x \<in> S\<close> by simp next
    case (Suc i) thus ?case using step[of "iterate i\<cdot>f\<cdot>{x}"] by simp
  qed
  } thus ?thesis by auto
qed

lemma args_finite: "finite (\<Union>i. iterate i\<cdot>(\<^ps>abs_R)\<cdot>{initial_r p})" (is "finite ?S")
proof (rule finite_subset[OF _finite_arg_space])
  have [simp]:"p \<in> lambdas p" by (cases p, simp)
  show "?S \<subseteq> arg_poss p"
  unfolding initial_r_def
  by  (rule UN_iterate_less[OF _ arg_space_complete_ps])
      (auto simp add:arg_poss_def fstate_poss_def proc_poss_def call_list_lengths_def NList_def nList_def
         intro!: imageI)
qed

subsection \<open>A decomposition\<close>

text \<open>
The functions \<open>abs_g\<close> and \<open>abs_R\<close> are derived from \<open>\<aF>\<close> and \<open>\<aC>\<close>. This connection has yet to expressed explicitly. 
\<close>

lemma Un_commute_helper:"(a \<union> b) \<union> (c \<union> d) = (a \<union> c) \<union> (b \<union> d)"
by auto

lemma a_evalF_decomp:
  "\<aF> = fst (sum_to_tup\<cdot>(fix\<cdot>(\<Lambda> f x. (\<Union>y\<in>abs_R\<cdot>x. f\<cdot>y) \<union> abs_g\<cdot>x)))"
apply (subst a_evalF_def)
apply (subst fix_transform_pair_sum)
apply (rule arg_cong [of _ _ "\<lambda>x. fst (sum_to_tup\<cdot>(fix\<cdot>x))"])
apply (simp)
apply (simp only: discr_app undiscr_Discr)
apply (rule cfun_eqI, rule cfun_eqI, simp)
apply (case_tac xa, rename_tac a, case_tac a, simp)
apply (case_tac aa rule:a_fstate_case, simp_all add: Un_commute_helper)
apply (case_tac b rule:prod_cases4)
apply (case_tac aa)
apply (simp_all add:HOL.Let_def)
done

subsection \<open>The iterative equation\<close>

text \<open>
Because of the special form of \<open>\<aF>\<close> (and thus \<open>\<aPR>\<close>) derived in the previous lemma, we can apply our generic results from @{theory "Shivers-CFA.Computability"} and express the abstract semantics as the image of a finite set under a computable function.
\<close>

lemma a_evalF_iterative:
  "\<aF>\<cdot>(Discr x) = \<^ps>abs_g\<cdot>(\<Union>i. iterate i\<cdot>(\<^ps>abs_R)\<cdot>{Discr (Inl x)})"
by (simp del:abs_R.simps abs_g.simps add: theorem12 Un_commute a_evalF_decomp)

lemma a_evalCPS_interative:
"\<aPR> prog = \<^ps>abs_g\<cdot>(\<Union>i. iterate i\<cdot>(\<^ps>abs_R)\<cdot>{initial_r prog})"
unfolding evalCPS_a_def and initial_r_def
by(subst a_evalF_iterative, simp del:abs_R.simps abs_g.simps evalV_a.simps)

end
