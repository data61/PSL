(*  Title:      perfect/Safety_Perfect.thy
    Author:     Sven Linker

Distance and Lane change controller for cars with perfect sensors.
Safety theorem and invariance with respect to switching views.
*)

section\<open>Safety for Cars with Perfect Sensors\<close>
text\<open>
This section contains the definition of requirements for
lane change and distance controllers for cars, with the assumption
of perfect sensors. Using these definitions, we show that safety
is an invariant along all possible behaviour of cars.
\<close>

theory Safety_Perfect
  imports HMLSL_Perfect
begin
  
context hmlsl_perfect
begin
interpretation hmlsl : hmlsl "perfect :: cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
proof unfold_locales   
  fix e ts c
  show " 0 < perfect e ts c" 
    by (metis less_add_same_cancel2 less_trans perfect_def traffic.psGeZero
        traffic.sdGeZero) 
qed

notation hmlsl.re ("re'(_')")
notation hmlsl.cl("cl'(_')")
notation hmlsl.len ("len")
  
text\<open>
Safety in the context of HMLSL means the absence of overlapping
reservations. Using the somewhere modality, this is easy to formalise. 
\<close>
abbreviation safe::"cars\<Rightarrow>\<sigma>" 
  where "safe e \<equiv> \<^bold>\<forall> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<rightarrow> \<^bold>\<not> \<^bold>\<langle>re(c) \<^bold>\<and> re(e) \<^bold>\<rangle>" 

text\<open>
The distance controller ensures, that as long as the cars do not try
to change their lane, they keep their distance. More formally,
if the reservations of two cars do not overlap, they will also not
overlap after an arbitrary amount of time passed. Observe that
the cars are allowed to change their dynamical behaviour, i.e.,
to accelerate and brake.
\<close>

abbreviation DC::"\<sigma>"
  where "DC \<equiv> \<^bold>G(\<^bold>\<forall> c d. \<^bold>\<not>(c \<^bold>= d) \<^bold>\<rightarrow>
                   \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<tau> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle>)"

text\<open>
To identify possibly dangerous situations during a lane change manoeuvre, 
we use the \emph{potential collision check}. It allows us to identify
situations, where the claim of a car \(d\) overlaps with 
any part of the car \(c\).
\<close>

abbreviation pcc::"cars \<Rightarrow> cars \<Rightarrow> \<sigma>" 
  where "pcc c d \<equiv> \<^bold>\<not> (c \<^bold>= d) \<^bold>\<and> \<^bold>\<langle> cl(d) \<^bold>\<and> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<rangle>"

text \<open>
The only restriction the lane change controller imposes onto the cars is
that in the case of a potential collision, they are not allowed to change
the claim into a reservation. 
\<close>

abbreviation LC::"\<sigma>"
  where "LC \<equiv> \<^bold>G ( \<^bold>\<forall>d.( \<^bold>\<exists> c. pcc c d) \<^bold>\<rightarrow> \<^bold>\<box>r(d) \<^bold>\<bottom>)  "
    

text\<open>
The safety theorem is as follows. If the controllers of all
cars adhere to the specifications given by \(LC\) and \(DC\),
and we start with an initially safe traffic snapshot, then
all reachable traffic snapshots are also safe.
\<close>
    
theorem safety:"\<Turnstile>( \<^bold>\<forall>e. safe e ) \<^bold>\<and> DC \<^bold>\<and> LC \<^bold>\<rightarrow> \<^bold>G (\<^bold>\<forall> e. safe e)"
proof (rule allI|rule impI)+
  fix ts v ts' 
  fix e c::cars
  assume assm:"ts,v \<Turnstile> ( \<^bold>\<forall>e. safe e ) \<^bold>\<and> DC \<^bold>\<and> LC" 
  assume  abs:"ts \<^bold>\<Rightarrow> ts'"
  assume nequals: "ts,v \<Turnstile>\<^bold>\<not>(c \<^bold>=e)"
  from assm have init:"ts,v \<Turnstile> ( \<^bold>\<forall>e. safe e )" by simp
  from assm have DC :"ts,v \<Turnstile> DC" by simp
  from assm have LC: "ts,v \<Turnstile> LC" by simp
  from abs show "ts',move ts ts' v \<Turnstile>  \<^bold>\<not> \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle> " 
  proof (induction)
    case (refl) 
    have "move ts ts v = v" using traffic.move_nothing by simp
    thus ?case using init traffic.move_nothing nequals  by auto
  next
    case (evolve ts' ts'' )
    have local_DC:
      "ts',move ts ts' v \<Turnstile> \<^bold>\<forall> c d. \<^bold>\<not>(c \<^bold>= d) \<^bold>\<rightarrow>
                               \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<tau> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle>"
      using "evolve.hyps" DC by simp
    show ?case 
    proof 
      assume e_def:" (ts'',move ts ts'' v \<Turnstile>  \<^bold>\<langle>re(c) \<^bold>\<and> re(e) \<^bold>\<rangle>)"
      from "evolve.IH"  and nequals have 
        ts'_safe:"ts',move ts ts' v \<Turnstile> \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by fastforce
      hence no_coll_after_evol:"ts',move ts ts' v \<Turnstile> \<^bold>\<box>\<^bold>\<tau> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
        using local_DC by blast
      have move_eq:"move ts' ts'' (move ts ts' v) = move ts ts'' v" 
        using "evolve.hyps" traffic.abstract.evolve traffic.abstract.refl 
          traffic.move_trans 
        by blast
      from no_coll_after_evol and "evolve.hyps" have 
        "ts'',move ts' ts'' (move ts ts' v) \<Turnstile>  \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"  
        by blast
      thus False using e_def using  move_eq by fastforce
    qed
  next
    case (cr_res ts' ts'')
    have local_LC: "ts',move ts ts' v \<Turnstile>( \<^bold>\<forall>d.( \<^bold>\<exists> c. pcc c d) \<^bold>\<rightarrow> \<^bold>\<box>r(d) \<^bold>\<bottom>)" 
      using LC "cr_res.hyps" by blast
    have "move ts ts' v = move ts' ts'' (move ts ts' v)" 
      using traffic.move_stability_res "cr_res.hyps" traffic.move_trans 
      move_stability_clm by auto
    hence move_stab: "move ts ts' v = move ts ts'' v" 
      by (metis traffic.abstract.simps cr_res.hyps traffic.move_trans)
    show ?case 
    proof (rule)
      assume e_def:" (ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle>re(c) \<^bold>\<and> re(e) \<^bold>\<rangle>)"
      obtain d where d_def: "ts' \<^bold>\<midarrow>r(d) \<^bold>\<rightarrow> ts''" using "cr_res.hyps" by best
      have "d = e \<or> d \<noteq> e" by simp
      thus False
      proof
        assume eq:"d = e"
        hence e_trans:"ts' \<^bold>\<midarrow>r(e) \<^bold>\<rightarrow> ts''" using d_def by simp
        from e_def have "ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by auto
        hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" 
          using view.somewhere_leq   
          by meson
        then obtain v' where v'_def:
          "(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
          by blast
        with backwards_res_act have "ts',v' \<Turnstile>   re(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e))"
          using e_def  backwards_res_stab nequals
          by (metis (no_types, lifting) d_def eq)
        hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts',v' \<Turnstile> re(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e)))"  
          using  v'_def by blast
        hence "ts',move ts ts'' v \<Turnstile>\<^bold>\<langle> re(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e)) \<^bold>\<rangle>"
          using view.somewhere_leq by meson
        hence "ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> re(c) \<^bold>\<and> cl(e)\<^bold>\<rangle> " 
          using hmlsl.somewhere_and_or_distr by blast 
        thus False 
        proof
          assume assm':"ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
          have "ts',move ts ts' v \<Turnstile> \<^bold>\<not> (c \<^bold>= e)" using nequals by blast
          thus False using assm' cr_res.IH e_def move_stab by force
        next
          assume assm':"ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> cl(e)\<^bold>\<rangle>"
          hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> cl(e)\<^bold>\<rangle>" 
            using e_def nequals by force
          hence "ts',move ts ts'' v \<Turnstile>\<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> cl(e) \<^bold>\<and> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<rangle>" by blast
          hence pcc:"ts',move ts ts'' v \<Turnstile> pcc c e" by blast
          have "ts',move ts ts'' v \<Turnstile>( \<^bold>\<exists> c. pcc c e) \<^bold>\<rightarrow> \<^bold>\<box>r(e) \<^bold>\<bottom>  " 
            using local_LC move_stab by fastforce
          hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<box>r(e) \<^bold>\<bottom>" using pcc by blast
          thus "ts'',move ts ts'' v \<Turnstile> \<^bold>\<bottom>" using e_trans by blast
        qed
      next 
        assume neq:"d \<noteq> e"
        have "c=d \<or> c \<noteq> d" by simp
        thus False 
        proof
          assume neq2:"c \<noteq> d" 
          from e_def have "ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by auto
          hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
            using view.somewhere_leq   
            by meson
          then obtain v' where v'_def:
            "(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
            by blast
          with backwards_res_stab have overlap: "ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e)"
            using e_def  backwards_res_stab nequals neq2 
            by (metis (no_types, lifting) d_def neq)
          hence unsafe2:"ts',move ts ts'' v \<Turnstile> \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" 
            using  nequals view.somewhere_leq v'_def by blast
          from cr_res.IH have "ts',move ts ts'' v \<Turnstile> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
            using move_stab by force
          thus False using unsafe2 by best
        next
          assume eq2:"c = d"
          hence e_trans:"ts' \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts''" using d_def by simp
          from e_def have "ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by auto
          hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
            using view.somewhere_leq   
            by meson
          then obtain v' where v'_def:
            "(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
            by blast
          with backwards_res_act have "ts',v' \<Turnstile> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<and> re(e)"
            using e_def  backwards_res_stab nequals 
            by (metis (no_types, lifting) d_def eq2)
          hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts',v' \<Turnstile> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<and> (re(e)))"
            using v'_def by blast
          hence "ts',move ts ts'' v \<Turnstile>\<^bold>\<langle> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<and> (re(e) ) \<^bold>\<rangle>"
            using view.somewhere_leq by meson
          hence "ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> cl(c) \<^bold>\<and> re(e)\<^bold>\<rangle> " 
            using hmlsl.somewhere_and_or_distr  by blast 
          thus False 
          proof
            assume assm':"ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
            have "ts',move ts ts'' v \<Turnstile> \<^bold>\<not> (c \<^bold>= e)" using nequals by blast
            thus False using assm' cr_res.IH e_def move_stab by fastforce
          next
            assume assm':"ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> cl(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
            hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> cl(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
              using e_def nequals by blast
            hence "ts',move ts ts'' v \<Turnstile>\<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> cl(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e)) \<^bold>\<rangle>"
              by blast
            hence pcc:"ts',move ts ts'' v \<Turnstile> pcc e c" by blast
            have "ts',move ts ts'' v \<Turnstile>( \<^bold>\<exists> d. pcc d c) \<^bold>\<rightarrow> \<^bold>\<box>r(c) \<^bold>\<bottom>  "
              using local_LC move_stab by fastforce
            hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<box>r(c) \<^bold>\<bottom>" using pcc by blast
            thus "ts'',move ts ts'' v \<Turnstile> \<^bold>\<bottom>" using e_trans by blast
          qed
        qed
      qed
    qed
  next 
    case (cr_clm ts' ts'')
    have "move ts ts' v = move ts' ts'' (move ts ts' v)"
      using traffic.move_stability_clm cr_clm.hyps traffic.move_trans 
      by auto
    hence move_stab: "move ts ts' v = move ts ts'' v"
      by (metis traffic.abstract.simps cr_clm.hyps traffic.move_trans)
    show ?case 
    proof (rule)
      assume e_def:"(ts'',move ts ts'' v \<Turnstile>  \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)"
      obtain d where d_def: "\<exists>n. (ts' \<^bold>\<midarrow>c(d,n) \<^bold>\<rightarrow> ts'')"
        using cr_clm.hyps by blast
      from this obtain n where n_def:" (ts' \<^bold>\<midarrow>c(d,n) \<^bold>\<rightarrow> ts'')"  by blast
      from e_def have "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using view.somewhere_leq by fastforce
      then obtain v' where v'_def:"(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        by blast
      then have " (ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using n_def backwards_c_res_stab by blast 
      then have "ts', move ts ts'' v \<Turnstile> \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
        using v'_def view.somewhere_leq by meson   
      thus False using cr_clm.IH move_stab e_def nequals by fastforce 
    qed 
  next
    case (wd_res ts' ts'')
    have "move ts ts' v = move ts' ts'' (move ts ts' v)"
      using traffic.move_stability_wdr wd_res.hyps traffic.move_trans 
      by auto
    hence move_stab: "move ts ts' v = move ts ts'' v"
      by (metis traffic.abstract.simps wd_res.hyps traffic.move_trans)
    show ?case
    proof (rule )
      assume e_def: " (ts'',move ts ts'' v \<Turnstile>  \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)"
      obtain d where d_def:"\<exists>n. (ts' \<^bold>\<midarrow>wdr(d,n) \<^bold>\<rightarrow> ts'')" 
        using wd_res.hyps by blast
      from this obtain n where n_def:" (ts' \<^bold>\<midarrow>wdr(d,n) \<^bold>\<rightarrow> ts'')"  by blast
      from e_def have "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using view.somewhere_leq by fastforce
      then obtain v' where v'_def:"(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        by blast
      then have " (ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using n_def backwards_wdr_res_stab by blast 
      then have "  (ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)"
        using v'_def view.somewhere_leq by meson          
      thus False using wd_res.IH move_stab by fastforce
    qed 
  next
    case (wd_clm ts' ts'')
    have "move ts ts' v = move ts' ts'' (move ts ts' v)"
      using traffic.move_stability_wdc wd_clm.hyps traffic.move_trans 
      by auto
    hence move_stab: "move ts ts' v = move ts ts'' v"
      by (metis traffic.abstract.simps wd_clm.hyps traffic.move_trans)
    show ?case
    proof (rule)
      assume e_def: " (ts'',move ts ts'' v \<Turnstile>  \<^bold>\<langle>re(c) \<^bold>\<and> re(e) \<^bold>\<rangle>)"
      obtain d where d_def: " (ts' \<^bold>\<midarrow>wdc(d) \<^bold>\<rightarrow> ts'')"
        using wd_clm.hyps by blast
      from e_def have "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using view.somewhere_leq by fastforce
      then obtain v' where v'_def:"(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        by blast
      then have " (ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using d_def backwards_wdc_res_stab by blast 
      hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" 
        using v'_def view.somewhere_leq by meson
      thus False using wd_clm.IH move_stab by fastforce
    qed 
  qed
qed

text\<open>
While the safety theorem was only proven for a single car, we can
show that the choice of this car is irrelevant. That is, if we have
a safe situation, and switch the perspective to another car,
the resulting situation is also safe.
\<close>
  
lemma safety_switch_invariant:"\<Turnstile>(\<^bold>\<forall>e. safe(e)) \<^bold>\<rightarrow>  \<^bold>@c (\<^bold>\<forall>e. safe(e))"
proof (rule allI|rule impI)+
  fix ts v v' 
  fix e d :: cars
  assume assm: "ts,v \<Turnstile>  \<^bold>\<forall>e. safe(e)" 
    and v'_def:"(v=c>v')" 
    and nequals:"ts,v \<Turnstile> \<^bold>\<not>(d \<^bold>=  e)"
  show "ts,v' \<Turnstile>  \<^bold>\<not> \<^bold>\<langle>re(d) \<^bold>\<and> re(e)\<^bold>\<rangle>"
  proof(rule) 
    assume e_def: "ts,v' \<Turnstile>  \<^bold>\<langle>re(d) \<^bold>\<and> re(e)\<^bold>\<rangle>"
    from e_def obtain v'sub where v'sub_def:
      "(v'sub \<le> v') \<and> (ts,v'sub \<Turnstile> re(d) \<^bold>\<and> re(e))" 
      using view.somewhere_leq by fastforce 
    have "own v' = c" using v'_def view.switch_def by auto
    hence "own v'sub = c" using v'sub_def less_eq_view_ext_def by auto
    obtain vsub where vsub:"(vsub =c> v'sub) \<and> (vsub \<le> v)" 
      using v'_def v'sub_def view.switch_leq by blast
    from v'sub_def and vsub have "ts,vsub \<Turnstile> \<^bold>@c re(d)" 
      by (metis view.switch_unique)
    hence vsub_re_d:"ts,vsub \<Turnstile> re(d)" using at_res_inst by blast
    from v'sub_def and vsub have "ts,vsub \<Turnstile> \<^bold>@c re(e)" 
      by (metis view.switch_unique)
    hence vsub_re_e:"ts,vsub \<Turnstile> re(e)" using at_res_inst by blast
    hence "ts,vsub\<Turnstile>re(d) \<^bold>\<and> re(e)" using vsub_re_e vsub_re_d by blast
    hence "ts,v \<Turnstile>\<^bold>\<langle> re(d) \<^bold>\<and> re(e) \<^bold>\<rangle>" 
      using vsub view.somewhere_leq by fastforce
    then show False using assm nequals by blast
  qed
qed
end
end
