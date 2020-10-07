(*  Title:      regular/Safety_Regular.thy
    Author:     Sven Linker

Distance and Lane change controller for cars with regular sensors.
Flawed safety theorem and proof of flawedness.
Controller definitions that take knowledge of other cars
into account and correct safety theorem.
*)

section\<open>Safety for Cars with Regular Sensors\<close>
text\<open>
This section contains the definition of requirements for
lane change and distance controllers for cars, with the assumption
of regular sensors. Using these definitions, we show that safety
is an invariant along all possible behaviour of cars. 
However, we need to slightly amend our notion of safety, compared
to the safety proof for perfect sensors.
\<close>

theory Safety_Regular
  imports HMLSL_Regular
begin
context hmlsl_regular 
begin
  
interpretation hmlsl : hmlsl "regular :: cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
proof unfold_locales   
  fix e ts c
  show " 0 < regular e ts c" 
    by (metis less_add_same_cancel2 less_trans regular_def
        traffic.psGeZero traffic.sdGeZero) 
qed
notation hmlsl.space ("space")
notation hmlsl.re ("re'(_')")
notation hmlsl.cl("cl'(_')")
notation hmlsl.len ("len")

text\<open>
First we show that the same "safety" theorem as for perfect senors can be 
proven. However, we will subsequently show that this theorem does not
ensure safety from the perspective of each car.

The controller definitions for this "flawed" safety are the same as for perfect sensors.
\<close>
  
abbreviation safe::"cars\<Rightarrow>\<sigma>" 
  where "safe e \<equiv> \<^bold>\<forall> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e) \<^bold>\<rangle>" 
    
abbreviation DC::"\<sigma>"
  where "DC \<equiv> \<^bold>G(\<^bold>\<forall> c d. \<^bold>\<not>(c \<^bold>= d) \<^bold>\<rightarrow> 
                  \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<tau> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle>)"
    
abbreviation pcc::"cars \<Rightarrow> cars \<Rightarrow> \<sigma>" 
  where "pcc c d \<equiv> \<^bold>\<not> (c \<^bold>= d) \<^bold>\<and> \<^bold>\<langle> cl(d) \<^bold>\<and> (re(c) \<^bold>\<or> cl(c))\<^bold>\<rangle>"
    
abbreviation LC::"\<sigma>"
  where "LC \<equiv> \<^bold>G ( \<^bold>\<forall>d.( \<^bold>\<exists> c. pcc c d) \<^bold>\<rightarrow> \<^bold>\<box>r(d) \<^bold>\<bottom>)"
    

text\<open>
The safety proof is exactly the same as for perfect sensors. Note
in particular, that we fix a single car \(e\) for which we show
safety.
\<close>
    
theorem safety_flawed:"\<Turnstile>( \<^bold>\<forall>e. safe e ) \<^bold>\<and> DC \<^bold>\<and> LC \<^bold>\<rightarrow> \<^bold>G (\<^bold>\<forall> e. safe e)"
proof (rule allI|rule impI)+  
  fix ts v ts' 
  fix e c:: cars
  assume assm:"ts,v \<Turnstile> ( \<^bold>\<forall>e. safe e ) \<^bold>\<and> DC \<^bold>\<and> LC"
  assume abs:"(ts \<^bold>\<Rightarrow> ts')"
  assume neg:"ts,v \<Turnstile>\<^bold>\<not>(c \<^bold>= e)"
  from assm have init:"ts,v \<Turnstile> ( \<^bold>\<forall>e. safe e )" by simp
  from assm have DC :"ts,v \<Turnstile> DC" by simp
  from assm have LC: "ts,v \<Turnstile> LC" by simp
  show "ts',move ts ts' v \<Turnstile> \<^bold>\<not> \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" using abs 
  proof (induction)
    case (refl ) 
    have "move ts ts v = v" using move_nothing  by simp
    thus ?case using init move_nothing neg by simp
  next
    case (evolve ts' ts'' )
    have local_DC:
      "ts',move ts ts' v \<Turnstile> \<^bold>\<forall> c d. \<^bold>\<not>(c \<^bold>= d) \<^bold>\<rightarrow> 
                            \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<tau> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle>"
      using evolve.hyps DC by simp
    show ?case 
    proof (rule )
      assume e_def: " (ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)"
      from evolve.IH  and e_def and neg have 
        ts'_safe:"ts',move ts ts' v \<Turnstile> \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
      hence no_coll_after_evol:"ts',move ts ts' v \<Turnstile> \<^bold>\<box>\<^bold>\<tau> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
        using local_DC by blast
      have move_eq:"move ts' ts'' (move ts ts' v) = move ts ts'' v" 
          using "evolve.hyps" abstract.evolve abstract.refl move_trans
        by (meson traffic.abstract.evolve traffic.abstract.refl traffic.move_trans)
      from no_coll_after_evol and evolve.hyps have 
        "ts'',move ts' ts'' (move ts ts' v) \<Turnstile>  \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"  
        by blast
      thus False using e_def using  move_eq by fastforce
    qed
  next
    case (cr_res ts' ts'')
    have local_LC: "ts',move ts ts' v \<Turnstile>( \<^bold>\<forall>d.( \<^bold>\<exists> c. pcc c d) \<^bold>\<rightarrow> \<^bold>\<box>r(d) \<^bold>\<bottom>)  " 
      using LC cr_res.hyps by blast
    have "move ts ts' v = move ts' ts'' (move ts ts' v)" 
      using move_stability_res cr_res.hyps move_trans 
      by auto
    hence move_stab: "move ts ts' v = move ts ts'' v" 
      using cr_res.hyps local.create_reservation_def local.move_def by auto 
    show ?case 
    proof (rule)
      assume e_def:" (ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)"
      obtain d where d_def: "ts' \<^bold>\<midarrow>r(d) \<^bold>\<rightarrow> ts''" using cr_res.hyps by blast
      have "d = e \<or> d \<noteq> e" by simp
      thus False
      proof
        assume eq:"d = e"
        hence e_trans:"ts' \<^bold>\<midarrow>r(e) \<^bold>\<rightarrow> ts''" using d_def by simp
        from e_def have "ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by auto
        hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" 
          using somewhere_leq   
          by meson
        then obtain v' where v'_def:
          "(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" 
          by blast
        with backwards_res_act have "ts',v' \<Turnstile> re(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e))"
          using e_def  backwards_res_stab neg 
          by (metis (no_types, lifting) d_def eq)
        hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts',v' \<Turnstile> re(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e)))"  
          using  v'_def by blast
        hence "ts',move ts ts'' v \<Turnstile>\<^bold>\<langle> re(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e)) \<^bold>\<rangle>"
          using somewhere_leq by meson
        hence "ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> re(c) \<^bold>\<and> cl(e)\<^bold>\<rangle> " 
          using hmlsl.somewhere_and_or_distr by blast 
        thus False 
        proof
          assume assm':"ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
          have "ts',move ts ts' v \<Turnstile> \<^bold>\<not> (c \<^bold>= e)" using neg by blast
          thus False using assm' cr_res.IH e_def move_stab by force
        next
          assume assm':"ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> cl(e)\<^bold>\<rangle>"
          hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> cl(e)\<^bold>\<rangle>" 
            using neg by force
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
            using somewhere_leq   
            by meson
          then obtain v' where v'_def:
            "(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
            by blast
          with backwards_res_stab have overlap: "ts',v' \<Turnstile> re(c) \<^bold>\<and> (re(e))"
            using e_def  backwards_res_stab neg neq2 
            by (metis (no_types, lifting) d_def neq)
          hence unsafe2:"ts',move ts ts'' v \<Turnstile>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" 
            using   somewhere_leq v'_def by blast 
          from cr_res.IH have "ts',move ts ts'' v \<Turnstile> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
            using move_stab by force
          thus False using unsafe2 by best
        next
          assume eq2:"c = d"
          hence e_trans:"ts' \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts''" using d_def by simp
          from e_def have "ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by auto
          hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" 
            using somewhere_leq   
            by meson
          then obtain v' where v'_def:
            "(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
            by blast
          with backwards_res_act have "ts',v' \<Turnstile>   (re(c) \<^bold>\<or> cl(c)) \<^bold>\<and> (re(e) )"
            using e_def  backwards_res_stab neg 
            by (metis (no_types, lifting) d_def eq2)
          hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts',v' \<Turnstile> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<and> (re(e)))"
            using v'_def by blast
          hence "ts',move ts ts'' v \<Turnstile>\<^bold>\<langle> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<and> (re(e) ) \<^bold>\<rangle>"
            using somewhere_leq by meson
          hence "ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> cl(c) \<^bold>\<and> re(e)\<^bold>\<rangle> " 
            using hmlsl.somewhere_and_or_distr  by blast 
          thus False 
          proof
            assume assm':"ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
            have "ts',move ts ts'' v \<Turnstile> \<^bold>\<not> (c \<^bold>= e)" using neg by blast
            thus False using assm' cr_res.IH e_def move_stab by fastforce
          next
            assume assm':"ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> cl(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
            hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> cl(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
              using neg by blast
            hence "ts',move ts ts'' v \<Turnstile>\<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> cl(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e))\<^bold>\<rangle>"
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
      using move_stability_clm cr_clm.hyps move_trans 
      by auto
    hence move_stab: "move ts ts' v = move ts ts'' v"
      by (metis abstract.simps cr_clm.hyps move_trans)
    show ?case 
    proof (rule)
      assume e_def: "(ts'',move ts ts'' v \<Turnstile>  \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)"
      obtain d where d_def: "\<exists>n. (ts' \<^bold>\<midarrow>c(d,n) \<^bold>\<rightarrow> ts'')" using cr_clm.hyps by blast
      then obtain n where n_def:" (ts' \<^bold>\<midarrow>c(d,n) \<^bold>\<rightarrow> ts'')"  by blast
      from e_def have "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using somewhere_leq by fastforce
      then obtain v' where v'_def:
        "(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        by blast
      then have " (ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using n_def backwards_c_res_stab by blast 
      hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<langle>re(c) \<^bold>\<and>re(e) \<^bold>\<rangle>"
        using e_def v'_def somewhere_leq by meson
      thus False using cr_clm.IH move_stab by fastforce
    qed 
  next
    case (wd_res ts' ts'')
    have "move ts ts' v = move ts' ts'' (move ts ts' v)"
      using move_stability_wdr wd_res.hyps move_trans 
      by auto
    hence move_stab: "move ts ts' v = move ts ts'' v"
      by (metis abstract.simps wd_res.hyps move_trans)
    show ?case
    proof (rule)
      assume e_def:" (ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)"
      obtain d and n where n_def:" (ts' \<^bold>\<midarrow>wdr(d,n) \<^bold>\<rightarrow> ts'')"  
        using wd_res.hyps by auto
      from e_def have "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using somewhere_leq by fastforce
      then obtain v' where v'_def:
        "(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        by blast
      then have " (ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using n_def backwards_wdr_res_stab by blast 
      hence "ts',move ts ts'' v \<Turnstile>\<^bold>\<langle>re(c) \<^bold>\<and>re(e)\<^bold>\<rangle>" using
          v'_def somewhere_leq by meson
      thus False using wd_res.IH move_stab by fastforce
    qed 
  next
    case (wd_clm ts' ts'')
    have "move ts ts' v = move ts' ts'' (move ts ts' v)"
      using move_stability_wdc wd_clm.hyps move_trans 
      by auto
    hence move_stab: "move ts ts' v = move ts ts'' v"
      by (metis abstract.simps wd_clm.hyps move_trans)
    show ?case
    proof (rule)
      assume e_def: " (ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)"
      obtain d where d_def: " (ts' \<^bold>\<midarrow>wdc(d) \<^bold>\<rightarrow> ts'')" using wd_clm.hyps by blast
      from e_def have "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using somewhere_leq by fastforce
      then obtain v' where v'_def:
        "(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        by blast
      from this have " (ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using d_def backwards_wdc_res_stab by blast 
      hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" using  v'_def somewhere_leq by meson
      thus False using wd_clm.IH move_stab by fastforce
    qed 
  qed
qed

text\<open>
As stated above, the flawed safety theorem does not ensure safety for 
the perspective of each car.
In particular, we can construct a traffic snapshot and a view, such that
it satisfies our safety predicate for each car, but if we switch the
perspective of the view to another car, the situation is unsafe. A
visualisation of this situation can be found in the publication
of this work at iFM 2017 \cite{Linker2017}.
\<close>

lemma safety_not_invariant_switch:
  "\<exists>ts v. (ts,v \<Turnstile> \<^bold>\<forall>e. safe(e) \<^bold>\<and> ( \<^bold>\<exists> c. \<^bold>@c  \<^bold>\<not>( \<^bold>\<forall>e. safe(e))))"
proof -
  obtain d c ::cars where assumption:"d \<noteq>c" 
    using cars.at_least_two_cars_exists by best  
  obtain pos' where  pos'_def:"\<forall>(c::cars). (pos' c) = (5::real)" by best
  obtain po where pos_def:"po = (pos'(c:=0))(d:=2)" by best
  obtain re where res_def:"\<forall>(c::cars). re c = Abs_nat_int{0}" by best  
  obtain cl where clm_def:"\<forall>(c::cars). cl c= \<emptyset>" by best
  obtain dy where dyn_def:"\<forall>c::cars. \<forall>x::real . (dy c) x  = (0::real)"  by force
  obtain sd where sd_def:"\<forall>(c::cars). sd c = (2::real)" by best
  obtain ps where ps_def:"\<forall>(c::cars). ps c = (1::real)" by best
  obtain ts_rep where ts_rep_def:"ts_rep= (po, re, cl, dy, ps, sd)"  by best
      
  have disj:"\<forall>c .((re c) \<sqinter> (cl c) = \<emptyset>)" by (simp add: clm_def nat_int.inter_empty1)
  have re_geq_one:"\<forall>c. |re c| \<ge> 1" 
    by (simp add: Abs_nat_int_inverse nat_int.card'_def res_def)
  have re_leq_two:"\<forall>c. |re c| \<le> 2" 
    using nat_int.card'.rep_eq res_def nat_int.rep_single by auto
  have cl_leq_one:"\<forall>c. |cl c| \<le> 1" 
    using nat_int.card_empty_zero clm_def by (simp )
  have add_leq_two:"\<forall>c . |re c| + |cl c| \<le> 2"  
    using nat_int.card_empty_zero clm_def re_leq_two by (simp )
  have  clNextRe : 
    "\<forall>c. ((cl c) \<noteq> \<emptyset> \<longrightarrow> (\<exists> n. Rep_nat_int (re c) \<union> Rep_nat_int (cl c) = {n, n+1}))"
    by (simp add: clm_def)
  from dyn_def have dyn_geq_zero:"\<forall>c. \<forall>x. (dy c x) \<ge> 0" by auto
  from ps_def have ps_ge_zero :"\<forall>c. ps c> 0" by auto
  from sd_def have sd_ge_zero: "\<forall>c. sd c > 0" by auto
  have ts_in_type: " ts_rep \<in> 
  {ts :: (cars\<Rightarrow>real)*(cars\<Rightarrow>lanes)*(cars\<Rightarrow>lanes)*(cars\<Rightarrow>real\<Rightarrow>real)*(cars\<Rightarrow>real)*(cars\<Rightarrow>real).
    (\<forall>c. ((fst (snd ts))) c \<sqinter> ((fst (snd (snd ts)))) c = \<emptyset> )  \<and>
    (\<forall>c. |(fst (snd ts)) c| \<ge> 1) \<and>
    (\<forall>c. |(fst (snd ts)) c| \<le> 2) \<and>
    (\<forall>c. |(fst (snd (snd ts)) c)| \<le> 1) \<and>
    (\<forall>c. |(fst (snd ts)) c| + |(fst (snd (snd ts))) c| \<le> 2) \<and>
    (\<forall>c. (fst(snd(snd (ts)))) c \<noteq> \<emptyset> \<longrightarrow> 
      (\<exists> n. Rep_nat_int ((fst (snd ts)) c) \<union> Rep_nat_int ((fst (snd (snd ts))) c) 
        = {n, n+1})) \<and>
    (\<forall>c . fst (snd (snd (snd (snd (ts))))) c > 0) \<and>
    (\<forall>c.  snd (snd (snd (snd (snd (ts))))) c > 0)
 } " 
    using pos_def res_def clm_def disj re_geq_one re_leq_two cl_leq_one add_leq_two
      ps_ge_zero sd_ge_zero ts_rep_def 
    by auto
  obtain v where v_def:
    "v=\<lparr>ext = Abs_real_int (0,3), lan = Abs_nat_int{0}, own = d\<rparr>"
    by best
  obtain ts where ts_def:"ts=Abs_traffic ts_rep" 
    by blast      
  have size:"\<forall>c. physical_size ts c = 1" using ps_def physical_size_def ts_rep_def
      ts_in_type ts_def ps_ge_zero using Abs_traffic_inverse 
    by auto
      
  have safe:" ts,v \<Turnstile> \<^bold>\<forall>e. safe(e) " 
  proof
    have other_len_zero:"\<forall>e. e \<noteq>c \<and> e \<noteq>d \<longrightarrow> \<parallel> len v ts e\<parallel> = 0" 
    proof (rule allI|rule impI)+
      fix e
      assume e_def:" e \<noteq>c \<and> e \<noteq>d"
      have position:"pos ts e = 5" using e_def ts_def ts_rep_def ts_in_type ts_def
          Abs_traffic_inverse pos_def fun_upd_apply pos'_def traffic.pos_def
        by auto
      have "regular (own v) ts e = 1"
        using e_def v_def sensors_def ps_def ts_def size regular_def by auto
      then have space:"space ts v e = Abs_real_int (5,6)"
        using e_def pos_def position hmlsl.space_def  by auto
      have "left (space ts v e) > right (ext v)"
        using space v_def Abs_real_int_inverse by auto
      thus "\<parallel> len v ts e\<parallel> = 0"
        using hmlsl.len_def real_int.length_def Abs_real_int_inverse by auto
    qed
    have no_cars:"\<forall>e. e \<noteq>c \<and> e \<noteq>d \<longrightarrow> (ts,v \<Turnstile> \<^bold>\<not> \<^bold>\<langle> re(e) \<^bold>\<or> cl(e) \<^bold>\<rangle>)"
    proof (rule allI|rule impI|rule notI)+
      fix e
      assume neq:"e \<noteq>c \<and> e \<noteq>d"
      assume contra:"ts,v \<Turnstile> \<^bold>\<langle> re(e) \<^bold>\<or> cl(e) \<^bold>\<rangle>" 
      from other_len_zero have len_e:"\<parallel>len v ts e\<parallel> = 0" using neq by auto
      from contra obtain v' where v'_def:"v' \<le> v \<and> (ts,v' \<Turnstile>re(e) \<^bold>\<or> cl(e))"
        using somewhere_leq by force
      from v'_def and len_e have len_v':"\<parallel>len v' ts e\<parallel> = 0"
        using hmlsl.len_empty_subview  by blast
      from v'_def have "ts,v' \<Turnstile>re(e) \<^bold>\<or> cl(e)" by blast
      thus False using len_v' by auto
    qed
      
    have sensors_c:"regular (own v) ts c = 1"
      using v_def regular_def ps_def ts_def size assumption by auto
    have space_c:"space ts v c = Abs_real_int (0,1)"
      using pos_def ts_def ts_rep_def ts_in_type Abs_traffic_inverse
        fun_upd_apply sensors_c  assumption hmlsl.space_def traffic.pos_def
      by auto
    have lc:"left (space ts v c) = 0" using space_c Abs_real_int_inverse by auto
    have rv:"right (ext v) = 3" using v_def Abs_real_int_inverse by auto
    have lv:"left (ext v) = 0" using v_def Abs_real_int_inverse by auto
    have rc:"right (space ts v c) = 1" using space_c Abs_real_int_inverse by auto
    have len_c:"len v ts c = Abs_real_int(0,1)"
      using space_c v_def hmlsl.len_def lc lv rv rc by auto
    have sensors_d:"regular (own v) ts d = 3" 
      using v_def regular_def braking_distance_def ts_def size sd_def
        Abs_traffic_inverse ts_in_type ts_rep_def
      by auto
    have space_d:"space ts v d = Abs_real_int(2,5)"
      using pos_def ts_def ts_rep_def ts_in_type Abs_traffic_inverse
        fun_upd_apply sensors_d assumption hmlsl.space_def traffic.pos_def
      by auto
    have ld:"left (space ts v d) = 2" using space_d Abs_real_int_inverse by auto
    have rd: "right (space ts v d) = 5" using space_d Abs_real_int_inverse by auto
    have len_d :"len v ts d = Abs_real_int(2,3)"
      using space_d v_def hmlsl.len_def ld rd lv rv by auto
    have no_overlap_c_d:"ts,v \<Turnstile>\<^bold>\<not> \<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle>" 
    proof (rule notI)
      assume contra:"ts,v \<Turnstile>  \<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle>" 
      obtain v' where v'_def:"(v' \<le> v) \<and> (ts,v' \<Turnstile>re(c) \<^bold>\<and> re(d))"
        using somewhere_leq contra by force
      hence len_eq:"len v' ts c = len v' ts d" by simp
      from v'_def have v'_c:"\<parallel>len v' ts c\<parallel> > 0" 
                   and  v'_d:"\<parallel>len v' ts d\<parallel> > 0" by simp+
      from v'_c have v'_rel_c:
        "left (space ts v' c) < right (ext v') \<and> right (space ts v' c) > left (ext v')" 
        using hmlsl.len_non_empty_inside by blast
      from v'_d have v'_rel_d:
        "left (space ts v' d) < right (ext v') \<and> right (space ts v' d) > left (ext v')" 
        using hmlsl.len_non_empty_inside by blast
      have less_len:"len v' ts c \<le> len v ts c"
        using hmlsl.view_leq_len_leq v'_c v'_def less_eq_view_ext_def by blast
      have sp_eq_c:"space ts v' c = space ts v c"
        using v'_def less_eq_view_ext_def regular_def hmlsl.space_def by auto
      have sp_eq_d:"space ts v' d = space ts v d"
        using v'_def less_eq_view_ext_def regular_def hmlsl.space_def by auto
          
      have "right (ext v') > 0 \<and> right (ext v') > 2"
        using ld lc v'_rel_c v'_rel_d sp_eq_c sp_eq_d by auto
      hence r_v':"right (ext v') > 2" by blast
      have "left (ext v') < 1 \<and> left (ext v') < 5"
        using rd rc v'_rel_c v'_rel_d sp_eq_c sp_eq_d by auto
      hence l_v':"left (ext v') < 1" by blast
      have "len v' ts c \<noteq> ext v'  "
      proof
        assume "len v' ts c = ext v'"
        hence eq:"right (len v' ts c) = right (ext v')" by simp
        from less_len have "right (len v' ts c) \<le> right (len v ts c)"
          by (simp add: less_eq_real_int_def)
        with len_c have "right (len v' ts c) \<le> 1 "
          using Abs_real_int_inverse by auto
        thus False using r_v' eq by linarith
      qed
      thus False using v'_def by blast
    qed
    fix x
    show "ts,v \<Turnstile> safe(x)" 
    proof (rule allI|rule impI)+
      fix y
      assume x_neg_y: "ts,v \<Turnstile>  \<^bold>\<not>(y \<^bold>= x)"
      show "ts,v \<Turnstile>\<^bold>\<not>\<^bold>\<langle>re(y) \<^bold>\<and> re(x)\<^bold>\<rangle>"
      proof (cases "y \<noteq>c \<and> y \<noteq>d")
        assume "y \<noteq> c \<and> y \<noteq> d"
        hence "(ts,v \<Turnstile> \<^bold>\<not> \<^bold>\<langle> re(y) \<^bold>\<or> cl(y) \<^bold>\<rangle>)" using no_cars by blast
        hence "ts,v \<Turnstile> \<^bold>\<not> \<^bold>\<langle> re(y) \<^bold>\<rangle>" by blast
        then show ?thesis by blast
      next
        assume "\<not>(y \<noteq>c \<and> y \<noteq>d)"
        hence "y = c \<or> y = d" by blast
        thus ?thesis
        proof
          assume y_eq_c:"y=c"
          thus ?thesis
          proof (cases "x=d")
            assume "x=d"
            then show "ts,v \<Turnstile>\<^bold>\<not> \<^bold>\<langle>re(y) \<^bold>\<and> re(x)\<^bold>\<rangle>"
              using no_overlap_c_d y_eq_c by blast
          next
            assume x:"x \<noteq>d"
            have x2:"x \<noteq>c" using y_eq_c x_neg_y by blast
            hence "(ts,v \<Turnstile> \<^bold>\<not> \<^bold>\<langle> re(x) \<^bold>\<or> cl(x) \<^bold>\<rangle>)" using no_cars x by blast
            hence "ts,v \<Turnstile> \<^bold>\<not> \<^bold>\<langle> re(x) \<^bold>\<rangle>" by blast
            thus ?thesis by blast
          qed
        next
          assume y_eq_c:"y=d"
          thus ?thesis
          proof (cases "x=c")
            assume "x=c"
            thus "ts,v \<Turnstile>\<^bold>\<not> \<^bold>\<langle>re(y) \<^bold>\<and> re(x)\<^bold>\<rangle>" using no_overlap_c_d y_eq_c by blast
          next
            assume x:"x \<noteq>c"
            have x2:"x \<noteq>d" using y_eq_c x_neg_y by blast
            hence "(ts,v \<Turnstile> \<^bold>\<not> \<^bold>\<langle> re(x) \<^bold>\<or> cl(x) \<^bold>\<rangle>)" using no_cars x by blast
            hence "ts,v \<Turnstile> \<^bold>\<not> \<^bold>\<langle> re(x) \<^bold>\<rangle>" by blast
            thus ?thesis  by blast
          qed
        qed
      qed
    qed
  qed
    
  have unsafe:"ts,v \<Turnstile> (\<^bold>\<exists> c. (\<^bold>@c  \<^bold>\<not>( \<^bold>\<forall>e. safe(e))))"
  proof -
    have "ts,v \<Turnstile> (\<^bold>@c  \<^bold>\<not>( \<^bold>\<forall>e. safe(e)))"
    proof (rule allI|rule impI|rule notI)+
      fix vc
      assume sw:"( v=c>vc)"
      have spatial_vc:"ext v = ext vc \<and> lan v = lan vc"
        using switch_def sw by blast
      assume safe: "ts,vc\<Turnstile> ( \<^bold>\<forall>e. safe(e))"
      obtain vc' where vc'_def:
        "vc'=\<lparr>ext = Abs_real_int (2,3), lan = Abs_nat_int {0}, own = c\<rparr>"
        by best
      have own_eq:"own vc' = own vc" using sw switch_def vc'_def by auto
      have ext_vc:"ext vc = Abs_real_int (0,3)" using spatial_vc v_def by force
      have right_ok:"right (ext vc) \<ge> right (ext vc')"
        using vc'_def ext_vc Abs_real_int_inverse by auto
      have left_ok:"left (ext vc') \<ge> left (ext vc)"
        using vc'_def ext_vc Abs_real_int_inverse by auto
      hence ext_leq: "ext vc' \<le> ext vc"
        using right_ok left_ok less_eq_real_int_def by auto
      have "lan vc = Abs_nat_int{0}" using v_def switch_def sw by force
      hence lan_leq:"lan vc' \<sqsubseteq> lan vc" using  vc'_def  order_refl by force
      have leqvc:"vc' \<le> vc"
        using ext_leq lan_leq own_eq less_eq_view_ext_def by force         
      have sensors_c:"regular (own vc') ts c = 3"
        using vc'_def regular_def ps_def traffic.braking_distance_def 
          ts_def sd_def size assumption Abs_traffic_inverse ts_in_type  ts_rep_def
        by auto
      have space_c:"space ts vc' c = Abs_real_int (0,3)"
        using pos_def ts_def ts_rep_def ts_in_type Abs_traffic_inverse
          fun_upd_apply sensors_c  assumption hmlsl.space_def traffic.pos_def
        by auto
      have lc:"left (space ts vc' c) = 0" using space_c Abs_real_int_inverse by auto
      have rv:"right (ext vc') = 3" using vc'_def Abs_real_int_inverse by auto
      have lv:"left (ext vc') = 2" using vc'_def Abs_real_int_inverse by auto
      have rc:"right (space ts vc' c) = 3" using space_c Abs_real_int_inverse by auto
      have len_c:"len vc' ts c = Abs_real_int(2,3)"
        using space_c v_def hmlsl.len_def lc lv rv rc by auto
      have res_c: "restrict vc' (res ts) c = Abs_nat_int {0}"
        using ts_def ts_rep_def ts_in_type Abs_traffic_inverse res_def traffic.res_def
          inf_idem restrict_def vc'_def
        by force          
      have sensors_d:"regular (own vc') ts d = 1"
        using vc'_def regular_def ts_def size sd_def Abs_traffic_inverse ts_in_type
          ts_rep_def assumption
        by auto
      have space_d:"space ts vc' d = Abs_real_int(2,3)"
        using pos_def ts_def ts_rep_def ts_in_type Abs_traffic_inverse
          fun_upd_apply sensors_d assumption hmlsl.space_def traffic.pos_def
        by auto
      have ld:"left (space ts vc' d) = 2" using space_d Abs_real_int_inverse by auto
      have rd: "right (space ts vc' d) = 3" using space_d Abs_real_int_inverse by auto
      have len_d :"len vc' ts d = Abs_real_int(2,3)"
        using space_d v_def hmlsl.len_def ld rd lv rv
        by auto
      have  res_d:"restrict vc' (res ts) d = Abs_nat_int {0}" 
        using ts_def ts_rep_def ts_in_type Abs_traffic_inverse res_def traffic.res_def
          inf_idem restrict_def vc'_def by force          
      have "ts,vc' \<Turnstile> re(c) \<^bold>\<and> re(d)" using 
          len_d len_c vc'_def ts_def ts_rep_def ts_in_type Abs_traffic_inverse
          res_c res_d nat_int.card'_def
          Abs_real_int_inverse real_int.length_def traffic.res_def
          nat_int.singleton2 Abs_nat_int_inverse
        by auto
      with leqvc have "ts,vc \<Turnstile> \<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle>" using somewhere_leq by blast
      with assumption have "ts,vc \<Turnstile> \<^bold>\<not> (c \<^bold>= d) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(d) \<^bold>\<rangle>" by blast
      with safe show False by blast
    qed
    thus ?thesis by blast
  qed
  from safe and unsafe have "ts,v  \<Turnstile> \<^bold>\<forall>e. safe(e) \<^bold>\<and>  (\<^bold>\<exists> c. (\<^bold>@c  \<^bold>\<not>( \<^bold>\<forall>e. safe(e))))"
    by blast
  thus ?thesis by blast
qed

text\<open>
Now we show how to amend the controller specifications to gain safety as an invariant
even with regular sensors.

The distance controller can be strengthened, by requiring that we switch
to the perspective of one of the cars involved first, before checking
for the collision. Since all variables are universally quantified, 
this ensures that no collision exists for the perspective of any car.
\<close>
abbreviation DC'::"\<sigma>"
  where "DC' \<equiv> \<^bold>G ( \<^bold>\<forall> c d. \<^bold>\<not>(c \<^bold>= d) \<^bold>\<rightarrow> 
                  (\<^bold>@d \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<tau> \<^bold>@d \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle>)"
    
text\<open>
The amendment to the lane change controller is slightly different. Instead
of checking the potential collision only from the perspective of the
car \(d\) trying to change lanes, we require that also no other car may
perceive a potential collision. Note that the restriction to \(d\)'s
behaviour can only be enforced within \(d\), if the information from
the other car is somehow passed to \(d\). Hence, we require the 
cars to communicate in some way. However, we do not need to specifiy,
\emph{how} this communication is implemented. 
\<close>
abbreviation LC'::"\<sigma>"
  where "LC' \<equiv> \<^bold>G ( \<^bold>\<forall>d. (\<^bold>\<exists> c.  (\<^bold>@c (pcc c d)) \<^bold>\<or> (\<^bold>@d (pcc c d))) \<^bold>\<rightarrow> \<^bold>\<box>r(d) \<^bold>\<bottom> ) "
    

text\<open>
With these new controllers, we can prove a stronger theorem than before. Instead
of proving safety from the perspective of a single car as previously, we now
only consider a traffic situation to be safe, if it satisfies the safety
predicate from the perspective of \emph{all} cars. Note that this immediately
implies the safety invariance theorem proven for perfect sensors. 
\<close>
theorem safety:"\<Turnstile> (\<^bold>\<forall>e. \<^bold>@e ( safe e ) ) \<^bold>\<and> DC' \<^bold>\<and> LC' \<^bold>\<rightarrow>  \<^bold>G(\<^bold>\<forall> e.  \<^bold>@ e (safe e))"
proof (rule allI; rule allI;rule impI; rule allI; rule impI; rule allI)
  fix ts v ts' e
  assume assm:"ts,v \<Turnstile> ( \<^bold>\<forall>e. \<^bold>@e (safe e) ) \<^bold>\<and> DC' \<^bold>\<and> LC'"
  assume abs:"(ts \<^bold>\<Rightarrow> ts')"
  from assm have init:"ts,v \<Turnstile> ( \<^bold>\<forall>e. \<^bold>@e (safe e) )" by simp
  from assm have DC :"ts,v \<Turnstile> DC'" by simp
  from assm have LC: "ts,v \<Turnstile> LC'" by simp
  show "ts',move ts ts' v \<Turnstile> ( \<^bold>@e (safe e))" using abs
  proof (induction)
    case (refl ) 
    have "move ts ts v = v" using move_nothing by blast
    thus ?case using    move_nothing init  by simp  
  next
    case (evolve ts' ts'' )
    have local_DC:
      "ts',move ts ts' v \<Turnstile> \<^bold>\<forall> c d. \<^bold>\<not>(c \<^bold>= d) \<^bold>\<rightarrow>
                             (\<^bold>@d \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle> ) \<^bold>\<rightarrow> ( \<^bold>\<box>\<^bold>\<tau> \<^bold>@d \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle>)"
      using evolve.hyps DC by simp
    show ?case 
    proof (rule ccontr)
      assume "\<not> (ts'',move ts ts'' v \<Turnstile> ( \<^bold>@e (safe e)))"
      then have  e_def:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<not>(\<^bold>@e (safe e))" by best
      hence "ts'',move ts ts'' v \<Turnstile> \<^bold>@e (\<^bold>\<not> safe e)"
        using switch_always_exists switch_unique by fastforce
      then obtain ve where ve_def:
        "((move ts ts'' v) =e> ve) \<and> (ts'',ve \<Turnstile> \<^bold>\<not> safe e)" 
        using switch_always_exists by fastforce
      hence unsafe:"ts'',ve \<Turnstile> \<^bold>\<exists> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
      then obtain c where c_def:"ts'',ve \<Turnstile>  \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
      from evolve.IH  and c_def have 
        ts'_safe:"ts',move ts ts' v \<Turnstile> \<^bold>@e (\<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)"
        by blast
      hence not_eq:"ts',move ts ts' v \<Turnstile>\<^bold>@e (\<^bold>\<not>(c \<^bold>= e))" 
        and safe':"ts',move ts ts' v \<Turnstile> \<^bold>@e ( \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)" 
        using hmlsl.at_conj_distr by simp+
      from not_eq have not_eq_v:"ts',move ts ts' v \<Turnstile>\<^bold>\<not>(c \<^bold>=e)"
        using hmlsl.at_eq switch_always_exists by auto   
      have 
        "ts',move ts ts' v \<Turnstile>  \<^bold>\<not>(c \<^bold>= e) \<^bold>\<rightarrow>
                                 (\<^bold>@e \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle> ) \<^bold>\<rightarrow> (\<^bold>\<box>\<^bold>\<tau> \<^bold>@e \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)" 
        using local_DC by simp
      hence dc:"ts',move ts ts' v \<Turnstile> (\<^bold>@e \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle> ) \<^bold>\<rightarrow>
                                      (\<^bold>\<box>\<^bold>\<tau> \<^bold>@e \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)"
        using not_eq_v
        by simp
      hence no_coll_after_evol:"ts',move ts ts' v \<Turnstile> ( \<^bold>\<box>\<^bold>\<tau> \<^bold>@e \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>)"
        using safe' 
        by simp
      hence 1:"ts'',move ts' ts'' (move ts ts' v) \<Turnstile> \<^bold>@e \<^bold>\<not> \<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
        using evolve.hyps by simp
      have move_eq:"move ts' ts'' (move ts ts' v) = move ts ts'' v"
        using "evolve.hyps" abstract.evolve abstract.refl move_trans
        by blast
      from 1 have "ts'', move ts ts'' v \<Turnstile> \<^bold>@e \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
        using move_eq by fastforce
      hence "ts'',ve \<Turnstile>  \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" using ve_def by blast
      thus False using c_def by blast
    qed
  next
    case (cr_clm ts' ts'')
    have "move ts ts' v = move ts' ts'' (move ts ts' v)"
      using move_stability_clm cr_clm.hyps move_trans 
      by auto
    hence move_stab: "move ts ts' v = move ts ts'' v"
      by (metis abstract.simps cr_clm.hyps move_trans)
    show ?case 
    proof (rule ccontr)
      assume "\<not> (ts'',move ts ts'' v \<Turnstile> ( \<^bold>@e (safe e)))"
      then have  e_def:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<not>(\<^bold>@e (safe e))" by best
      hence "ts'',move ts ts'' v \<Turnstile> \<^bold>@e (\<^bold>\<not> safe e)"
        using switch_always_exists switch_unique 
        by fastforce  
      then obtain ve where ve_def:
        "((move ts ts'' v) =e> ve) \<and> (ts'',ve \<Turnstile> \<^bold>\<not> safe e)" 
        using switch_always_exists by fastforce
      hence unsafe:"ts'',ve \<Turnstile> \<^bold>\<exists> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
      then obtain c where c_def:"ts'',ve \<Turnstile>  \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
        by blast
      hence c_neq_e:"ts'',ve \<Turnstile>\<^bold>\<not> (c \<^bold>= e)" by blast
      obtain d n where d_def: " (ts' \<^bold>\<midarrow>c(d,n) \<^bold>\<rightarrow> ts'')" using cr_clm.hyps by blast
      from c_def have "\<exists>v'. (v' \<le> ve) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using somewhere_leq by fastforce
      then obtain v' where v'_def:"(v' \<le> ve) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        by blast
      then have " (ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using d_def backwards_c_res_stab by blast 
      hence "ts',ve \<Turnstile> \<^bold>\<not> safe (e)"
        using c_neq_e c_def v'_def somewhere_leq by meson
      thus False using cr_clm.IH move_stab ve_def by fastforce                                     
    qed
  next
    case (wd_res ts' ts'')
    have "move ts ts' v = move ts' ts'' (move ts ts' v)"
      using move_stability_wdr wd_res.hyps move_trans 
      by auto
    hence move_stab: "move ts ts' v = move ts ts'' v"
      by (metis abstract.simps wd_res.hyps move_trans)
    show ?case 
    proof (rule ccontr)
      assume "\<not> (ts'',move ts ts'' v \<Turnstile> ( \<^bold>@e (safe e)))"
      then have  e_def:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<not>(\<^bold>@e (safe e))" by best
      hence "ts'',move ts ts'' v \<Turnstile> \<^bold>@e (\<^bold>\<not> safe e)"
        using switch_always_exists switch_unique  by (fastforce) 
      then obtain ve where ve_def:
        "((move ts ts'' v) =e> ve) \<and> (ts'',ve \<Turnstile> \<^bold>\<not> safe e)" 
        using switch_always_exists by fastforce
      hence unsafe:"ts'',ve \<Turnstile> \<^bold>\<exists> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
      then obtain c where c_def:"ts'',ve \<Turnstile>  \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
      hence c_neq_e:"ts'',ve \<Turnstile>\<^bold>\<not> (c \<^bold>= e)" by blast
      obtain d n  where n_def:
        "(ts' \<^bold>\<midarrow>wdr(d,n) \<^bold>\<rightarrow> ts'')" using wd_res.hyps  by blast
      from c_def have "\<exists>v'. (v' \<le> ve) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using somewhere_leq by fastforce
      then obtain v' where v'_def:"(v' \<le> ve) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        by blast
      then have " (ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using n_def backwards_wdr_res_stab by blast 
      hence "ts',ve \<Turnstile> \<^bold>\<not> safe (e)" 
        using c_neq_e c_def v'_def somewhere_leq by meson
      thus False using wd_res.IH move_stab ve_def by fastforce                                     
    qed
  next
    case (wd_clm ts' ts'')
    have "move ts ts' v = move ts' ts'' (move ts ts' v)"
      using move_stability_wdc wd_clm.hyps move_trans 
      by auto
    hence move_stab: "move ts ts' v = move ts ts'' v"
      by (metis abstract.simps wd_clm.hyps move_trans)
    show ?case 
    proof (rule ccontr)
      assume "\<not> (ts'',move ts ts'' v \<Turnstile> ( \<^bold>@e (safe e)))"
      then have  e_def:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<not>(\<^bold>@e (safe e))" by best
      then obtain ve where ve_def:
        "((move ts ts'' v) =e> ve) \<and> (ts'',ve \<Turnstile> \<^bold>\<not> safe e)" 
        using switch_always_exists by fastforce
      hence unsafe:"ts'',ve \<Turnstile> \<^bold>\<exists> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
      then obtain c where c_def:"ts'',ve \<Turnstile>  \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
      hence c_neq_e:"ts'',ve \<Turnstile>\<^bold>\<not> (c \<^bold>= e)" by blast
      obtain d where d_def: "(ts' \<^bold>\<midarrow>wdc(d) \<^bold>\<rightarrow> ts'')" using wd_clm.hyps by blast
      from c_def have "\<exists>v'. (v' \<le> ve) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using somewhere_leq by fastforce
      then obtain v' where v'_def:
        "(v' \<le> ve) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" by blast
      then have " (ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
        using d_def backwards_wdc_res_stab by blast 
      hence "ts',ve \<Turnstile> \<^bold>\<not> safe (e)"
        using c_neq_e c_def v'_def somewhere_leq by meson
      thus False using wd_clm.IH move_stab ve_def by fastforce                                     
    qed
  next
    case (cr_res ts' ts'')
    have local_LC: 
      "ts',move ts ts' v \<Turnstile> \<^bold>\<forall>d.( \<^bold>\<exists> c. (\<^bold>@c (pcc c d)) \<^bold>\<or> (\<^bold>@d (pcc c d))) \<^bold>\<rightarrow> \<^bold>\<box>r(d) \<^bold>\<bottom>" 
      using LC cr_res.hyps(1)   by blast
    have "move ts ts' v = move ts' ts'' (move ts ts' v)"
      using move_stability_res cr_res.hyps move_trans 
      by auto
    hence move_stab: "move ts ts' v = move ts ts'' v"
      by (metis abstract.simps cr_res.hyps move_trans)
    show ?case 
    proof (rule ccontr)
      obtain d where d_def: "(ts' \<^bold>\<midarrow>r(d) \<^bold>\<rightarrow> ts'')"
        using cr_res.hyps by blast
      assume "\<not> (ts'',move ts ts'' v \<Turnstile> ( \<^bold>@e (safe e)))"
      then have  e_def:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<not>(\<^bold>@e (safe e))" by best
      hence "ts'',move ts ts'' v \<Turnstile> \<^bold>@e (\<^bold>\<not> safe e)"
        using switch_always_exists switch_unique by fast
      then obtain ve where ve_def:
        "((move ts ts'' v) =e> ve) \<and> (ts'',ve \<Turnstile> \<^bold>\<not> safe e)" 
        using switch_always_exists by fastforce
      hence unsafe:"ts'',ve \<Turnstile> \<^bold>\<exists> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
      then obtain c where c_def:"ts'',ve \<Turnstile>  \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
      hence c_neq_e:"ts'',ve \<Turnstile>\<^bold>\<not>(c \<^bold>= e)" by blast
      show False
      proof (cases "d=e")
        case True
        hence e_trans:"ts' \<^bold>\<midarrow>r(e) \<^bold>\<rightarrow> ts''" using d_def by simp
        from c_def have "ts'',ve \<Turnstile> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by auto
        hence "\<exists>v'. (v' \<le> ve) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
          using somewhere_leq   
          by meson
        then obtain v' where v'_def:
          "(v' \<le> ve) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" by blast
        with backwards_res_act have "ts',v' \<Turnstile>   re(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e))"
          using c_def  backwards_res_stab c_neq_e 
          by (metis (no_types, lifting) d_def True)
        hence "\<exists>v'. (v' \<le> ve) \<and> (ts',v' \<Turnstile> re(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e)))"  
          using  v'_def by blast
        hence "ts',ve \<Turnstile>\<^bold>\<langle> re(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e)) \<^bold>\<rangle>"
          using somewhere_leq by meson
        hence "ts',ve \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> re(c) \<^bold>\<and> cl(e)\<^bold>\<rangle> " 
          using hmlsl.somewhere_and_or_distr by metis  
        then show False 
        proof
          assume assm':"ts',ve \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
          have "ts',move ts ts' v \<Turnstile> \<^bold>\<not> (c \<^bold>= e)" using c_def by blast
          thus False using assm' cr_res.IH c_def move_stab ve_def by force
        next
          assume assm':"ts',ve \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> cl(e)\<^bold>\<rangle>"
          hence "ts',ve \<Turnstile> \<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> cl(e)\<^bold>\<rangle>" using c_def by force
          hence "ts',ve \<Turnstile> pcc c e" by blast
          hence "ts',move ts ts' v \<Turnstile> \<^bold>@e (pcc c e)"
            using ve_def move_stab switch_unique by fastforce
          hence pcc:"ts',move ts ts' v \<Turnstile> (\<^bold>@c (pcc c e)) \<^bold>\<or> (\<^bold>@e (pcc c e))"
            by blast
          have 
            "ts',move ts ts' v \<Turnstile>(\<^bold>\<exists> c.(\<^bold>@c (pcc c e)) \<^bold>\<or> (\<^bold>@e (pcc c e))) \<^bold>\<rightarrow> \<^bold>\<box>r(e) \<^bold>\<bottom>" 
            using local_LC e_def by blast
          thus "ts'',move ts ts'' v \<Turnstile> \<^bold>\<bottom>" using e_trans pcc by blast
        qed
      next
        case False
        then have neq:"d \<noteq>e" .
        show False 
        proof (cases "c=d")
          case False
          from c_def have "ts'',ve \<Turnstile> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by auto
          hence "\<exists>v'. (v' \<le> ve) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
            using somewhere_leq   
            by meson
          then obtain v' where v'_def:
            "(v' \<le> ve) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" by blast
          with backwards_res_stab have overlap: "ts',v' \<Turnstile> re(c) \<^bold>\<and> (re(e))"
            using c_def  backwards_res_stab c_neq_e False
            by (metis (no_types, lifting) d_def neq)
          hence unsafe2:"ts',ve \<Turnstile>\<^bold>\<not> safe(e)" 
            using  c_neq_e somewhere_leq v'_def by blast
          from cr_res.IH have "ts',move ts ts'' v \<Turnstile> \<^bold>@e (safe(e))"
            using move_stab by force
          thus False using unsafe2 ve_def by best
        next
          case True            
          hence e_trans:"ts' \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts''" using d_def by simp
          from c_def have "ts'',ve \<Turnstile> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by auto
          hence "\<exists>v'. (v' \<le> ve) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
            using somewhere_leq   
            by meson
          then obtain v' where v'_def:
            "(v' \<le> ve) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" by blast
          with backwards_res_act have "ts',v' \<Turnstile>   (re(c) \<^bold>\<or> cl(c)) \<^bold>\<and> (re(e) )"
            using c_def  backwards_res_stab c_neq_e 
            by (metis (no_types, lifting) d_def True)
          hence "\<exists>v'. (v' \<le> ve) \<and> (ts',v' \<Turnstile> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<and> (re(e)))"
            using v'_def by blast
          hence "ts',ve \<Turnstile>\<^bold>\<langle> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<and> (re(e) ) \<^bold>\<rangle>"
            using somewhere_leq move_stab 
            by meson
          hence "ts',ve \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> cl(c) \<^bold>\<and> re(e)\<^bold>\<rangle> " 
            using hmlsl.somewhere_and_or_distr  by blast 
          thus False 
          proof 
            assume assm':"ts',ve \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
            have "ts',ve \<Turnstile> \<^bold>\<not> (c \<^bold>= e)" using c_def by blast
            thus False using assm' cr_res.IH c_def move_stab ve_def by fastforce
          next
            assume assm':"ts',ve \<Turnstile>  \<^bold>\<langle> cl(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
            hence "ts',ve \<Turnstile> \<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> cl(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" using c_def by blast
            hence "ts',ve \<Turnstile>\<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> cl(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e)) \<^bold>\<rangle>" by blast
            hence "ts',ve \<Turnstile> pcc e c" by blast
            hence "ts',move ts ts' v \<Turnstile> \<^bold>@e (pcc e c)"
              using ve_def move_stab  switch_unique by fastforce
            hence pcc:"ts', move ts ts' v \<Turnstile> (\<^bold>@e (pcc e c)) \<^bold>\<or> (\<^bold>@c (pcc e c))"
              by blast
            have 
              "ts',move ts ts' v \<Turnstile>(\<^bold>\<exists> d.(\<^bold>@d (pcc d c)) \<^bold>\<or> (\<^bold>@c (pcc d c))) \<^bold>\<rightarrow> \<^bold>\<box>r(c) \<^bold>\<bottom>" 
              using local_LC move_stab c_def e_def by blast
            hence "ts',move ts ts' v \<Turnstile> \<^bold>\<box>r(c) \<^bold>\<bottom>" using pcc by blast
            thus "ts'',move ts ts'' v \<Turnstile> \<^bold>\<bottom>" using e_trans by blast
          qed
        qed
      qed
    qed
  qed
qed
end
end
