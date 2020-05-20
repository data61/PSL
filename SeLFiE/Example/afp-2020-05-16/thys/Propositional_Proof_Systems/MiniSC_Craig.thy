subsubsection\<open>Craig Interpolation\<close>
theory MiniSC_Craig
imports MiniSC Formulas
begin

abbreviation atoms_mset where "atoms_mset \<Theta> \<equiv> \<Union>F \<in> set_mset \<Theta>. atoms F"
  
(* which version of craig interpolation we show doesn't matter: *)
lemma interpolation_equal_styles: "
(\<forall>\<Gamma> \<Delta> \<Gamma>' \<Delta>'. \<Gamma> + \<Gamma>' \<Rightarrow> \<Delta> + \<Delta>' \<longrightarrow> (\<exists>F :: 'a formula. \<Gamma> \<Rightarrow> F,\<Delta> \<and> F,\<Gamma>' \<Rightarrow> \<Delta>' \<and> atoms F \<subseteq> atoms_mset (\<Gamma> + \<Delta>) \<and> atoms F \<subseteq> atoms_mset (\<Gamma>' + \<Delta>')))
  \<longleftrightarrow>
(\<forall>\<Gamma> \<Delta>. \<Gamma> \<Rightarrow> \<Delta> \<longrightarrow> (\<exists>F :: 'a formula. \<Gamma> \<Rightarrow> {#F#} \<and> {#F#} \<Rightarrow> \<Delta> \<and> atoms F \<subseteq> atoms_mset \<Gamma> \<and> atoms F \<subseteq> atoms_mset \<Delta>))"
proof(intro iffI allI impI, goal_cases)
  case (1 \<Gamma> \<Delta>)
  hence "\<Gamma> + {#} \<Rightarrow> {#} + \<Delta> \<longrightarrow> (\<exists>F. \<Gamma> \<Rightarrow> F, {#} \<and> F, {#} \<Rightarrow> \<Delta> \<and> atoms F \<subseteq> atoms_mset (\<Gamma> + {#}) \<and> atoms F \<subseteq> atoms_mset ({#} + \<Delta>))"  by presburger
  with 1 show ?case by auto
next
  case (2 \<Gamma> \<Delta> \<Gamma>' \<Delta>')
  from 2(2) have "\<Gamma> \<Rightarrow> \<Delta> + image_mset Not \<Gamma>' + \<Delta>'" by(induction \<Gamma>' arbitrary: \<Gamma>; simp add: SCp.NotR)
  hence "\<Gamma> + image_mset Not \<Delta> \<Rightarrow> image_mset Not \<Gamma>' + \<Delta>'" by(induction \<Delta> arbitrary: \<Delta>'; simp add: SCp.NotL) (metis SCp.NotL union_mset_add_mset_right)
  from 2(1)[THEN spec, THEN spec, THEN mp, OF this]
  have "\<exists>F. \<Gamma> + image_mset \<^bold>\<not> \<Delta> \<Rightarrow> {#F#} \<and> {#F#} \<Rightarrow> image_mset \<^bold>\<not> \<Gamma>' + \<Delta>' \<and> atoms F \<subseteq> atoms_mset (\<Gamma> + image_mset \<^bold>\<not> \<Delta>) \<and> atoms F \<subseteq> atoms_mset (image_mset \<^bold>\<not> \<Gamma>' + \<Delta>')" .
  then obtain F where n: "\<Gamma> + image_mset \<^bold>\<not> \<Delta> \<Rightarrow> {#F#}" and p: "{#F#} \<Rightarrow> image_mset \<^bold>\<not> \<Gamma>' + \<Delta>'" and at: "atoms F \<subseteq> atoms_mset (\<Gamma> + \<Delta>)" "atoms F \<subseteq> atoms_mset (\<Gamma>' + \<Delta>')" by auto
  from n have n: "\<Gamma> \<Rightarrow> F, \<Delta>" by(induction \<Delta> arbitrary: \<Gamma>; simp add: NotL_inv inR1)
  from p have p: "F,\<Gamma>' \<Rightarrow> \<Delta>'" by(induction \<Gamma>' arbitrary: \<Delta>'; simp add: NotR_inv inL1)
  show ?case using p at n by blast
qed
    

text\<open>The original version of the interpolation theorem is due to Craig~\cite{craig1957linear}.
Our proof partly follows the approach of Troelstra and Schwichtenberg~\cite{troelstra2000basic} but,
especially with the mini formulas, adds its own spin.\<close>

theorem SC_Craig_interpolation:
  assumes "\<Gamma> + \<Gamma>' \<Rightarrow> \<Delta> + \<Delta>'"
  obtains F where 
    "\<Gamma> \<Rightarrow> F,\<Delta>"
    "F,\<Gamma>' \<Rightarrow> \<Delta>'"
    "atoms F \<subseteq> atoms_mset (\<Gamma> + \<Delta>)"
    "atoms F \<subseteq> atoms_mset (\<Gamma>' + \<Delta>')"
proof -
  have split_seq: "(\<exists>H'. H = f F J,H') \<or> (\<exists>I'. I = f F J,I')" if "f F J, G = H + I" for f F G H I J
  proof -
    from that have "f F J \<in># H + I" by(metis (mono_tags) add_ac(2) union_single_eq_member)
    thus ?thesis by (meson multi_member_split union_iff)
  qed
  have mini: "\<exists> F. \<Gamma> \<Rightarrow> F, \<Delta> \<and> F, \<Gamma>' \<Rightarrow> \<Delta>' \<and> 
    atoms F \<subseteq> atoms_mset (\<Gamma> + \<Delta>) \<and> atoms F \<subseteq> atoms_mset (\<Gamma>' + \<Delta>') \<and> is_mini_formula F"
    if "\<Gamma> + \<Gamma>' \<Rightarrow> \<Delta> + \<Delta>'" "is_mini_mset (\<Gamma>+\<Gamma>'+\<Delta>+\<Delta>')" for \<Gamma> \<Gamma>' \<Delta> \<Delta>'
  using that proof(induction "\<Gamma> + \<Gamma>'" "\<Delta> + \<Delta>'" arbitrary: \<Gamma> \<Gamma>' \<Delta> \<Delta>' rule: SCp.induct)
    case BotL thus ?case proof(cases; intro exI)
      assume "\<bottom> \<in># \<Gamma>" with BotL 
      show "\<Gamma> \<Rightarrow> \<bottom>, \<Delta> \<and> \<bottom>, \<Gamma>' \<Rightarrow> \<Delta>' \<and> atoms \<bottom> \<subseteq> atoms_mset (\<Gamma> + \<Delta>) \<and> atoms \<bottom> \<subseteq> atoms_mset (\<Gamma>' + \<Delta>') \<and> is_mini_formula \<bottom>" 
        by(simp add: SCp.BotL)
    next
      assume "\<not>(\<bottom> \<in># \<Gamma>)" with BotL 
      show "\<Gamma> \<Rightarrow> \<top>, \<Delta> \<and> \<top>, \<Gamma>' \<Rightarrow> \<Delta>' \<and> atoms \<top> \<subseteq> atoms_mset (\<Gamma> + \<Delta>) \<and> atoms \<top> \<subseteq> atoms_mset (\<Gamma>' + \<Delta>') \<and> is_mini_formula \<top>"
        by(auto simp add: Top_def SCp.ImpR SCp.ImpL SCp.BotL intro!: SCp.intros(3-))
    qed
  next
    case (Ax k)
    let ?ss = "\<lambda>F. (\<Gamma> \<Rightarrow> F, \<Delta> \<and> F, \<Gamma>' \<Rightarrow> \<Delta>' \<and> is_mini_formula F)" (* troelstra calls it a split sequent. *)
    have ff: "?ss \<bottom>" if "Atom k \<in># \<Gamma>" "Atom k \<in># \<Delta>" (* troelstra uses \<top> in this case. That can't be right. (p. 117, case Ax, right bottom split) *)
      using SCp.BotL SCp.Ax[of k] that by auto
    have fs: "?ss (Atom k)" if "Atom k \<in># \<Gamma>" "Atom k \<in># \<Delta>'"
      using that by(auto intro!: SCp.Ax[where k=k])
    have sf: "?ss ((Atom k) \<^bold>\<rightarrow> \<bottom>)" if "Atom k \<in># \<Gamma>'" "Atom k \<in># \<Delta>"
      using that by(auto intro!: SCp.ImpR SCp.ImpL intro: SCp.Ax[where k=k] SCp.BotL)
    have ss: "?ss \<top>" if "Atom k \<in># \<Gamma>'" "Atom k \<in># \<Delta>'"
      unfolding Top_def using that SCp.ImpR SCp.Ax BotL_canonical by fastforce
    have in_sumE: "\<lbrakk>A \<in># (F + G); A \<in># F \<Longrightarrow> P; A \<in># G \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" for A F G P by fastforce
    have trust_firstE: "P F \<Longrightarrow> Q F \<Longrightarrow> \<exists>F. P F \<and> Q F" for P Q F by blast
    from Ax show ?case by(elim in_sumE) (frule (1) ff fs sf ss; elim conjE trust_firstE; force)+
  next
    case (ImpR F G \<Delta>'')
    note split_seq[of Imp, OF ImpR(3)]
    thus ?case proof(elim disjE exE)
      fix H' assume \<Delta>: "\<Delta> = F \<^bold>\<rightarrow> G, H'"
      have "F, \<Gamma> + \<Gamma>' = (F, \<Gamma>) + \<Gamma>'" "G, \<Delta>'' = (G, \<Delta> - {#F \<^bold>\<rightarrow> G#}) + \<Delta>'" "is_mini_mset ((F, \<Gamma>) + \<Gamma>' + (G, \<Delta> - {#F \<^bold>\<rightarrow> G#}) + \<Delta>')"
        using that ImpR(3-) by (simp_all add: union_assoc \<Delta>)
      from  ImpR(2)[OF this] obtain Fa where Fam:
        "F, \<Gamma> \<Rightarrow> Fa, G, H'" "Fa, \<Gamma>' \<Rightarrow> \<Delta>'" "is_mini_formula Fa"
        "atoms Fa \<subseteq> atoms_mset ((F, \<Gamma>) + (G, H'))" "atoms Fa \<subseteq> atoms_mset (\<Gamma>' + \<Delta>')" unfolding \<Delta> by auto
      thus ?thesis unfolding \<Delta> proof(intro exI[where x=Fa] conjI \<open>is_mini_formula Fa\<close>)
        show "\<Gamma> \<Rightarrow> Fa, F \<^bold>\<rightarrow> G, H'" using Fam by(intro SCp.ImpR[THEN inR1]; fast)
        show "Fa, \<Gamma>' \<Rightarrow> \<Delta>'" using Fam by blast
        show "atoms Fa \<subseteq> atoms_mset (\<Gamma> + (F \<^bold>\<rightarrow> G, H'))" "atoms Fa \<subseteq> atoms_mset (\<Gamma>' + \<Delta>')" using Fam by auto
      qed
    next
      fix I' assume \<Delta>': "\<Delta>' = F \<^bold>\<rightarrow> G, I'"
      have "F, \<Gamma> + \<Gamma>' = \<Gamma> + (F,\<Gamma>')" "G, \<Delta>'' = \<Delta> + (G, I')" "is_mini_mset (\<Gamma> + (F, \<Gamma>') + \<Delta> + (G, I'))"
        using ImpR(3-) by (simp_all add: add.left_commute \<Delta>')
      from ImpR(2)[OF this] obtain Fa m where Fam:
        "\<Gamma> \<Rightarrow> Fa, \<Delta>" "Fa, F, \<Gamma>' \<Rightarrow> G, I'" "is_mini_formula Fa"
        "atoms Fa \<subseteq> atoms_mset (\<Gamma> + \<Delta>)" "atoms Fa \<subseteq> atoms_mset ((F, \<Gamma>') + (G, I'))" unfolding \<Delta>' by auto
      show ?thesis unfolding \<Delta>' proof(intro exI[where x=Fa] conjI \<open>is_mini_formula Fa\<close>)
         show "\<Gamma> \<Rightarrow> Fa, \<Delta>" using Fam by fast
         show "Fa, \<Gamma>' \<Rightarrow> F \<^bold>\<rightarrow> G, I'" using Fam by (simp add: SCp.ImpR inL1)
         show "atoms Fa \<subseteq> atoms_mset (\<Gamma> + \<Delta>)" "atoms Fa \<subseteq> atoms_mset (\<Gamma>' + (F \<^bold>\<rightarrow> G, I'))" using Fam by auto
      qed
    qed
  next
    case (ImpL \<Gamma>'' F G)
    note split_seq[of Imp, OF ImpL(5)]
    thus ?case proof(elim disjE exE)
      fix H' assume \<Gamma>: "\<Gamma> = F \<^bold>\<rightarrow> G, H'"
      from \<Gamma> have *: "\<Gamma>'' = \<Gamma>' + H'" "F, \<Delta> + \<Delta>' = \<Delta>' + (F,\<Delta>)"
        using ImpL(5-) by (simp_all add: union_assoc \<Gamma>)
      hence  "is_mini_mset (\<Gamma>' + H' + \<Delta>' + (F, \<Delta>))" using ImpL(6) by(auto simp add: \<Gamma>)
      from ImpL(2)[OF * this] obtain Fa where IH1: "\<Gamma>' \<Rightarrow> Fa, \<Delta>'" "Fa, H' \<Rightarrow> F, \<Delta>" 
        "atoms Fa \<subseteq> atoms_mset (H' + (F,\<Delta>))" "atoms Fa \<subseteq> atoms_mset (\<Gamma>' + \<Delta>')" "is_mini_formula Fa"  by blast
      from \<Gamma> have *: "G, \<Gamma>'' = (G, H') + \<Gamma>'" "\<Delta> + \<Delta>' = \<Delta> + \<Delta>'"
        using ImpL(5-) by (simp_all add: union_assoc)
      hence "is_mini_mset ((G, H') + \<Gamma>' + \<Delta> + \<Delta>')" using ImpL(6) by(simp add: \<Gamma>)
      from ImpL(4)[OF * this] obtain Ga where IH2: "G, H' \<Rightarrow> Ga, \<Delta>" "Ga, \<Gamma>' \<Rightarrow> \<Delta>'" 
        "atoms Ga \<subseteq> atoms_mset ((G, H') + \<Delta>)" "atoms Ga \<subseteq> atoms_mset (\<Gamma>' + \<Delta>')" "is_mini_formula Ga" by blast
      text\<open>A big part of the difficulty of this proof is finding a way to instantiate the IHs.
        Interestingly, this is not the only way that works. 
        Originally, we used @{term "\<Gamma>'' = H' + \<Gamma>'"} and @{term "F, \<Delta> + \<Delta>' = (F,\<Delta>) + \<Delta>'"}
        to instantiate the IH (which is in some sense more natural, less use of commutativity).
        This gave us a @{term Fa} that verifies @{term "H' \<Rightarrow> Fa, F, \<Delta>"} and @{term "Fa, \<Gamma>' \<Rightarrow> \<Delta>'"}
         and resulted in the interpolant @{term "to_mini_formula (Fa \<^bold>\<or> Ga)"}.\<close>
      let ?w = "Fa \<^bold>\<rightarrow> Ga"
      show ?thesis proof(intro exI[where x="?w"] conjI)  
        from IH1(1) IH2(2) show "?w, \<Gamma>' \<Rightarrow> \<Delta>'"
          by (simp add: SCp.ImpL)
        from IH1(2) IH2(1) show "\<Gamma> \<Rightarrow> ?w, \<Delta>" unfolding \<Gamma>
          by(intro SCp.ImpL inR1[OF SCp.ImpR] SCp.ImpR) (simp_all add: weakenR weakenL)
        show "atoms ?w \<subseteq> atoms_mset (\<Gamma> + \<Delta>)" "atoms ?w \<subseteq> atoms_mset (\<Gamma>' + \<Delta>')"
          using IH1(3-) IH2(3-) unfolding \<Gamma> by auto
        show "is_mini_formula ?w" using \<open>is_mini_formula Fa\<close> \<open>is_mini_formula Ga\<close> by simp
      qed
    next
      fix I' assume \<Gamma>': "\<Gamma>' = F \<^bold>\<rightarrow> G, I'" note ImpL(5)[unfolded \<Gamma>']
      from \<Gamma>' have *: "\<Gamma>'' = \<Gamma> + I'" "F, \<Delta> + \<Delta>' = \<Delta> + (F,\<Delta>')"
        using ImpL(5-) by(simp_all add: union_assoc add_ac(2,3))
      hence "is_mini_mset (\<Gamma> + I' + \<Delta> + (F, \<Delta>'))" using ImpL(6) by(auto simp add: \<Gamma>')
      from ImpL(2)[OF * this] obtain Fa
        where IH1: "\<Gamma> \<Rightarrow> Fa, \<Delta>" "Fa, I' \<Rightarrow> F, \<Delta>'" "is_mini_formula Fa"
        "atoms Fa \<subseteq> atoms_mset (I' + (F,\<Delta>'))" "atoms Fa \<subseteq> atoms_mset (\<Gamma> + \<Delta>)" by blast
      from \<Gamma>' have *: "G, \<Gamma>'' = \<Gamma> + (G, I')" "\<Delta> + \<Delta>' = \<Delta> + \<Delta>'"
        using ImpL(5) by (simp_all add: add_ac \<open>\<Gamma>'' = \<Gamma> + I'\<close>)
      have "is_mini_mset (\<Gamma> + (G, I') + \<Delta> + \<Delta>')"  using ImpL(6) by(auto simp add: \<Gamma>')
      from ImpL(4)[OF * this] obtain Ga l
        where IH2: "\<Gamma> \<Rightarrow> Ga, \<Delta>" "Ga, G, I' \<Rightarrow> \<Delta>'" "is_mini_formula Ga"
        "atoms Ga \<subseteq> atoms_mset ((G, I') + \<Delta>')" "atoms Ga \<subseteq> atoms_mset (\<Gamma> + \<Delta>)" by blast
      text\<open>Same thing as in the other case, just with 
        @{term "G, \<Gamma>'' = (G, I') + \<Gamma>"}, @{term "\<Delta> + \<Delta>' = \<Delta>' + \<Delta>"},
        @{term "\<Gamma>'' = I' + \<Gamma>"}, and @{term "F, \<Delta> + \<Delta>' = (F,\<Delta>') + \<Delta>"}
       resulting in @{term "to_mini_formula (\<^bold>\<not>(Fa \<^bold>\<or> Ga))"}\<close>
      let ?w = "(Ga \<^bold>\<rightarrow> (Fa \<^bold>\<rightarrow> \<bottom>)) \<^bold>\<rightarrow> \<bottom>"
      have "?w = to_mini_formula (Ga \<^bold>\<and> Fa)" by (simp add: IH1(3) IH2(3) mini_to_mini)
      show ?thesis proof(intro exI[of _ ?w] conjI)
        from IH1(1) IH2(1) show "\<Gamma> \<Rightarrow> ?w, \<Delta>"
          by(intro SCp.ImpR SCp.ImpL) (simp_all add: inR1 weakenR BotL_canonical)
        from IH1(2) IH2(2) show "?w, \<Gamma>' \<Rightarrow> \<Delta>'" unfolding \<Gamma>'
          by(blast intro!: SCp.ImpL SCp.ImpR dest: weakenL weakenR)+
        show "atoms ?w \<subseteq> atoms_mset (\<Gamma> + \<Delta>)"
             "atoms ?w \<subseteq> atoms_mset (\<Gamma>' + \<Delta>')" using IH1(3-) IH2(3-) unfolding \<Gamma>' by auto
        show "is_mini_formula ?w" using \<open>is_mini_formula Fa\<close> \<open>is_mini_formula Ga\<close> by simp
      qed
    qed
  next
    text\<open>The rest is just those cases that can't happen because of the mini formula property.\<close>
  qed (metis add.commute is_mini_formula.simps union_iff union_single_eq_member)+
  define tms :: "'a formula multiset \<Rightarrow> 'a formula multiset"
    where "tms = image_mset to_mini_formula"
  have [simp]: "tms (A + B) = tms A + tms B" "tms {#F#} = {#to_mini_formula F#}" for A B F unfolding tms_def by simp_all
  have [simp]: "atoms_mset (tms \<Gamma>) = atoms_mset \<Gamma>" for \<Gamma> unfolding tms_def using mini_formula_atoms by fastforce
  have imm: "is_mini_mset (tms \<Gamma> + tms \<Gamma>' + tms \<Delta> + tms \<Delta>')" unfolding tms_def by auto
  from assms have "tms \<Gamma> + tms \<Gamma>' \<Rightarrow> tms \<Delta> + tms \<Delta>'" unfolding tms_def using SC_full_to_mini by force
  from mini[OF this imm] obtain F where hp(*habemus papam*):
    "tms \<Gamma> \<Rightarrow> F, tms \<Delta>" "F, tms \<Gamma>' \<Rightarrow> tms \<Delta>'"
    and su: "atoms F \<subseteq> atoms_mset (tms \<Gamma> + tms \<Delta>)" "atoms F \<subseteq> atoms_mset (tms \<Gamma>' + tms \<Delta>')"
    and mf: "is_mini_formula F" by blast
  from hp mf have "tms \<Gamma> \<Rightarrow> tms (F, \<Delta>)" "tms (F, \<Gamma>') \<Rightarrow> tms \<Delta>'" using mini_to_mini[where 'a='a] unfolding tms_def by simp_all
  hence "\<Gamma> \<Rightarrow> F, \<Delta>" "F, \<Gamma>' \<Rightarrow> \<Delta>'" using SC_mini_to_full unfolding tms_def by blast+
  with su show ?thesis using \<open>\<And>\<Gamma>. atoms_mset (tms \<Gamma>) = atoms_mset \<Gamma>\<close> image_mset_union that by auto
qed
(*
  Gallier:
   - wouldn't hold without bottom. Try interpolating A \<rightarrow> A and B \<rightarrow> B 
   - is an application of cut elimination? oh well, if you'd have a cut rule in the \<Rightarrow> predicate,
      you'd be in trouble, ok.
*)

text\<open>Note that there is an extension to Craig interpolation:
One can show that atoms that only appear positively/negatively in the original formulas will only appear
positively/negatively in the interpolant. \<close>

abbreviation "patoms_mset S \<equiv> \<Union>F\<in>set_mset S. fst (pn_atoms F)"
abbreviation "natoms_mset S \<equiv> \<Union>F\<in>set_mset S. snd (pn_atoms F)"

theorem SC_Craig_interpolation_pn:
  assumes "\<Gamma> + \<Gamma>' \<Rightarrow> \<Delta> + \<Delta>'"
  obtains F where 
    "\<Gamma> \<Rightarrow> F,\<Delta>"
    "F,\<Gamma>' \<Rightarrow> \<Delta>'"
    "fst (pn_atoms F) \<subseteq> (patoms_mset \<Gamma> \<union> natoms_mset \<Delta>) \<inter> (natoms_mset \<Gamma>' \<union> patoms_mset \<Delta>')"
    "snd (pn_atoms F) \<subseteq> (natoms_mset \<Gamma> \<union> patoms_mset \<Delta>) \<inter> (patoms_mset \<Gamma>' \<union> natoms_mset \<Delta>')"
proof -
  have split_seq: "(\<exists>H'. H = f F J,H') \<or> (\<exists>I'. I = f F J,I')" if "f F J, G = H + I" for f F G H I J
  proof -
    from that have "f F J \<in># H + I" by(metis (mono_tags) add_ac(2) union_single_eq_member)
    thus ?thesis by (meson multi_member_split union_iff)
  qed
  have mini: "\<exists> F :: 'a formula. \<Gamma> \<Rightarrow> F, \<Delta> \<and> F, \<Gamma>' \<Rightarrow> \<Delta>' \<and> 
    fst (pn_atoms F) \<subseteq> (patoms_mset \<Gamma> \<union> natoms_mset \<Delta>) \<inter> (natoms_mset \<Gamma>' \<union> patoms_mset \<Delta>') \<and> 
    snd (pn_atoms F) \<subseteq> (natoms_mset \<Gamma> \<union> patoms_mset \<Delta>) \<inter> (patoms_mset \<Gamma>' \<union> natoms_mset \<Delta>') \<and> is_mini_formula F"
    if "\<Gamma> + \<Gamma>' \<Rightarrow> \<Delta> + \<Delta>'" "is_mini_mset (\<Gamma>+\<Gamma>'+\<Delta>+\<Delta>')" for \<Gamma> \<Gamma>' \<Delta> \<Delta>'
  using that proof(induction "\<Gamma> + \<Gamma>'" "\<Delta> + \<Delta>'" arbitrary: \<Gamma> \<Gamma>' \<Delta> \<Delta>' rule: SCp.induct)
    case BotL 
    let ?om = "\<lambda>F. fst (pn_atoms F) \<subseteq> (patoms_mset \<Gamma> \<union> natoms_mset \<Delta>) \<inter> (natoms_mset \<Gamma>' \<union> patoms_mset \<Delta>') \<and>
        snd (pn_atoms F) \<subseteq> (natoms_mset \<Gamma> \<union> patoms_mset \<Delta>) \<inter> (patoms_mset \<Gamma>' \<union> natoms_mset \<Delta>') \<and> is_mini_formula (F :: 'a formula)"
    show ?case proof(cases; intro exI)
      assume "\<bottom> \<in># \<Gamma>" with BotL 
      show "\<Gamma> \<Rightarrow> \<bottom>, \<Delta> \<and> \<bottom>, \<Gamma>' \<Rightarrow> \<Delta>' \<and> ?om \<bottom>" by(simp add: SCp.BotL)
    next
      assume "\<not>(\<bottom> \<in># \<Gamma>)" with BotL 
      show "\<Gamma> \<Rightarrow> \<top>, \<Delta> \<and> \<top>, \<Gamma>' \<Rightarrow> \<Delta>' \<and> ?om \<top>" 
        by(auto simp add: Top_def SCp.ImpR SCp.ImpL SCp.BotL prod_unions_def intro!: SCp.intros(3-))
    qed
  next
    case (Ax k)
    let ?ss = "\<lambda>F. (\<Gamma> \<Rightarrow> F, \<Delta> \<and> F, \<Gamma>' \<Rightarrow> \<Delta>' \<and> fst (pn_atoms F) \<subseteq> (patoms_mset \<Gamma> \<union> natoms_mset \<Delta>) \<inter> (natoms_mset \<Gamma>' \<union> patoms_mset \<Delta>') \<and>
        snd (pn_atoms F) \<subseteq> (natoms_mset \<Gamma> \<union> patoms_mset \<Delta>) \<inter> (patoms_mset \<Gamma>' \<union> natoms_mset \<Delta>') \<and> is_mini_formula F)" (* troelstra calls it a split sequent. *)
    have ff: "?ss \<bottom>" if "Atom k \<in># \<Gamma>" "Atom k \<in># \<Delta>"
      using SCp.BotL SCp.Ax[of k] that by auto
    have fs: "?ss (Atom k)" if "Atom k \<in># \<Gamma>" "Atom k \<in># \<Delta>'"
      using that by(force intro!: SCp.Ax[where k=k])
    have sf: "?ss ((Atom k) \<^bold>\<rightarrow> \<bottom>)" if "Atom k \<in># \<Gamma>'" "Atom k \<in># \<Delta>"
      using that by(auto intro!: SCp.ImpR SCp.ImpL intro: SCp.Ax[where k=k] SCp.BotL exI[where x="Atom k"] simp add: prod_unions_def; force)
    have ss: "?ss \<top>" if "Atom k \<in># \<Gamma>'" "Atom k \<in># \<Delta>'"
      unfolding Top_def using that SCp.ImpR by (auto simp add: prod_unions_def SCp.Ax)
    have in_sumE: "\<lbrakk>A \<in># (F + G); A \<in># F \<Longrightarrow> P; A \<in># G \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" for A F G P by fastforce
    have trust_firstE: "P F \<Longrightarrow> Q F \<Longrightarrow> \<exists>F. P F \<and> Q F" for P Q F by blast
    from Ax show ?case by(elim in_sumE) (frule (1) ff fs sf ss; elim conjE trust_firstE; force)+
  next
  next
    case (ImpR F G \<Delta>'')
    note split_seq[of Imp, OF ImpR(3)]
    thus ?case proof(elim disjE exE)
      fix H' assume \<Delta>: "\<Delta> = F \<^bold>\<rightarrow> G, H'"
      have "F, \<Gamma> + \<Gamma>' = (F, \<Gamma>) + \<Gamma>'" "G, \<Delta>'' = (G, \<Delta> - {#F \<^bold>\<rightarrow> G#}) + \<Delta>'" "is_mini_mset ((F, \<Gamma>) + \<Gamma>' + (G, \<Delta> - {#F \<^bold>\<rightarrow> G#}) + \<Delta>')"
        using that ImpR(3-) by (simp_all add: union_assoc \<Delta>)
      from  ImpR(2)[OF this] obtain Fa where Fam:
        "F, \<Gamma> \<Rightarrow> Fa, G, H'" "Fa, \<Gamma>' \<Rightarrow> \<Delta>'" "is_mini_formula Fa"
        "fst (pn_atoms Fa) \<subseteq> (patoms_mset (F, \<Gamma>) \<union> natoms_mset (G, H')) \<inter> (natoms_mset \<Gamma>' \<union> patoms_mset \<Delta>')"
        "snd (pn_atoms Fa) \<subseteq> (natoms_mset (F, \<Gamma>) \<union> patoms_mset (G, H')) \<inter> (patoms_mset \<Gamma>' \<union> natoms_mset \<Delta>')" unfolding \<Delta> by auto
      thus ?thesis unfolding \<Delta> proof(intro exI[where x=Fa] conjI \<open>is_mini_formula Fa\<close>)
        show "\<Gamma> \<Rightarrow> Fa, F \<^bold>\<rightarrow> G, H'" using Fam by(intro SCp.ImpR[THEN inR1]; fast)
        show "Fa, \<Gamma>' \<Rightarrow> \<Delta>'" using Fam by blast
        show "fst (pn_atoms Fa) \<subseteq> (patoms_mset \<Gamma> \<union> natoms_mset (F \<^bold>\<rightarrow> G, H')) \<inter> (natoms_mset \<Gamma>' \<union> patoms_mset \<Delta>')" 
             "snd (pn_atoms Fa) \<subseteq> (natoms_mset \<Gamma> \<union> patoms_mset (F \<^bold>\<rightarrow> G, H')) \<inter> (patoms_mset \<Gamma>' \<union> natoms_mset \<Delta>')" 
          using Fam(4-) by (auto simp: prod_unions_def split: prod.splits)
      qed
    next
      fix I' assume \<Delta>': "\<Delta>' = F \<^bold>\<rightarrow> G, I'"
      have "F, \<Gamma> + \<Gamma>' = \<Gamma> + (F,\<Gamma>')" "G, \<Delta>'' = \<Delta> + (G, I')" "is_mini_mset (\<Gamma> + (F, \<Gamma>') + \<Delta> + (G, I'))"
        using ImpR(3-) by (simp_all add: add.left_commute \<Delta>')
      from ImpR(2)[OF this] obtain Fa m where Fam:
        "\<Gamma> \<Rightarrow> Fa, \<Delta>" "Fa, F, \<Gamma>' \<Rightarrow> G, I'" "is_mini_formula Fa"
        "fst (pn_atoms Fa) \<subseteq> (patoms_mset \<Gamma> \<union> natoms_mset \<Delta>) \<inter> (natoms_mset (F, \<Gamma>') \<union> patoms_mset (G, I'))"
        "snd (pn_atoms Fa) \<subseteq> (natoms_mset \<Gamma> \<union> patoms_mset \<Delta>) \<inter> (patoms_mset (F, \<Gamma>') \<union> natoms_mset (G, I'))" unfolding \<Delta>' by auto
      show ?thesis unfolding \<Delta>' proof(intro exI[where x=Fa] conjI \<open>is_mini_formula Fa\<close>)
         show "\<Gamma> \<Rightarrow> Fa, \<Delta>" using Fam by fast
         show "Fa, \<Gamma>' \<Rightarrow> F \<^bold>\<rightarrow> G, I'" using Fam by (simp add: SCp.ImpR inL1)
         show "fst (pn_atoms Fa) \<subseteq> (patoms_mset \<Gamma> \<union> natoms_mset \<Delta>) \<inter> (natoms_mset \<Gamma>' \<union> patoms_mset (F \<^bold>\<rightarrow> G, I'))"
              "snd (pn_atoms Fa) \<subseteq> (natoms_mset \<Gamma> \<union> patoms_mset \<Delta>) \<inter> (patoms_mset \<Gamma>' \<union> natoms_mset (F \<^bold>\<rightarrow> G, I'))" 
              using Fam by (auto simp: prod_unions_def split: prod.splits)
      qed
    qed
  next
  next
    case (ImpL \<Gamma>'' F G)
    note split_seq[of Imp, OF ImpL(5)]
    thus ?case proof(elim disjE exE)
      fix H' assume \<Gamma>: "\<Gamma> = F \<^bold>\<rightarrow> G, H'"
      from \<Gamma> have *: "\<Gamma>'' = \<Gamma>' + H'" "F, \<Delta> + \<Delta>' = \<Delta>' + (F,\<Delta>)"
        using ImpL(5-) by (simp_all add: union_assoc \<Gamma>)
      hence  "is_mini_mset (\<Gamma>' + H' + \<Delta>' + (F, \<Delta>))" using ImpL(6) by(auto simp add: \<Gamma>)
      from ImpL(2)[OF * this] obtain Fa where IH1: "\<Gamma>' \<Rightarrow> Fa, \<Delta>'" "Fa, H' \<Rightarrow> F, \<Delta>" 
        "fst (pn_atoms Fa) \<subseteq> (patoms_mset \<Gamma>' \<union> natoms_mset \<Delta>') \<inter> (natoms_mset H' \<union> patoms_mset (F, \<Delta>))"
        "snd (pn_atoms Fa) \<subseteq> (natoms_mset \<Gamma>' \<union> patoms_mset \<Delta>') \<inter> (patoms_mset H' \<union> natoms_mset (F, \<Delta>))" "is_mini_formula Fa"  by blast
      from \<Gamma> have *: "G, \<Gamma>'' = (G, H') + \<Gamma>'" "\<Delta> + \<Delta>' = \<Delta> + \<Delta>'"
        using ImpL(5-) by (simp_all add: union_assoc)
      hence "is_mini_mset ((G, H') + \<Gamma>' + \<Delta> + \<Delta>')" using ImpL(6) by(simp add: \<Gamma>)
      from ImpL(4)[OF * this] obtain Ga where IH2: "G, H' \<Rightarrow> Ga, \<Delta>" "Ga, \<Gamma>' \<Rightarrow> \<Delta>'" 
        "fst (pn_atoms Ga) \<subseteq> (patoms_mset (G, H') \<union> natoms_mset \<Delta>) \<inter> (natoms_mset \<Gamma>' \<union> patoms_mset \<Delta>')"
        "snd (pn_atoms Ga) \<subseteq> (natoms_mset (G, H') \<union> patoms_mset \<Delta>) \<inter> (patoms_mset \<Gamma>' \<union> natoms_mset \<Delta>')" "is_mini_formula Ga" by blast
      let ?w = "Fa \<^bold>\<rightarrow> Ga"
      show ?thesis proof(intro exI[where x="?w"] conjI)
        from IH1(1) IH2(2) show "?w, \<Gamma>' \<Rightarrow> \<Delta>'"
          by (simp add: SCp.ImpL)
        from IH1(2) IH2(1) show "\<Gamma> \<Rightarrow> ?w, \<Delta>" unfolding \<Gamma>
          by(intro SCp.ImpL inR1[OF SCp.ImpR] SCp.ImpR) (simp_all add: weakenR weakenL)
        show "fst (pn_atoms ?w) \<subseteq> (patoms_mset \<Gamma> \<union> natoms_mset \<Delta>) \<inter> (natoms_mset \<Gamma>' \<union> patoms_mset \<Delta>')" 
             "snd (pn_atoms ?w) \<subseteq> (natoms_mset \<Gamma> \<union> patoms_mset \<Delta>) \<inter> (patoms_mset \<Gamma>' \<union> natoms_mset \<Delta>')"
          using IH1(3-) IH2(3-) unfolding \<Gamma> by (auto simp: prod_unions_def split: prod.splits)
        show "is_mini_formula ?w" using \<open>is_mini_formula Fa\<close> \<open>is_mini_formula Ga\<close> by simp
      qed
    next
      fix I' assume \<Gamma>': "\<Gamma>' = F \<^bold>\<rightarrow> G, I'" note ImpL(5)[unfolded \<Gamma>']
      from \<Gamma>' have *: "\<Gamma>'' = \<Gamma> + I'" "F, \<Delta> + \<Delta>' = \<Delta> + (F,\<Delta>')"
        using ImpL(5-) by(simp_all add: union_assoc add_ac(2,3))
      hence "is_mini_mset (\<Gamma> + I' + \<Delta> + (F, \<Delta>'))" using ImpL(6) by(auto simp add: \<Gamma>')
      from ImpL(2)[OF * this] obtain Fa
        where IH1: "\<Gamma> \<Rightarrow> Fa, \<Delta>" "Fa, I' \<Rightarrow> F, \<Delta>'" "is_mini_formula Fa"
        "fst (pn_atoms Fa) \<subseteq> (patoms_mset \<Gamma> \<union> natoms_mset \<Delta>) \<inter> (natoms_mset I' \<union> patoms_mset (F, \<Delta>'))"
        " snd (pn_atoms Fa) \<subseteq> (natoms_mset \<Gamma> \<union> patoms_mset \<Delta>) \<inter> (patoms_mset I' \<union> natoms_mset (F, \<Delta>'))" by blast
      from \<Gamma>' have *: "G, \<Gamma>'' = (G, I') + \<Gamma>" "\<Delta> + \<Delta>' = \<Delta>' + \<Delta>"
        using ImpL(5) by (simp_all add: add_ac \<open>\<Gamma>'' = \<Gamma> + I'\<close>)
      have "is_mini_mset ((G, I') + \<Gamma> + \<Delta>' + \<Delta>)"  using ImpL(6) by(auto simp add: \<Gamma>')
      from ImpL(4)[OF * this] obtain Ga
        where IH2: "G, I' \<Rightarrow> Ga, \<Delta>'" "Ga, \<Gamma> \<Rightarrow> \<Delta>" "is_mini_formula Ga"
        "fst (pn_atoms Ga) \<subseteq> (patoms_mset (G, I') \<union> natoms_mset \<Delta>') \<inter> (natoms_mset \<Gamma> \<union> patoms_mset \<Delta>)"
        "snd (pn_atoms Ga) \<subseteq> (natoms_mset (G, I') \<union> patoms_mset \<Delta>') \<inter> (patoms_mset \<Gamma> \<union> natoms_mset \<Delta>)" by blast
      let ?w = "(Fa \<^bold>\<rightarrow> Ga) \<^bold>\<rightarrow> \<bottom>"
      have "?w = to_mini_formula (\<^bold>\<not>(Fa \<^bold>\<rightarrow> Ga))" unfolding to_mini_formula.simps mini_to_mini[OF IH1(3)] mini_to_mini[OF IH2(3)] by (simp add: IH1(3) IH2(3) )
      show ?thesis proof(intro exI[of _ ?w] conjI)
        from IH1(1) IH2(2) show "\<Gamma> \<Rightarrow> ?w, \<Delta>"
          by(intro SCp.ImpR SCp.ImpL) (simp_all add: inR1 weakenR BotL_canonical)
        from IH1(2) IH2(1) show "?w, \<Gamma>' \<Rightarrow> \<Delta>'" unfolding \<Gamma>'
          by(blast intro!: SCp.ImpL SCp.ImpR dest: weakenL weakenR)+
        show "fst (pn_atoms ?w) \<subseteq> (patoms_mset \<Gamma> \<union> natoms_mset \<Delta>) \<inter> (natoms_mset \<Gamma>' \<union> patoms_mset \<Delta>')"
             "snd (pn_atoms ?w) \<subseteq> (natoms_mset \<Gamma> \<union> patoms_mset \<Delta>) \<inter> (patoms_mset \<Gamma>' \<union> natoms_mset \<Delta>')"
          using IH1(4-) IH2(4-) unfolding \<Gamma>' by (auto simp: prod_unions_def split: prod.splits)
        show "is_mini_formula ?w" using \<open>is_mini_formula Fa\<close> \<open>is_mini_formula Ga\<close> by simp
      qed
    qed
  next
  qed (metis add.commute is_mini_formula.simps union_iff union_single_eq_member)+
  define tms :: "'a formula multiset \<Rightarrow> 'a formula multiset"
    where "tms = image_mset to_mini_formula"
  have [simp]: "tms (A + B) = tms A + tms B" "tms {#F#} = {#to_mini_formula F#}" for A B F unfolding tms_def by simp_all
  have imm: "is_mini_mset (tms \<Gamma> + tms \<Gamma>' + tms \<Delta> + tms \<Delta>')" unfolding tms_def by auto
  from assms have "tms \<Gamma> + tms \<Gamma>' \<Rightarrow> tms \<Delta> + tms \<Delta>'" unfolding tms_def using SC_full_to_mini by force
  from mini[OF this imm] obtain F where hp:
    "tms \<Gamma> \<Rightarrow> F, tms \<Delta>" "F, tms \<Gamma>' \<Rightarrow> tms \<Delta>'"
    and su: " fst (pn_atoms F) \<subseteq> (patoms_mset (tms \<Gamma>) \<union> natoms_mset (tms \<Delta>)) \<inter> (natoms_mset (tms \<Gamma>') \<union> patoms_mset (tms \<Delta>'))"
      "snd (pn_atoms F) \<subseteq> (natoms_mset (tms \<Gamma>) \<union> patoms_mset (tms \<Delta>)) \<inter> (patoms_mset (tms \<Gamma>') \<union> natoms_mset (tms \<Delta>'))"
    and mf: "is_mini_formula F" by blast
  from hp mf have "tms \<Gamma> \<Rightarrow> tms (F, \<Delta>)" "tms (F, \<Gamma>') \<Rightarrow> tms \<Delta>'" using mini_to_mini[where 'a='a] unfolding tms_def by simp_all
  hence *: "\<Gamma> \<Rightarrow> F, \<Delta>" "F, \<Gamma>' \<Rightarrow> \<Delta>'" using SC_mini_to_full unfolding tms_def by blast+
  have "pn_atoms (to_mini_formula F) = pn_atoms F" for F :: "'a formula" by(induction F; simp add: prod_unions_def split: prod.splits)
  hence pn_tms: "patoms_mset (tms \<Gamma>) = patoms_mset \<Gamma>" "natoms_mset (tms \<Gamma>) = natoms_mset \<Gamma>" for \<Gamma> unfolding tms_def by simp_all
  from su[unfolded pn_tms] show ?thesis using that[of F, OF * _ _] by auto
qed
(* why this proof, again? Troelstra, somewhat unintuitively uses Fa \<^bold>\<rightarrow> Ga and Fa \<^bold>\<and> Ga as interpolants in the
   ImpL cases. The asymmetry seems weird, at least. This shows: at least, they are correct. *)

end
