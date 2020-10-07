subsubsection\<open>Mimicking the original\<close>

theory SC_Gentzen
imports SC_Depth SC_Cut
begin

text\<open>This system attempts to mimic the original sequent calculus 
  (``Reihen von Formeln, durch Kommata getrennt'', translates roughly to sequences of formulas, separated by a comma)~\cite{gentzen1935untersuchungen}.\<close>
inductive SCg :: "'a formula list \<Rightarrow> 'a formula list \<Rightarrow> bool" (infix "\<Rightarrow>" 30) where
Anfang: "[\<DD>] \<Rightarrow> [\<DD>]" |
FalschA: "[\<bottom>] \<Rightarrow> []" |
VerduennungA: "\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<DD>#\<Gamma> \<Rightarrow> \<Theta>" |
VerduennungS: "\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<DD>#\<Theta>" |
ZusammenziehungA: "\<DD>#\<DD>#\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<DD>#\<Gamma> \<Rightarrow> \<Theta>" |
ZusammenziehungS: "\<Gamma> \<Rightarrow> \<DD>#\<DD>#\<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<DD>#\<Theta>" |
VertauschungA: "\<Delta>@\<DD>#\<EE>#\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<Delta>@\<EE>#\<DD>#\<Gamma> \<Rightarrow> \<Theta>" |
VertauschungS: "\<Gamma> \<Rightarrow> \<Theta>@\<EE>#\<DD>#\<Lambda> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Theta>@\<DD>#\<EE>#\<Lambda>" |
Schnitt: "\<lbrakk>\<Gamma> \<Rightarrow> \<DD>#\<Theta>; \<DD>#\<Delta> \<Rightarrow> \<Lambda>\<rbrakk> \<Longrightarrow> \<Gamma>@\<Delta> \<Rightarrow> \<Theta>@\<Lambda>" |
UES: "\<lbrakk>\<Gamma> \<Rightarrow> \<AA>#\<Theta>; \<Gamma> \<Rightarrow> \<BB>#\<Theta>\<rbrakk> \<Longrightarrow> \<Gamma> \<Rightarrow> \<AA>\<^bold>\<and>\<BB>#\<Theta>" |
UEA1: "\<AA>#\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<AA>\<^bold>\<and>\<BB>#\<Gamma> \<Rightarrow> \<Theta>" | UEA2: "\<BB>#\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<AA>\<^bold>\<and>\<BB>#\<Gamma> \<Rightarrow> \<Theta>" |
OEA: "\<lbrakk>\<AA>#\<Gamma> \<Rightarrow> \<Theta>; \<BB>#\<Gamma> \<Rightarrow> \<Theta>\<rbrakk> \<Longrightarrow> \<AA>\<^bold>\<or>\<BB>#\<Gamma> \<Rightarrow> \<Theta>" |
OES1: "\<Gamma> \<Rightarrow> \<AA>#\<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<AA>\<^bold>\<or>\<BB>#\<Theta>" | OES2: "\<Gamma> \<Rightarrow> \<BB>#\<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<AA>\<^bold>\<or>\<BB>#\<Theta>" |
FES: "\<AA>#\<Gamma> \<Rightarrow> \<BB>#\<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<AA>\<^bold>\<rightarrow>\<BB>#\<Theta>" |
FEA: "\<lbrakk>\<Gamma> \<Rightarrow> \<AA>#\<Theta>; \<BB>#\<Delta> \<Rightarrow> \<Lambda>\<rbrakk> \<Longrightarrow> \<AA>\<^bold>\<rightarrow>\<BB>#\<Gamma>@\<Delta> \<Rightarrow> \<Theta>@\<Lambda>" |
NES: "\<AA>#\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<^bold>\<not>\<AA>#\<Theta>" |
NEA: "\<Gamma> \<Rightarrow> \<AA>#\<Theta> \<Longrightarrow> \<^bold>\<not>\<AA>#\<Gamma> \<Rightarrow> \<Theta>"
text\<open>Nota bene: E here stands for ``Einführung'', which is introduction and not elemination.\<close>
text\<open>The rule for @{term \<bottom>} is not part of the original calculus. Its addition is necessary to show equivalence to our @{const SCp}.\<close>

text\<open>Note that we purposefully did not recreate the fact that Gentzen sometimes puts his principal formulas on end and sometimes on the beginning of the list.\<close>

lemma AnfangTauschA: "\<DD>#\<Delta>@\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<Delta>@\<DD>#\<Gamma> \<Rightarrow> \<Theta>"
  by(induction \<Delta> arbitrary: \<Gamma> rule: List.rev_induct) (simp_all add: VertauschungA)
lemma AnfangTauschS: "\<Gamma> \<Rightarrow> \<DD>#\<Delta>@\<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>@\<DD>#\<Theta>"
  by(induction \<Delta> arbitrary: \<Theta> rule: List.rev_induct) (simp_all add: VertauschungS)
lemma MittenTauschA: "\<Delta>@\<DD>#\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<DD>#\<Delta>@\<Gamma> \<Rightarrow> \<Theta>"
  by(induction \<Delta> arbitrary: \<Gamma> rule: List.rev_induct) (simp_all add: VertauschungA)
lemma MittenTauschS: "\<Gamma> \<Rightarrow> \<Delta>@\<DD>#\<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<DD>#\<Delta>@\<Theta>"
  by(induction \<Delta> arbitrary: \<Theta> rule: List.rev_induct) (simp_all add: VertauschungS)

lemma BotLe: "\<bottom>\<in>set \<Gamma> \<Longrightarrow> \<Gamma>\<Rightarrow>\<Delta>"
proof -
  have A: "\<bottom>#\<Gamma>\<Rightarrow>[]" for \<Gamma> by(induction \<Gamma>) (simp_all add: FalschA VerduennungA VertauschungA[where \<Delta>=Nil, simplified])
  have *: "\<bottom>#\<Gamma>\<Rightarrow>\<Delta>" for \<Gamma> by(induction \<Delta>) (simp_all add: A VerduennungS)
  assume "\<bottom>\<in>set \<Gamma>" then obtain \<Gamma>1 \<Gamma>2 where \<Gamma>: "\<Gamma> = \<Gamma>1@\<bottom>#\<Gamma>2" by (meson split_list)
  show ?thesis unfolding \<Gamma> using AnfangTauschA * by blast
qed

lemma Axe: "A \<in> set \<Gamma> \<Longrightarrow> A \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof -
  have A: "A#\<Gamma> \<Rightarrow> [A]" for \<Gamma> by(induction \<Gamma>) (simp_all add: Anfang VertauschungA[where \<Delta>=Nil, simplified] VerduennungA)
  have S: "A#\<Gamma> \<Rightarrow> A#\<Delta>" for \<Gamma> \<Delta> by(induction \<Delta>) (simp_all add: A Anfang VertauschungS[where \<Theta>=Nil, simplified] VerduennungS)
  assume "A \<in> set \<Gamma>" "A \<in> set \<Delta>" thus ?thesis
    apply(-)
    apply(drule split_list)+
    apply(clarify)
    apply(intro AnfangTauschA AnfangTauschS)
    apply(rule S)
  done
qed

lemma VerduennungListeA: "\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<Gamma>@\<Gamma> \<Rightarrow> \<Theta>"
proof -
  have "\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<exists>\<Gamma>''. \<Gamma>=\<Gamma>''@\<Gamma>' \<Longrightarrow> \<Gamma>'@\<Gamma> \<Rightarrow> \<Theta>" for \<Gamma>'
  proof(induction \<Gamma>')
    case (Cons a as)
    from \<open>\<exists>\<Gamma>''. \<Gamma> = \<Gamma>'' @ a # as\<close> guess \<Gamma>'' ..
    hence "\<exists>\<Gamma>''. \<Gamma> = \<Gamma>'' @ as" by(intro exI[where x="\<Gamma>'' @ [a]"]) simp
    from Cons.IH[OF Cons.prems(1) this] have "as @ \<Gamma> \<Rightarrow> \<Theta>" .
    thus ?case using VerduennungA by simp
  qed simp
  thus "\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<Gamma>@\<Gamma> \<Rightarrow> \<Theta>" by simp
qed
lemma VerduennungListeS: "\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Theta>@\<Theta>"
proof -
  have "\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<exists>\<Theta>''. \<Theta>=\<Theta>''@\<Theta>' \<Longrightarrow> \<Gamma> \<Rightarrow> \<Theta>'@\<Theta>" for \<Theta>'
  proof(induction \<Theta>')
    case (Cons a as)
    from \<open>\<exists>\<Theta>''. \<Theta> = \<Theta>'' @ a # as\<close> guess \<Theta>'' ..
    hence "\<exists>\<Theta>''. \<Theta> = \<Theta>'' @ as" by(intro exI[where x="\<Theta>'' @ [a]"]) simp
    from Cons.IH[OF Cons.prems(1) this] have " \<Gamma> \<Rightarrow> as @ \<Theta>" .
    thus ?case using VerduennungS by simp
  qed simp
  thus "\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Theta>@\<Theta>" by simp
qed
(* wak, those weren't the droids I was looking for. *)
lemma ZusammenziehungListeA: "\<Gamma>@\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Theta>"
proof -
  have "\<Gamma>'@\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<exists>\<Gamma>''. \<Gamma>=\<Gamma>''@\<Gamma>' \<Longrightarrow> \<Gamma> \<Rightarrow> \<Theta>" for \<Gamma>'
  proof(induction \<Gamma>')
    case (Cons a \<Gamma>')
    from \<open>\<exists>\<Gamma>''. \<Gamma> = \<Gamma>'' @ a # \<Gamma>'\<close> guess \<Gamma>'' .. note \<Gamma>'' = this
    then obtain \<Gamma>1 \<Gamma>2 where \<Gamma>: "\<Gamma> = \<Gamma>1 @ a # \<Gamma>2" by blast
    from \<Gamma>'' have **: "\<exists>\<Gamma>''. \<Gamma> = \<Gamma>'' @ \<Gamma>'" by(intro exI[where x="\<Gamma>'' @ [a]"]) simp
    from Cons.prems(1) have "a # (a # \<Gamma>') @ \<Gamma>1 @ \<Gamma>2 \<Rightarrow> \<Theta>" unfolding \<Gamma>  using MittenTauschA by (metis append_assoc)
    hence "(a # \<Gamma>') @ \<Gamma>1 @ \<Gamma>2 \<Rightarrow> \<Theta>" using ZusammenziehungA by auto
    hence "\<Gamma>' @ \<Gamma> \<Rightarrow> \<Theta>" unfolding \<Gamma>  using AnfangTauschA by (metis append_Cons append_assoc)
    from Cons.IH[OF this **] show "\<Gamma> \<Rightarrow> \<Theta>" .
  qed simp
  thus "\<Gamma>@\<Gamma> \<Rightarrow> \<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Theta>" by simp
qed
lemma ZusammenziehungListeS: "\<Gamma> \<Rightarrow> \<Theta>@\<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Theta>"
proof -
  have "\<Gamma> \<Rightarrow> \<Theta>'@\<Theta> \<Longrightarrow> \<exists>\<Theta>''. \<Theta>=\<Theta>''@\<Theta>' \<Longrightarrow> \<Gamma> \<Rightarrow> \<Theta>" for \<Theta>'
  proof(induction \<Theta>')
    case (Cons a \<Theta>')
    from \<open>\<exists>\<Theta>''. \<Theta> = \<Theta>'' @ a # \<Theta>'\<close> guess \<Theta>'' .. note \<Theta>'' = this
    then obtain \<Theta>1 \<Theta>2 where \<Theta>: "\<Theta> = \<Theta>1 @ a # \<Theta>2" by blast
    from \<Theta>'' have **: "\<exists>\<Theta>''. \<Theta> = \<Theta>'' @ \<Theta>'" by(intro exI[where x="\<Theta>'' @ [a]"]) simp
    from Cons.prems(1) have "\<Gamma> \<Rightarrow> a # (a # \<Theta>') @ \<Theta>1 @ \<Theta>2" unfolding \<Theta>  using MittenTauschS by (metis append_assoc)
    hence "\<Gamma> \<Rightarrow> (a # \<Theta>') @ \<Theta>1 @ \<Theta>2" using ZusammenziehungS by auto
    hence "\<Gamma> \<Rightarrow> \<Theta>' @ \<Theta>" unfolding \<Theta>  using AnfangTauschS by (metis append_Cons append_assoc)
    from Cons.IH[OF this **] show "\<Gamma> \<Rightarrow> \<Theta>" .
  qed simp
  thus "\<Gamma> \<Rightarrow> \<Theta>@\<Theta> \<Longrightarrow> \<Gamma> \<Rightarrow>\<Theta>" by simp
qed

theorem gentzen_sc_eq: "mset \<Gamma> \<Rightarrow> mset \<Delta> \<longleftrightarrow> \<Gamma> \<Rightarrow> \<Delta>" proof
  assume "mset \<Gamma> \<Rightarrow> mset \<Delta>" 
  then obtain n where "mset \<Gamma> \<Rightarrow> mset \<Delta> \<down> n" unfolding SC_SCp_eq[symmetric] ..
  thus "\<Gamma> \<Rightarrow> \<Delta>"
  (* structural induction not necessary at all. I still don't get it. *)
  proof(induction n arbitrary: \<Gamma> \<Delta> rule: nat.induct)
    case (Suc n) 
    have sr: "\<exists>\<Gamma>1 \<Gamma>2. \<Gamma> = \<Gamma>1 @ F # \<Gamma>2 \<and> \<Gamma>' = mset (\<Gamma>1@\<Gamma>2)" (is "?s") if "mset \<Gamma> = F, \<Gamma>'" for \<Gamma> \<Gamma>' F proof -
      from that obtain \<Gamma>1 \<Gamma>2 where \<Gamma>: "\<Gamma> = \<Gamma>1 @ F # \<Gamma>2" by (metis split_list add.commute ex_mset list.set_intros(1) mset.simps(2) set_mset_mset)
      hence \<Gamma>': "\<Gamma>' = mset (\<Gamma>1@\<Gamma>2)" using that by auto
      show ?s using \<Gamma> \<Gamma>' by blast
    qed
    from Suc.prems show ?case proof(cases rule: SCc.cases)
      case BotL thus ?thesis using BotLe by simp
    next
      case Ax thus ?thesis using Axe by simp
    next
      case (NotL \<Gamma>' F)
      from \<open>mset \<Gamma> = \<^bold>\<not> F, \<Gamma>'\<close> obtain \<Gamma>1 \<Gamma>2 where \<Gamma>: "\<Gamma> = \<Gamma>1 @ \<^bold>\<not> F # \<Gamma>2" 
        by (metis split_list add.commute ex_mset list.set_intros(1) mset.simps(2) set_mset_mset)
      hence \<Gamma>': "\<Gamma>' = mset (\<Gamma>1@\<Gamma>2)" using NotL(1) by simp
      from \<open>\<Gamma>' \<Rightarrow> F, mset \<Delta> \<down> n\<close> have "mset (\<Gamma>1@\<Gamma>2) \<Rightarrow> mset (F#\<Delta>) \<down> n" unfolding \<Gamma>' by (simp add: add.commute)
      from Suc.IH[OF this] show ?thesis unfolding \<Gamma> using AnfangTauschA NEA by blast
    next
      case (NotR F \<Delta>')
      from sr[OF NotR(1)] guess \<Delta>1 .. then guess \<Delta>2 .. note \<Delta> = this
      with NotR have "mset (F#\<Gamma>) \<Rightarrow> mset (\<Delta>1@\<Delta>2) \<down> n" by (simp add: add.commute)
      from Suc.IH[OF this] show ?thesis using \<Delta> using AnfangTauschS NES by blast
    next
      case (AndR F \<Delta>' G)
      from sr[OF AndR(1)] guess \<Delta>1 .. then guess \<Delta>2 .. note \<Delta> = this
      with AndR have "mset \<Gamma> \<Rightarrow> mset (F # \<Delta>1@\<Delta>2) \<down> n" "mset \<Gamma> \<Rightarrow> mset (G # \<Delta>1@\<Delta>2) \<down> n" by (simp add: add.commute)+
      from this[THEN Suc.IH] show ?thesis using \<Delta> using AnfangTauschS UES by blast
    next
      case (OrR F G \<Delta>')
      from sr[OF OrR(1)] guess \<Delta>1 .. then guess \<Delta>2 .. note \<Delta> = this
      with OrR have "mset \<Gamma> \<Rightarrow> mset (G # F # \<Delta>1@\<Delta>2) \<down> n" by (simp add: add.commute add.left_commute add_mset_commute)
      from this[THEN Suc.IH] have "\<Gamma> \<Rightarrow> G # F # \<Delta>1 @ \<Delta>2" .
      with OES2 have "\<Gamma> \<Rightarrow> F \<^bold>\<or> G # F # \<Delta>1 @ \<Delta>2" .
      with VertauschungS[where \<Theta>=Nil, simplified] have "\<Gamma> \<Rightarrow> F # F \<^bold>\<or> G # \<Delta>1 @ \<Delta>2" .
      with OES1 have "\<Gamma> \<Rightarrow> F \<^bold>\<or> G # F \<^bold>\<or> G # \<Delta>1 @ \<Delta>2" .
      hence "\<Gamma> \<Rightarrow> F \<^bold>\<or> G # \<Delta>1 @ \<Delta>2" using ZusammenziehungS by fast 
      thus ?thesis unfolding \<Delta>[THEN conjunct1] using AnfangTauschS by blast
    next
      case (ImpR F G \<Delta>')
      from sr[OF ImpR(1)] guess \<Delta>1 .. then guess \<Delta>2 .. note \<Delta> = this
      with ImpR have "mset (F#\<Gamma>) \<Rightarrow> mset (G # \<Delta>1@\<Delta>2) \<down> n" by (simp add: add.commute)
      from this[THEN Suc.IH] show ?thesis using \<Delta> using AnfangTauschS FES by blast
    next
      case (AndL F G \<Gamma>')
      from sr[OF this(1)] guess \<Gamma>1 .. then guess \<Gamma>2 .. note \<Gamma> = this
      with AndL have "mset (G # F # \<Gamma>1@\<Gamma>2) \<Rightarrow> mset \<Delta> \<down> n" by (simp add: add.commute add.left_commute add_mset_commute)
      from this[THEN Suc.IH] have "G # F # \<Gamma>1 @ \<Gamma>2 \<Rightarrow> \<Delta>" .
      with UEA2 have "F \<^bold>\<and> G # F # \<Gamma>1 @ \<Gamma>2 \<Rightarrow> \<Delta>" .
      with VertauschungA[where \<Delta>=Nil, simplified] have "F # F \<^bold>\<and> G # \<Gamma>1 @ \<Gamma>2 \<Rightarrow> \<Delta>" .
      with UEA1 have "F \<^bold>\<and> G # F \<^bold>\<and> G # \<Gamma>1 @ \<Gamma>2 \<Rightarrow> \<Delta>" .
      hence "F \<^bold>\<and> G # \<Gamma>1 @ \<Gamma>2 \<Rightarrow> \<Delta>" using ZusammenziehungA by fast 
      thus ?thesis unfolding \<Gamma>[THEN conjunct1] using AnfangTauschA by blast
    next
      case (OrL F \<Delta>' G)
      from sr[OF this(1)] guess \<Gamma>1 .. then guess \<Gamma>2 .. note \<Gamma> = this
      with OrL have "mset (F # \<Gamma>1@\<Gamma>2) \<Rightarrow> mset \<Delta> \<down> n" "mset (G # \<Gamma>1@\<Gamma>2) \<Rightarrow> mset \<Delta> \<down> n" by (simp add: add.commute)+
      from this[THEN Suc.IH] show ?thesis using \<Gamma> using AnfangTauschA OEA by blast
    next
      case (ImpL \<Gamma>' F G)
      from sr[OF this(1)] guess \<Gamma>1 .. then guess \<Gamma>2 .. note \<Gamma> = this
      with ImpL have "mset (\<Gamma>1@\<Gamma>2) \<Rightarrow> mset (F#\<Delta>) \<down> n" "mset (G # \<Gamma>1@\<Gamma>2) \<Rightarrow> mset \<Delta> \<down> n" by (simp add: add.commute)+
      from this[THEN Suc.IH] have "\<Gamma>1 @ \<Gamma>2 \<Rightarrow> F # \<Delta>" "G # \<Gamma>1 @ \<Gamma>2 \<Rightarrow> \<Delta>" .
      from FEA[OF this] have "F \<^bold>\<rightarrow> G # (\<Gamma>1 @ \<Gamma>2) @ (\<Gamma>1 @ \<Gamma>2) \<Rightarrow> \<Delta> @ \<Delta>" .
      hence "F \<^bold>\<rightarrow> G # (\<Gamma>1 @ \<Gamma>2) @ (F \<^bold>\<rightarrow> G # \<Gamma>1 @ \<Gamma>2) \<Rightarrow> \<Delta> @ \<Delta>" using AnfangTauschA VerduennungA by blast (* given the form of ZusammenziehungListeA, using this intermediate step is just easier. maybe a different from for ZusammenziehungListeA would be nice? *)
      hence "F \<^bold>\<rightarrow> G # (\<Gamma>1 @ \<Gamma>2) \<Rightarrow> \<Delta> @ \<Delta>" using ZusammenziehungListeA[where \<Gamma>="F \<^bold>\<rightarrow> G # (\<Gamma>1 @ \<Gamma>2)"] by simp
      thus ?thesis unfolding \<Gamma>[THEN conjunct1] by(intro AnfangTauschA; elim ZusammenziehungListeS)
    qed
  qed blast
next
  have mset_Cons[simp]: "mset (A # S) = A, mset S" for A::"'a formula" and S by (simp add: add.commute)
  note mset.simps(2)[simp del]
  show "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> mset \<Gamma> \<Rightarrow> mset \<Delta>" proof(induction rule: SCg.induct)
    (*sed -n '/^\([^\\]*\):/ {N;s/_\\\?//g; s/let.*$//; s/\n//; s/[\\:]//g; s/fix //; s/  / /g; s/^.*$/case (&) thus ?case sorry/; p;}' ${print_cases} *)
    case (Anfang \<DD>) thus ?case using extended_Ax SC_SCp_eq by force
  next
    case (FalschA) thus ?case using SCp.BotL by force
  next
    case (VerduennungA \<Gamma> \<Theta> \<DD>) thus ?case by (simp add: SC.weakenL)
  next
    case (VerduennungS \<Gamma> \<Theta> \<DD>) thus ?case by (simp add: SC.weakenR)
  next
    case (ZusammenziehungA \<DD> \<Gamma> \<Theta>) thus ?case using contractL by force
  next
    case (ZusammenziehungS \<Gamma> \<DD> \<Theta>) thus ?case using contract by force
  next
    case (VertauschungA \<Delta> \<DD> \<EE> \<Gamma> \<Theta>) thus ?case by fastforce
  next
    case (VertauschungS \<Gamma> \<Theta> \<EE> \<DD> \<Lambda>) thus ?case by fastforce
  next
    case (Schnitt \<Gamma> \<DD> \<Theta> \<Delta> \<Lambda>)
    hence "mset \<Gamma> \<Rightarrow> \<DD>,mset \<Theta>" "\<DD>,mset \<Delta> \<Rightarrow> mset \<Lambda>" using SC_SCp_eq by auto
    from cut_cf[OF this] show ?case unfolding SC_SCp_eq by simp
  next
    case (UES \<Gamma> \<AA> \<Theta> \<BB>) thus ?case using SCp.AndR by (simp add: SC_SCp_eq)
  next
    case (UEA1 \<AA> \<Gamma> \<Theta> \<BB>) 
    from \<open>mset (\<AA> # \<Gamma>) \<Rightarrow> mset \<Theta>\<close> have "\<AA>,\<BB>,mset \<Gamma> \<Rightarrow> mset \<Theta>" using SC.weakenL by auto
    thus ?case using SCp.AndL by force
  next
    case (UEA2 \<BB> \<Gamma> \<Theta> \<AA>)
    from \<open>mset (\<BB> # \<Gamma>) \<Rightarrow> mset \<Theta>\<close> have "\<AA>,\<BB>,mset \<Gamma> \<Rightarrow> mset \<Theta>" using SC.weakenL by auto
    thus ?case using SCp.AndL by force
  next
    case (OEA \<AA> \<Gamma> \<Theta> \<BB>) thus ?case unfolding SC_SCp_eq by (simp add: SCp.OrL)
  next
    case (OES1 \<Gamma> \<AA> \<Theta> \<BB>) thus ?case using SC.weakenR[where 'a='a] by(auto intro!: SCp.intros(3-))
  next
    case (OES2 \<Gamma> \<BB> \<Theta> \<AA>) thus ?case by (simp add: SC.weakenR SCp.OrR)
  next
    case (FES \<AA> \<Gamma> \<BB> \<Theta>) thus ?case using weakenR unfolding SC_SCp_eq by (simp add: SCp.ImpR)
  next
    case (FEA \<Gamma> \<AA> \<Theta> \<BB> \<Delta> \<Lambda>) 
    from \<open>mset \<Gamma> \<Rightarrow> mset (\<AA> # \<Theta>)\<close>[THEN weakenL_set, THEN weakenR_set, of "mset \<Delta>" "mset \<Lambda>"]
    have S: "mset (\<Gamma>@\<Delta>) \<Rightarrow> \<AA>,mset (\<Theta>@\<Lambda>)" unfolding mset_append mset_Cons by (simp add: add_ac) (* sledgehammer comes up with some funny proof using cut\<dots> *)
    from FEA obtain m where "mset (\<BB> # \<Delta>) \<Rightarrow> mset \<Lambda>" by blast
    hence "mset \<Gamma> + mset (\<BB> # \<Delta>) \<Rightarrow> mset \<Theta> + mset \<Lambda>" using weakenL_set weakenR_set by fast
    hence A: "\<BB>,mset (\<Gamma>@\<Delta>) \<Rightarrow> mset (\<Theta>@\<Lambda>)" by (simp add: add.left_commute)
    show ?case using S A SC_SCp_eq SCp.ImpL unfolding mset_Cons by blast
  next
    case (NES \<AA> \<Gamma> \<Theta>) thus ?case using SCp.NotR by(simp add: SC_SCp_eq)
  next
    case (NEA \<Gamma> \<AA> \<Theta>) thus ?case using SCp.NotL by(simp add: SC_SCp_eq)
  qed
qed


end
