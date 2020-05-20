theory EventSystems
imports "../Basics/Prefix" "../Basics/Projection"
begin

(* structural representation of event systems *)
record 'e ES_rec =
  E_ES ::  "'e set"
  I_ES ::  "'e set"
  O_ES ::  "'e set"
  Tr_ES :: "('e list) set"

(* syntax abbreviations for ES_rec *)
abbreviation ESrecEES :: "'e ES_rec \<Rightarrow> 'e set"
("E\<^bsub>_\<^esub>" [1000] 1000)
where
"E\<^bsub>ES\<^esub> \<equiv> (E_ES ES)"

abbreviation ESrecIES :: "'e ES_rec \<Rightarrow> 'e set"
("I\<^bsub>_\<^esub>" [1000] 1000)
where
"I\<^bsub>ES\<^esub> \<equiv> (I_ES ES)"

abbreviation ESrecOES :: "'e ES_rec \<Rightarrow> 'e set"
("O\<^bsub>_\<^esub>" [1000] 1000)
where
"O\<^bsub>ES\<^esub> \<equiv> (O_ES ES)"

abbreviation ESrecTrES :: "'e ES_rec \<Rightarrow> ('e list) set"
("Tr\<^bsub>_\<^esub>" [1000] 1000)
where
"Tr\<^bsub>ES\<^esub> \<equiv> (Tr_ES ES)"

(* side conditions for event systems *)
definition es_inputs_are_events :: "'e ES_rec \<Rightarrow> bool"
where
"es_inputs_are_events ES \<equiv> I\<^bsub>ES\<^esub> \<subseteq> E\<^bsub>ES\<^esub>"

definition es_outputs_are_events :: "'e ES_rec \<Rightarrow> bool"
where
"es_outputs_are_events ES \<equiv> O\<^bsub>ES\<^esub> \<subseteq> E\<^bsub>ES\<^esub>"

definition es_inputs_outputs_disjoint :: "'e ES_rec \<Rightarrow> bool"
where
"es_inputs_outputs_disjoint ES \<equiv> I\<^bsub>ES\<^esub> \<inter> O\<^bsub>ES\<^esub> = {}"

definition traces_contain_events :: "'e ES_rec \<Rightarrow> bool"
where
"traces_contain_events ES \<equiv> \<forall>l \<in> Tr\<^bsub>ES\<^esub>. \<forall>e \<in> (set l). e \<in> E\<^bsub>ES\<^esub>"

definition traces_prefixclosed :: "'e ES_rec \<Rightarrow> bool"
where
"traces_prefixclosed ES \<equiv> prefixclosed Tr\<^bsub>ES\<^esub>"

definition ES_valid :: "'e ES_rec \<Rightarrow> bool"
where
"ES_valid ES \<equiv> 
  es_inputs_are_events ES \<and> es_outputs_are_events ES 
  \<and> es_inputs_outputs_disjoint ES \<and> traces_contain_events ES 
  \<and> traces_prefixclosed ES"

(* Event systems are instances of ES_rec that satisfy ES_valid. *)

(* Totality of an event system ES with respect to a set E *)
definition total :: "'e ES_rec \<Rightarrow> 'e set \<Rightarrow> bool"
where
"total ES E \<equiv> E \<subseteq> E\<^bsub>ES\<^esub> \<and> (\<forall>\<tau> \<in> Tr\<^bsub>ES\<^esub>. \<forall>e \<in> E. \<tau> @ [e] \<in> Tr\<^bsub>ES\<^esub>)"

lemma totality: "\<lbrakk> total ES E; t \<in> Tr\<^bsub>ES\<^esub>; set t' \<subseteq> E \<rbrakk> \<Longrightarrow> t @ t' \<in> Tr\<^bsub>ES\<^esub>"
  by (induct t' rule: rev_induct, force, simp only: total_def, auto)


(* structural representation of composed event systems (composition operator) *)
definition composeES :: "'e ES_rec \<Rightarrow> 'e ES_rec \<Rightarrow> 'e ES_rec" 
where
"composeES ES1 ES2 \<equiv>  
  \<lparr>  
    E_ES  = E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>, 
    I_ES  = (I\<^bsub>ES1\<^esub> - O\<^bsub>ES2\<^esub>) \<union> (I\<^bsub>ES2\<^esub> - O\<^bsub>ES1\<^esub>),
    O_ES  = (O\<^bsub>ES1\<^esub> - I\<^bsub>ES2\<^esub>) \<union> (O\<^bsub>ES2\<^esub> - I\<^bsub>ES1\<^esub>),
    Tr_ES = {\<tau> . (\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub> \<and> (\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub> 
                  \<and> (set \<tau> \<subseteq> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>)} 
  \<rparr>"

abbreviation composeESAbbrv :: "'e ES_rec \<Rightarrow> 'e ES_rec \<Rightarrow> 'e ES_rec"
("_ \<parallel> _"[1000] 1000)
where
"ES1 \<parallel> ES2 \<equiv> (composeES ES1 ES2)"

definition composable :: "'e ES_rec \<Rightarrow> 'e ES_rec \<Rightarrow> bool"
where
"composable ES1 ES2 \<equiv> (E\<^bsub>ES1\<^esub> \<inter> E\<^bsub>ES2\<^esub>) \<subseteq> ((O\<^bsub>ES1\<^esub> \<inter> I\<^bsub>ES2\<^esub>) \<union> (O\<^bsub>ES2\<^esub> \<inter> I\<^bsub>ES1\<^esub>))"


(* composing two event systems yields an event system *)
lemma composeES_yields_ES: 
  "\<lbrakk> ES_valid ES1; ES_valid ES2 \<rbrakk> \<Longrightarrow> ES_valid (ES1 \<parallel> ES2)"
  unfolding ES_valid_def
proof (auto)
  assume ES1_inputs_are_events: "es_inputs_are_events ES1"
  assume ES2_inputs_are_events: "es_inputs_are_events ES2"
  show "es_inputs_are_events (ES1 \<parallel> ES2)" unfolding composeES_def es_inputs_are_events_def
    proof (simp)
      have subgoal11: "I\<^bsub>ES1\<^esub> - O\<^bsub>ES2\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>"
      proof (auto)
        fix x
        assume "x \<in> I\<^bsub>ES1\<^esub>"
        with ES1_inputs_are_events  show "x \<in> E\<^bsub>ES1\<^esub>" 
          by (auto simp add: es_inputs_are_events_def)
      qed
      have subgoal12: "I\<^bsub>ES2\<^esub> - O\<^bsub>ES1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>"    
      proof (rule subsetI, rule UnI2, auto)
        fix x
        assume "x \<in> I\<^bsub>ES2\<^esub>"
        with ES2_inputs_are_events show "x \<in> E\<^bsub>ES2\<^esub>" 
          by (auto simp add: es_inputs_are_events_def)
      qed
      from subgoal11 subgoal12 
      show "I\<^bsub>ES1\<^esub> - O\<^bsub>ES2\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub> \<and> I\<^bsub>ES2\<^esub> - O\<^bsub>ES1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>" ..
  qed
next
  assume ES1_outputs_are_events: "es_outputs_are_events ES1"
  assume ES2_outputs_are_events: "es_outputs_are_events ES2"
  show "es_outputs_are_events (ES1 \<parallel> ES2)" 
    unfolding composeES_def es_outputs_are_events_def
    proof (simp)
      have subgoal21: "O\<^bsub>ES1\<^esub> - I\<^bsub>ES2\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>"
      proof (auto)
        fix x
        assume "x \<in> O\<^bsub>ES1\<^esub>"
        with ES1_outputs_are_events  show "x \<in> E\<^bsub>ES1\<^esub>" 
          by (auto simp add: es_outputs_are_events_def)
      qed
      have subgoal22: "O\<^bsub>ES2\<^esub> - I\<^bsub>ES1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>"    
      proof (rule subsetI, rule UnI2, auto)
        fix x
        assume "x \<in> O\<^bsub>ES2\<^esub>"
        with ES2_outputs_are_events show "x \<in> E\<^bsub>ES2\<^esub>" 
          by (auto simp add: es_outputs_are_events_def)
      qed
      from subgoal21 subgoal22 
      show "O\<^bsub>ES1\<^esub> - I\<^bsub>ES2\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub> \<and> O\<^bsub>ES2\<^esub> - I\<^bsub>ES1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>" ..
  qed
next
  assume ES1_inputs_outputs_disjoint: "es_inputs_outputs_disjoint ES1"
  assume ES2_inputs_outputs_disjoint: "es_inputs_outputs_disjoint ES2"
  show "es_inputs_outputs_disjoint (ES1 \<parallel> ES2)" 
    unfolding composeES_def es_inputs_outputs_disjoint_def
    proof (simp)
      have subgoal31:
        "{} \<subseteq> (I\<^bsub>ES1\<^esub> - O\<^bsub>ES2\<^esub> \<union> (I\<^bsub>ES2\<^esub> - O\<^bsub>ES1\<^esub>)) \<inter> (O\<^bsub>ES1\<^esub> - I\<^bsub>ES2\<^esub> \<union> (O\<^bsub>ES2\<^esub> - I\<^bsub>ES1\<^esub>))" 
        by auto
      have subgoal32:
        "(I\<^bsub>ES1\<^esub> - O\<^bsub>ES2\<^esub> \<union> (I\<^bsub>ES2\<^esub> - O\<^bsub>ES1\<^esub>)) \<inter> (O\<^bsub>ES1\<^esub> - I\<^bsub>ES2\<^esub> \<union> (O\<^bsub>ES2\<^esub> - I\<^bsub>ES1\<^esub>)) \<subseteq> {}"
      proof (rule subsetI, erule IntE)
      fix x
      assume ass1: "x \<in> I\<^bsub>ES1\<^esub> - O\<^bsub>ES2\<^esub> \<union> (I\<^bsub>ES2\<^esub> - O\<^bsub>ES1\<^esub>)"
      then have ass1': "x \<in> I\<^bsub>ES1\<^esub> - O\<^bsub>ES2\<^esub> \<or> x \<in> (I\<^bsub>ES2\<^esub> - O\<^bsub>ES1\<^esub>)" 
        by auto
      assume ass2: "x \<in> O\<^bsub>ES1\<^esub> - I\<^bsub>ES2\<^esub> \<union> (O\<^bsub>ES2\<^esub> - I\<^bsub>ES1\<^esub>)"
      then have ass2':"x \<in> O\<^bsub>ES1\<^esub> - I\<^bsub>ES2\<^esub> \<or> x \<in> (O\<^bsub>ES2\<^esub> - I\<^bsub>ES1\<^esub>)" 
        by auto
      note ass1'
      moreover {
        assume left1: "x \<in> I\<^bsub>ES1\<^esub> - O\<^bsub>ES2\<^esub>"
        note ass2'
        moreover {
          assume left2: "x \<in> O\<^bsub>ES1\<^esub> - I\<^bsub>ES2\<^esub>"
          with left1 have "x\<in> (I\<^bsub>ES1\<^esub>) \<inter> (O\<^bsub>ES1\<^esub>)" 
            by (auto)
          with ES1_inputs_outputs_disjoint have "x\<in>{}" 
            by (auto simp add: es_inputs_outputs_disjoint_def)
        }
        moreover {
          assume right2: "x \<in> (O\<^bsub>ES2\<^esub> - I\<^bsub>ES1\<^esub>)"
          with left1 have "x\<in> (I\<^bsub>ES1\<^esub> - I\<^bsub>ES1\<^esub>)" 
            by auto
          hence "x\<in>{}" 
            by auto                
        }
        ultimately have "x\<in>{}" ..
      }
      moreover {
        assume right1: "x \<in> I\<^bsub>ES2\<^esub> - O\<^bsub>ES1\<^esub>"
        note ass2'
        moreover {
          assume left2: "x \<in> O\<^bsub>ES1\<^esub> - I\<^bsub>ES2\<^esub>"
          with right1 have "x\<in> (I\<^bsub>ES2\<^esub> - I\<^bsub>ES2\<^esub>)" 
            by auto
          hence "x\<in>{}" 
            by auto
        }
        moreover {
          assume right2: "x \<in> (O\<^bsub>ES2\<^esub> - I\<^bsub>ES1\<^esub>)"
          with right1 have "x \<in> (I\<^bsub>ES2\<^esub> \<inter> O\<^bsub>ES2\<^esub>)" 
            by auto
          with ES2_inputs_outputs_disjoint have "x\<in>{}" 
            by (auto simp add: es_inputs_outputs_disjoint_def)
        }
        ultimately have "x\<in>{}" ..
      }
      ultimately show "x\<in>{}" ..
    qed

    from subgoal31 subgoal32 
    show "(I\<^bsub>ES1\<^esub> - O\<^bsub>ES2\<^esub> \<union> (I\<^bsub>ES2\<^esub> - O\<^bsub>ES1\<^esub>)) \<inter> (O\<^bsub>ES1\<^esub> - I\<^bsub>ES2\<^esub> \<union> (O\<^bsub>ES2\<^esub> - I\<^bsub>ES1\<^esub>)) = {}" 
      by auto
  qed
next
  show "traces_contain_events (ES1 \<parallel> ES2)" unfolding composeES_def traces_contain_events_def
    proof (clarsimp)
      fix l e
      assume "e \<in> set l"
        and "set l \<subseteq> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>"
      then have e_in_union: "e \<in> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>" 
        by auto
      assume "e \<notin> E\<^bsub>ES2\<^esub>"
      with e_in_union show "e \<in> E\<^bsub>ES1\<^esub>" 
        by auto
    qed
next
  assume ES1_traces_prefixclosed: "traces_prefixclosed ES1"
  assume ES2_traces_prefixclosed: "traces_prefixclosed ES2"
  show "traces_prefixclosed (ES1 \<parallel> ES2)" 
    unfolding composeES_def traces_prefixclosed_def prefixclosed_def prefix_def
  proof (clarsimp)
    fix l2 l3
    have l2l3split: "(l2 @ l3) \<upharpoonleft> E\<^bsub>ES1\<^esub> = (l2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES1\<^esub>)" 
      by (rule projection_concatenation_commute)
    assume "(l2 @ l3) \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
    with l2l3split have l2l3cattrace: "(l2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>" 
      by auto
    have theprefix: "(l2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<preceq> ((l2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES1\<^esub>))" 
      by (simp add: prefix_def)
    have prefixclosure: "\<forall> es1 \<in> (Tr\<^bsub>ES1\<^esub>). \<forall> es2. es2 \<preceq> es1 \<longrightarrow> es2 \<in> (Tr\<^bsub>ES1\<^esub>)" 
      by (clarsimp, insert ES1_traces_prefixclosed, unfold traces_prefixclosed_def prefixclosed_def, 
        erule_tac x="es1" in ballE, erule_tac x="es2" in allE, erule impE, auto)
    hence 
      " ((l2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES1\<^esub>)) \<in> Tr\<^bsub>ES1\<^esub> \<Longrightarrow> \<forall> es2. es2 \<preceq> ((l2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES1\<^esub>))
         \<longrightarrow> es2 \<in> Tr\<^bsub>ES1\<^esub>" ..
    with l2l3cattrace have "\<forall> es2. es2 \<preceq> ((l2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES1\<^esub>)) \<longrightarrow> es2 \<in> Tr\<^bsub>ES1\<^esub>" 
      by auto
    hence "(l2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<preceq> ((l2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES1\<^esub>)) \<longrightarrow> (l2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>" ..
    with theprefix have goal51: "(l2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>" 
      by simp
    have l2l3split: "(l2 @ l3) \<upharpoonleft> E\<^bsub>ES2\<^esub> = (l2 \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES2\<^esub>)" 
      by (rule projection_concatenation_commute)
    assume "(l2 @ l3) \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
    with l2l3split have l2l3cattrace: "(l2 \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>" 
      by auto
    have theprefix: "(l2 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<preceq> ((l2 \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES2\<^esub>))" 
      by (simp add: prefix_def)
    have prefixclosure: "\<forall> es1 \<in> Tr\<^bsub>ES2\<^esub>. \<forall>es2. es2 \<preceq> es1 \<longrightarrow> es2 \<in> Tr\<^bsub>ES2\<^esub>" 
      by (clarsimp, insert ES2_traces_prefixclosed, 
        unfold traces_prefixclosed_def prefixclosed_def, 
        erule_tac x="es1" in ballE, erule_tac x="es2" in allE, erule impE, auto)
    hence " ((l2 \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES2\<^esub>)) \<in> Tr\<^bsub>ES2\<^esub> 
      \<Longrightarrow> \<forall> es2. es2 \<preceq> ((l2 \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES2\<^esub>)) \<longrightarrow> es2 \<in> Tr\<^bsub>ES2\<^esub>" ..
    with l2l3cattrace have "\<forall> es2. es2 \<preceq> ((l2 \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES2\<^esub>)) \<longrightarrow> es2 \<in> Tr\<^bsub>ES2\<^esub>" 
      by auto
    hence "(l2 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<preceq> ((l2 \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ (l3 \<upharpoonleft> E\<^bsub>ES2\<^esub>)) \<longrightarrow> (l2 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>" ..
    with theprefix have goal52: "(l2 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>" 
      by simp
    from goal51 goal52 show goal5: "l2 \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub> \<and> l2 \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>" .. 
  qed
qed

end 
