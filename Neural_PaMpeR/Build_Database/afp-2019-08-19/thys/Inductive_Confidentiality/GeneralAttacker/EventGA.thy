section\<open>Theory of Events for Security Protocols against the General Attacker\<close>

theory EventGA imports MessageGA begin

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: "agent => msg set"

datatype
  event = Says  agent agent msg
        | Gets  agent       msg
        | Notes agent       msg
       
primrec knows  :: "agent => event list => msg set" where
   knows_Nil:   "knows A [] = initState A"
 | knows_Cons:
    "knows A (ev # evs) =
        (case ev of
           Says A' B X \<Rightarrow> insert X (knows A evs)
         | Gets A' X   \<Rightarrow> knows A evs
         | Notes A' X  \<Rightarrow> 
             if A'=A then insert X (knows A evs) else knows A evs)"

primrec
  (*Set of items that might be visible to somebody:
    complement of the set of fresh items*)
 used :: "event list => msg set" where
   used_Nil:   "used []         = (UN B. parts (initState B))"
 | used_Cons:  "used (ev # evs) =
                     (case ev of
                        Says A B X => parts {X} \<union> used evs
                      | Gets A X   => used evs
                      | Notes A X  => parts {X} \<union> used evs)"
    \<comment> \<open>The case for @{term Gets} seems anomalous, but @{term Gets} always
        follows @{term Says} in real protocols.  Seems difficult to change.
        See @{text Gets_correct} in theory @{text "Guard/Extensions.thy"}.\<close>

lemma Notes_imp_used [rule_format]: "Notes A X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done

lemma Says_imp_used [rule_format]: "Says A B X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done


subsection\<open>Function @{term knows}\<close>

lemmas parts_insert_knows_A = parts_insert [of _ "knows A evs"] for A evs

lemma knows_Says [simp]:
     "knows A (Says A' B X # evs) = insert X (knows A evs)"
by simp

lemma knows_Notes [simp]:
     "knows A (Notes A' X # evs) =  
          (if A=A' then insert X (knows A evs) else knows A evs)"
by simp

lemma knows_Gets [simp]: "knows A (Gets A' X # evs) = knows A evs"
by simp

text\<open>Everybody sees what is sent on the traffic\<close>
lemma Says_imp_knows [rule_format]:
     "Says A' B X \<in> set evs \<longrightarrow> (\<forall>A. X \<in> knows A evs)"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply auto
done

lemma Notes_imp_knows [rule_format]:
"Notes A' X \<in> set evs \<longrightarrow> X \<in> knows A' evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
done


text\<open>Elimination rules: derive contradictions from old Says events containing
  items known to be fresh\<close>
lemmas Says_imp_parts_knows = 
       Says_imp_knows [THEN parts.Inj, THEN revcut_rl] 

lemmas knows_partsEs =
     Says_imp_parts_knows parts.Body [THEN revcut_rl]

lemmas Says_imp_analz = Says_imp_knows [THEN analz.Inj]


subsection\<open>Knowledge of generic agents\<close>

lemma knows_subset_knows_Says: "knows A evs \<subseteq> knows A (Says A' B X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Notes: "knows A evs \<subseteq> knows A (Notes A' X # evs)"
by (simp add: subset_insertI)

lemma knows_subset_knows_Gets: "knows A evs \<subseteq> knows A (Gets A' X # evs)"
by (simp add: subset_insertI)

lemma knows_imp_Says_Gets_Notes_initState [rule_format]:
     "X \<in> knows A evs \<Longrightarrow> \<exists>A' B.  
  Says A' B X \<in> set evs \<or> Notes A X \<in> set evs \<or> X \<in> initState A"
apply (erule rev_mp)
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) split: event.split)
apply auto
done

lemma parts_knows_subset_used: "parts (knows A evs) \<subseteq> used evs"
apply (induct_tac "evs", force)  
apply (simp add: parts_insert_knows_A add: event.split, blast) 
done

lemmas usedI = parts_knows_subset_used [THEN subsetD, intro]

lemma initState_into_used: "X \<in> parts (initState B) \<Longrightarrow> X \<in> used evs"
apply (induct_tac "evs")
apply (simp_all add: parts_insert_knows_A split: event.split, blast)
done

lemma used_Says [simp]: "used (Says A B X # evs) = parts{X} \<union> used evs"
by simp

lemma used_Notes [simp]: "used (Notes A X # evs) = parts{X} \<union> used evs"
by simp

lemma used_Gets [simp]: "used (Gets A X # evs) = used evs"
by simp

lemma used_nil_subset: "used [] \<subseteq> used evs"
apply simp
apply (blast intro: initState_into_used)
done

text\<open>NOTE REMOVAL--laws above are cleaner, as they don't involve "case"\<close>
declare knows_Cons [simp del]
        used_Nil [simp del] used_Cons [simp del]


lemmas analz_mono_contra =
       knows_subset_knows_Says [THEN analz_mono, THEN contra_subsetD]
       knows_subset_knows_Notes [THEN analz_mono, THEN contra_subsetD]
       knows_subset_knows_Gets [THEN analz_mono, THEN contra_subsetD]


lemma knows_subset_knows_Cons: "knows A evs \<subseteq> knows A (e # evs)"
by (induct e, auto simp: knows_Cons)

lemma initState_subset_knows: "initState A \<subseteq> knows A evs"
apply (induct_tac evs, simp) 
apply (blast intro: knows_subset_knows_Cons [THEN subsetD])
done


text\<open>For proving \<open>new_keys_not_used\<close>\<close>
lemma keysFor_parts_insert:
     "[| K \<in> keysFor (parts (insert X G));  X \<in> synth (analz H) |] 
      ==> K \<in> keysFor (parts (G \<union> H)) | Key (invKey K) \<in> parts H" 
by (force 
    dest!: parts_insert_subset_Un [THEN keysFor_mono, THEN [2] rev_subsetD]
           analz_subset_parts [THEN keysFor_mono, THEN [2] rev_subsetD]
    intro: analz_subset_parts [THEN subsetD] parts_mono [THEN [2] rev_subsetD])


lemmas analz_impI = impI [where P = "Y \<notin> analz (knows A evs)"] for Y A evs

ML
\<open>
fun analz_mono_contra_tac ctxt =
  resolve_tac ctxt @{thms analz_impI} THEN' 
  REPEAT1 o (dresolve_tac ctxt @{thms analz_mono_contra})
  THEN' mp_tac ctxt
\<close>

method_setup analz_mono_contra = \<open>
    Scan.succeed (fn ctxt => SIMPLE_METHOD (REPEAT_FIRST (analz_mono_contra_tac ctxt)))\<close>
    "for proving theorems of the form X \<notin> analz (knows A evs) \<longrightarrow> P"

text\<open>Useful for case analysis on whether a hash is a spoof or not\<close>

lemmas syan_impI = impI [where P = "Y \<notin> synth (analz (knows A evs))"] for Y A evs

ML
\<open>
fun synth_analz_mono_contra_tac ctxt =
  resolve_tac ctxt @{thms syan_impI} THEN'
  REPEAT1 o 
    (dresolve_tac ctxt 
     [@{thm knows_subset_knows_Says} RS @{thm synth_analz_mono} RS @{thm contra_subsetD},
      @{thm knows_subset_knows_Notes} RS @{thm synth_analz_mono} RS @{thm contra_subsetD},
      @{thm knows_subset_knows_Gets} RS @{thm synth_analz_mono} RS @{thm contra_subsetD}])
  THEN'
  mp_tac ctxt
\<close>

method_setup synth_analz_mono_contra = \<open>
    Scan.succeed (fn ctxt => SIMPLE_METHOD (REPEAT_FIRST (synth_analz_mono_contra_tac ctxt)))\<close>
    "for proving theorems of the form X \<notin> synth (analz (knows A evs)) \<longrightarrow> P"

end
