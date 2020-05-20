(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "From regular expressions directly to nondeterministic automata"

theory RegExp2NA
imports "Regular-Sets.Regular_Exp" NA
begin

type_synonym 'a bitsNA = "('a,bool list)na"

definition
"atom"  :: "'a \<Rightarrow> 'a bitsNA" where
"atom a = ([True],
            \<lambda>b s. if s=[True] \<and> b=a then {[False]} else {},
            \<lambda>s. s=[False])"

definition
 or :: "'a bitsNA \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
"or = (\<lambda>(ql,dl,fl)(qr,dr,fr).
   ([],
    \<lambda>a s. case s of
            [] \<Rightarrow> (True ## dl a ql) \<union> (False ## dr a qr)
          | left#s \<Rightarrow> if left then True ## dl a s
                              else False ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> (fl ql | fr qr)
                | left#s \<Rightarrow> if left then fl s else fr s))"

definition
 conc :: "'a bitsNA \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
"conc = (\<lambda>(ql,dl,fl)(qr,dr,fr).
   (True#ql,
    \<lambda>a s. case s of
            [] \<Rightarrow> {}
          | left#s \<Rightarrow> if left then (True ## dl a s) \<union>
                                   (if fl s then False ## dr a qr else {})
                              else False ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> False | left#s \<Rightarrow> left \<and> fl s \<and> fr qr | \<not>left \<and> fr s))"

definition
 epsilon :: "'a bitsNA" where
"epsilon = ([],\<lambda>a s. {}, \<lambda>s. s=[])"

definition
 plus :: "'a bitsNA \<Rightarrow> 'a bitsNA" where
"plus = (\<lambda>(q,d,f). (q, \<lambda>a s. d a s \<union> (if f s then d a q else {}), f))"

definition
 star :: "'a bitsNA \<Rightarrow> 'a bitsNA" where
"star A = or epsilon (plus A)"

primrec rexp2na :: "'a rexp \<Rightarrow> 'a bitsNA" where
"rexp2na Zero       = ([], \<lambda>a s. {}, \<lambda>s. False)" |
"rexp2na One        = epsilon" |
"rexp2na(Atom a)    = atom a" |
"rexp2na(Plus r s)  = or (rexp2na r) (rexp2na s)" |
"rexp2na(Times r s) = conc (rexp2na r) (rexp2na s)" |
"rexp2na(Star r)    = star (rexp2na r)"

declare split_paired_all[simp]

(******************************************************)
(*                       atom                         *)
(******************************************************)

lemma fin_atom: "(fin (atom a) q) = (q = [False])"
by(simp add:atom_def)

lemma start_atom: "start (atom a) = [True]"
by(simp add:atom_def)

lemma in_step_atom_Some[simp]:
 "(p,q) : step (atom a) b = (p=[True] \<and> q=[False] \<and> b=a)"
by (simp add: atom_def step_def)

lemma False_False_in_steps_atom:
 "([False],[False]) : steps (atom a) w = (w = [])"
apply (induct "w")
 apply simp
apply (simp add: relcomp_unfold)
done

lemma start_fin_in_steps_atom:
 "(start (atom a), [False]) : steps (atom a) w = (w = [a])"
apply (induct "w")
 apply (simp add: start_atom)
apply (simp add: False_False_in_steps_atom relcomp_unfold start_atom)
done

lemma accepts_atom:
 "accepts (atom a) w = (w = [a])"
by (simp add: accepts_conv_steps start_fin_in_steps_atom fin_atom)

(******************************************************)
(*                      or                            *)
(******************************************************)

(***** lift True/False over fin *****)

lemma fin_or_True[iff]:
 "\<And>L R. fin (or L R) (True#p) = fin L p"
by(simp add:or_def)

lemma fin_or_False[iff]:
 "\<And>L R. fin (or L R) (False#p) = fin R p"
by(simp add:or_def)

(***** lift True/False over step *****)

lemma True_in_step_or[iff]:
"\<And>L R. (True#p,q) : step (or L R) a = (\<exists>r. q = True#r \<and> (p,r) \<in> step L a)"
apply (simp add:or_def step_def)
apply blast
done

lemma False_in_step_or[iff]:
"\<And>L R. (False#p,q) : step (or L R) a = (\<exists>r. q = False#r \<and> (p,r) \<in> step R a)"
apply (simp add:or_def step_def)
apply blast
done


(***** lift True/False over steps *****)

lemma lift_True_over_steps_or[iff]:
 "\<And>p. (True#p,q)\<in>steps (or L R) w = (\<exists>r. q = True # r \<and> (p,r) \<in> steps L w)"
apply (induct "w")
 apply force
apply force
done

lemma lift_False_over_steps_or[iff]:
 "\<And>p. (False#p,q)\<in>steps (or L R) w = (\<exists>r. q = False#r \<and> (p,r)\<in>steps R w)"
apply (induct "w")
 apply force
apply force
done

(** From the start  **)

lemma start_step_or[iff]:
 "\<And>L R. (start(or L R),q) : step(or L R) a = 
         (\<exists>p. (q = True#p \<and> (start L,p) : step L a) | 
               (q = False#p \<and> (start R,p) : step R a))"
apply (simp add:or_def step_def)
apply blast
done

lemma steps_or:
 "(start(or L R), q) : steps (or L R) w = 
  ( (w = [] \<and> q = start(or L R)) | 
    (w \<noteq> [] \<and> (\<exists>p.  q = True  # p \<and> (start L,p) : steps L w | 
                      q = False # p \<and> (start R,p) : steps R w)))"
apply (case_tac "w")
 apply (simp)
 apply blast
apply (simp)
apply blast
done

lemma fin_start_or[iff]:
 "\<And>L R. fin (or L R) (start(or L R)) = (fin L (start L) | fin R (start R))"
by (simp add:or_def)

lemma accepts_or[iff]:
 "accepts (or L R) w = (accepts L w | accepts R w)"
apply (simp add: accepts_conv_steps steps_or)
(* get rid of case_tac: *)
apply (case_tac "w = []")
 apply auto
done

(******************************************************)
(*                      conc                        *)
(******************************************************)

(** True/False in fin **)

lemma fin_conc_True[iff]:
 "\<And>L R. fin (conc L R) (True#p) = (fin L p \<and> fin R (start R))"
by(simp add:conc_def)

lemma fin_conc_False[iff]:
 "\<And>L R. fin (conc L R) (False#p) = fin R p"
by(simp add:conc_def)


(** True/False in step **)

lemma True_step_conc[iff]:
 "\<And>L R. (True#p,q) : step (conc L R) a = 
        ((\<exists>r. q=True#r \<and> (p,r): step L a) | 
         (fin L p \<and> (\<exists>r. q=False#r \<and> (start R,r) : step R a)))"
apply (simp add:conc_def step_def)
apply blast
done

lemma False_step_conc[iff]:
 "\<And>L R. (False#p,q) : step (conc L R) a = 
       (\<exists>r. q = False#r \<and> (p,r) : step R a)"
apply (simp add:conc_def step_def)
apply blast
done

(** False in steps **)

lemma False_steps_conc[iff]:
 "\<And>p. (False#p,q): steps (conc L R) w = (\<exists>r. q=False#r \<and> (p,r): steps R w)"
apply (induct "w")
 apply fastforce
apply force
done

(** True in steps **)

lemma True_True_steps_concI:
 "\<And>L R p. (p,q) : steps L w \<Longrightarrow> (True#p,True#q) : steps (conc L R) w"
apply (induct "w")
 apply simp
apply simp
apply fast
done

lemma True_False_step_conc[iff]:
 "\<And>L R. (True#p,False#q) : step (conc L R) a = 
         (fin L p \<and> (start R,q) : step R a)"
by simp

lemma True_steps_concD[rule_format]:
 "\<forall>p. (True#p,q) : steps (conc L R) w \<longrightarrow> 
     ((\<exists>r. (p,r) : steps L w \<and> q = True#r)  \<or> 
  (\<exists>u a v. w = u@a#v \<and> 
            (\<exists>r. (p,r) : steps L u \<and> fin L r \<and> 
            (\<exists>s. (start R,s) : step R a \<and> 
            (\<exists>t. (s,t) : steps R v \<and> q = False#t)))))"
apply (induct "w")
 apply simp
apply simp
apply (clarify del:disjCI)
apply (erule disjE)
 apply (clarify del:disjCI)
 apply (erule allE, erule impE, assumption)
 apply (erule disjE)
  apply blast
 apply (rule disjI2)
 apply (clarify)
 apply simp
 apply (rule_tac x = "a#u" in exI)
 apply simp
 apply blast
apply (rule disjI2)
apply (clarify)
apply simp
apply (rule_tac x = "[]" in exI)
apply simp
apply blast
done

lemma True_steps_conc:
 "(True#p,q) : steps (conc L R) w = 
 ((\<exists>r. (p,r) : steps L w \<and> q = True#r)  \<or>
  (\<exists>u a v. w = u@a#v \<and>
            (\<exists>r. (p,r) : steps L u \<and> fin L r \<and> 
            (\<exists>s. (start R,s) : step R a \<and> 
            (\<exists>t. (s,t) : steps R v \<and> q = False#t)))))"
by(force dest!: True_steps_concD intro!: True_True_steps_concI)

(** starting from the start **)

lemma start_conc:
  "\<And>L R. start(conc L R) = True#start L"
by (simp add:conc_def)

lemma final_conc:
 "\<And>L R. fin(conc L R) p = ((fin R (start R) \<and> (\<exists>s. p = True#s \<and> fin L s)) \<or>
                           (\<exists>s. p = False#s \<and> fin R s))"
apply (simp add:conc_def split: list.split)
apply blast
done

lemma accepts_conc:
 "accepts (conc L R) w = (\<exists>u v. w = u@v \<and> accepts L u \<and> accepts R v)"
apply (simp add: accepts_conv_steps True_steps_conc final_conc start_conc)
apply (rule iffI)
 apply (clarify)
 apply (erule disjE)
  apply (clarify)
  apply (erule disjE)
   apply (rule_tac x = "w" in exI)
   apply simp
   apply blast
  apply blast
 apply (erule disjE)
  apply blast
 apply (clarify)
 apply (rule_tac x = "u" in exI)
 apply simp
 apply blast
apply (clarify)
apply (case_tac "v")
 apply simp
 apply blast
apply simp
apply blast
done

(******************************************************)
(*                     epsilon                        *)
(******************************************************)

lemma step_epsilon[simp]: "step epsilon a = {}"
by(simp add:epsilon_def step_def)

lemma steps_epsilon: "((p,q) : steps epsilon w) = (w=[] \<and> p=q)"
by (induct "w") auto

lemma accepts_epsilon[iff]: "accepts epsilon w = (w = [])"
apply (simp add: steps_epsilon accepts_conv_steps)
apply (simp add: epsilon_def)
done

(******************************************************)
(*                       plus                         *)
(******************************************************)

lemma start_plus[simp]: "\<And>A. start (plus A) = start A"
by(simp add:plus_def)

lemma fin_plus[iff]: "\<And>A. fin (plus A) = fin A"
by(simp add:plus_def)

lemma step_plusI:
  "\<And>A. (p,q) : step A a \<Longrightarrow> (p,q) : step (plus A) a"
by(simp add:plus_def step_def)

lemma steps_plusI: "\<And>p. (p,q) : steps A w \<Longrightarrow> (p,q) \<in> steps (plus A) w"
apply (induct "w")
 apply simp
apply simp
apply (blast intro: step_plusI)
done

lemma step_plus_conv[iff]:
 "\<And>A. (p,r): step (plus A) a = 
       ( (p,r): step A a | fin A p \<and> (start A,r) : step A a )"
by(simp add:plus_def step_def)

lemma fin_steps_plusI:
 "[| (start A,q) : steps A u; u \<noteq> []; fin A p |] 
 ==> (p,q) : steps (plus A) u"
apply (case_tac "u")
 apply blast
apply simp
apply (blast intro: steps_plusI)
done

(* reverse list induction! Complicates matters for conc? *)
lemma start_steps_plusD[rule_format]:
 "\<forall>r. (start A,r) \<in> steps (plus A) w \<longrightarrow>
     (\<exists>us v. w = concat us @ v \<and> 
              (\<forall>u\<in>set us. accepts A u) \<and> 
              (start A,r) \<in> steps A v)"
apply (induct w rule: rev_induct)
 apply simp
 apply (rule_tac x = "[]" in exI)
 apply simp
apply simp
apply (clarify)
apply (erule allE, erule impE, assumption)
apply (clarify)
apply (erule disjE)
 apply (rule_tac x = "us" in exI)
 apply (simp)
 apply blast
apply (rule_tac x = "us@[v]" in exI)
apply (simp add: accepts_conv_steps)
apply blast
done

lemma steps_star_cycle[rule_format]:
 "us \<noteq> [] \<longrightarrow> (\<forall>u \<in> set us. accepts A u) \<longrightarrow> accepts (plus A) (concat us)"
apply (simp add: accepts_conv_steps)
apply (induct us rule: rev_induct)
 apply simp
apply (rename_tac u us)
apply simp
apply (clarify)
apply (case_tac "us = []")
 apply (simp)
 apply (blast intro: steps_plusI fin_steps_plusI)
apply (clarify)
apply (case_tac "u = []")
 apply (simp)
 apply (blast intro: steps_plusI fin_steps_plusI)
apply (blast intro: steps_plusI fin_steps_plusI)
done

lemma accepts_plus[iff]:
 "accepts (plus A) w = 
 (\<exists>us. us \<noteq> [] \<and> w = concat us \<and> (\<forall>u \<in> set us. accepts A u))"
apply (rule iffI)
 apply (simp add: accepts_conv_steps)
 apply (clarify)
 apply (drule start_steps_plusD)
 apply (clarify)
 apply (rule_tac x = "us@[v]" in exI)
 apply (simp add: accepts_conv_steps)
 apply blast
apply (blast intro: steps_star_cycle)
done

(******************************************************)
(*                       star                         *)
(******************************************************)

lemma accepts_star:
 "accepts (star A) w = (\<exists>us. (\<forall>u \<in> set us. accepts A u) \<and> w = concat us)"
apply(unfold star_def)
apply (rule iffI)
 apply (clarify)
 apply (erule disjE)
  apply (rule_tac x = "[]" in exI)
  apply simp
 apply blast
apply force
done

(***** Correctness of r2n *****)

lemma accepts_rexp2na:
 "\<And>w. accepts (rexp2na r) w = (w : lang r)"
apply (induct "r")
     apply (simp add: accepts_conv_steps)
    apply simp
   apply (simp add: accepts_atom)
  apply (simp)
 apply (simp add: accepts_conc Regular_Set.conc_def)
apply (simp add: accepts_star in_star_iff_concat subset_iff Ball_def)
done

end
