(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "From regular expressions to nondeterministic automata with epsilon"

theory RegExp2NAe
imports "Regular-Sets.Regular_Exp" NAe
begin

type_synonym 'a bitsNAe = "('a,bool list)nae"

definition
 epsilon :: "'a bitsNAe" where
"epsilon = ([],\<lambda>a s. {}, \<lambda>s. s=[])"

definition
"atom"  :: "'a \<Rightarrow> 'a bitsNAe" where
"atom a = ([True],
            \<lambda>b s. if s=[True] \<and> b=Some a then {[False]} else {},
            \<lambda>s. s=[False])"

definition
 or :: "'a bitsNAe \<Rightarrow> 'a bitsNAe \<Rightarrow> 'a bitsNAe" where
"or = (\<lambda>(ql,dl,fl)(qr,dr,fr).
   ([],
    \<lambda>a s. case s of
            [] \<Rightarrow> if a=None then {True#ql,False#qr} else {}
          | left#s \<Rightarrow> if left then True ## dl a s
                              else False ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> False | left#s \<Rightarrow> if left then fl s else fr s))"

definition
 conc :: "'a bitsNAe \<Rightarrow> 'a bitsNAe \<Rightarrow> 'a bitsNAe" where
"conc = (\<lambda>(ql,dl,fl)(qr,dr,fr).
   (True#ql,
    \<lambda>a s. case s of
            [] \<Rightarrow> {}
          | left#s \<Rightarrow> if left then (True ## dl a s) \<union>
                                   (if fl s \<and> a=None then {False#qr} else {})
                              else False ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> False | left#s \<Rightarrow> \<not>left \<and> fr s))"

definition
 star :: "'a bitsNAe \<Rightarrow> 'a bitsNAe" where
"star = (\<lambda>(q,d,f).
   ([],
    \<lambda>a s. case s of
            [] \<Rightarrow> if a=None then {True#q} else {}
          | left#s \<Rightarrow> if left then (True ## d a s) \<union>
                                   (if f s \<and> a=None then {True#q} else {})
                              else {},
    \<lambda>s. case s of [] \<Rightarrow> True | left#s \<Rightarrow> left \<and> f s))"

primrec rexp2nae :: "'a rexp \<Rightarrow> 'a bitsNAe" where
"rexp2nae Zero       = ([], \<lambda>a s. {}, \<lambda>s. False)" |
"rexp2nae One        = epsilon" |
"rexp2nae(Atom a)    = atom a" |
"rexp2nae(Plus r s)  = or   (rexp2nae r) (rexp2nae s)" |
"rexp2nae(Times r s) = conc (rexp2nae r) (rexp2nae s)" |
"rexp2nae(Star r)    = star (rexp2nae r)"

declare split_paired_all[simp]

(******************************************************)
(*                     epsilon                        *)
(******************************************************)

lemma step_epsilon[simp]: "step epsilon a = {}"
by(simp add:epsilon_def step_def)

lemma steps_epsilon: "((p,q) : steps epsilon w) = (w=[] \<and> p=q)"
by (induct "w") auto

lemma accepts_epsilon[simp]: "accepts epsilon w = (w = [])"
apply (simp add: steps_epsilon accepts_def)
apply (simp add: epsilon_def)
done

(******************************************************)
(*                       atom                         *)
(******************************************************)

lemma fin_atom: "(fin (atom a) q) = (q = [False])"
by(simp add:atom_def)

lemma start_atom: "start (atom a) = [True]"
by(simp add:atom_def)

(* Use {x. False} = {}? *)

lemma eps_atom[simp]:
 "eps(atom a) = {}"
by (simp add:atom_def step_def)

lemma in_step_atom_Some[simp]:
 "(p,q) : step (atom a) (Some b) = (p=[True] \<and> q=[False] \<and> b=a)"
by (simp add:atom_def step_def)

lemma False_False_in_steps_atom:
  "([False],[False]) : steps (atom a) w = (w = [])"
apply (induct "w")
 apply (simp)
apply (simp add: relcomp_unfold)
done

lemma start_fin_in_steps_atom:
  "(start (atom a), [False]) : steps (atom a) w = (w = [a])"
apply (induct "w")
 apply (simp add: start_atom rtrancl_empty)
apply (simp add: False_False_in_steps_atom relcomp_unfold start_atom)
done

lemma accepts_atom: "accepts (atom a) w = (w = [a])"
by (simp add: accepts_def start_fin_in_steps_atom fin_atom)


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
"\<And>L R. (True#p,q) : step (or L R) a = (\<exists>r. q = True#r \<and> (p,r) : step L a)"
apply (simp add:or_def step_def)
apply blast
done

lemma False_in_step_or[iff]:
"\<And>L R. (False#p,q) : step (or L R) a = (\<exists>r. q = False#r \<and> (p,r) : step R a)"
apply (simp add:or_def step_def)
apply blast
done


(***** lift True/False over epsclosure *****)

lemma lemma1a:
 "(tp,tq) : (eps(or L R))\<^sup>* \<Longrightarrow> 
 (\<And>p. tp = True#p \<Longrightarrow> \<exists>q. (p,q) : (eps L)\<^sup>* \<and> tq = True#q)"
apply (induct rule:rtrancl_induct)
 apply (blast)
apply (clarify)
apply (simp)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma lemma1b:
 "(tp,tq) : (eps(or L R))\<^sup>* \<Longrightarrow> 
 (\<And>p. tp = False#p \<Longrightarrow> \<exists>q. (p,q) : (eps R)\<^sup>* \<and> tq = False#q)"
apply (induct rule:rtrancl_induct)
 apply (blast)
apply (clarify)
apply (simp)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma lemma2a:
 "(p,q) : (eps L)\<^sup>*  \<Longrightarrow> (True#p, True#q) : (eps(or L R))\<^sup>*"
apply (induct rule: rtrancl_induct)
 apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma lemma2b:
 "(p,q) : (eps R)\<^sup>*  \<Longrightarrow> (False#p, False#q) : (eps(or L R))\<^sup>*"
apply (induct rule: rtrancl_induct)
 apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma True_epsclosure_or[iff]:
 "(True#p,q) : (eps(or L R))\<^sup>* = (\<exists>r. q = True#r \<and> (p,r) : (eps L)\<^sup>*)"
by (blast dest: lemma1a lemma2a)

lemma False_epsclosure_or[iff]:
 "(False#p,q) : (eps(or L R))\<^sup>* = (\<exists>r. q = False#r \<and> (p,r) : (eps R)\<^sup>*)"
by (blast dest: lemma1b lemma2b)

(***** lift True/False over steps *****)

lemma lift_True_over_steps_or[iff]:
 "\<And>p. (True#p,q):steps (or L R) w = (\<exists>r. q = True # r \<and> (p,r):steps L w)"
apply (induct "w")
 apply auto
apply force
done

lemma lift_False_over_steps_or[iff]:
 "\<And>p. (False#p,q):steps (or L R) w = (\<exists>r. q = False#r \<and> (p,r):steps R w)"
apply (induct "w")
 apply auto
apply (force)
done

(***** Epsilon closure of start state *****)

lemma unfold_rtrancl2:
 "R\<^sup>* = Id \<union> (R O R\<^sup>*)"
apply (rule set_eqI)
apply (simp)
apply (rule iffI)
 apply (erule rtrancl_induct)
  apply (blast)
 apply (blast intro: rtrancl_into_rtrancl)
apply (blast intro: converse_rtrancl_into_rtrancl)
done

lemma in_unfold_rtrancl2:
 "(p,q) : R\<^sup>* = (q = p | (\<exists>r. (p,r) : R \<and> (r,q) : R\<^sup>*))"
apply (rule unfold_rtrancl2[THEN equalityE])
apply (blast)
done

lemmas [iff] = in_unfold_rtrancl2[where ?p = "start(or L R)"] for L R

lemma start_eps_or[iff]:
 "\<And>L R. (start(or L R),q) : eps(or L R) = 
       (q = True#start L | q = False#start R)"
by (simp add:or_def step_def)

lemma not_start_step_or_Some[iff]:
 "\<And>L R. (start(or L R),q) \<notin> step (or L R) (Some a)"
by (simp add:or_def step_def)

lemma steps_or:
 "(start(or L R), q) : steps (or L R) w = 
 ( (w = [] \<and> q = start(or L R)) | 
   (\<exists>p.  q = True  # p \<and> (start L,p) : steps L w | 
         q = False # p \<and> (start R,p) : steps R w) )"
apply (case_tac "w")
 apply (simp)
 apply (blast)
apply (simp)
apply (blast)
done

lemma start_or_not_final[iff]:
 "\<And>L R. \<not> fin (or L R) (start(or L R))"
by (simp add:or_def)

lemma accepts_or:
 "accepts (or L R) w = (accepts L w | accepts R w)"
apply (simp add:accepts_def steps_or)
 apply auto
done


(******************************************************)
(*                      conc                          *)
(******************************************************)

(** True/False in fin **)

lemma in_conc_True[iff]:
 "\<And>L R. fin (conc L R) (True#p) = False"
by (simp add:conc_def)

lemma fin_conc_False[iff]:
 "\<And>L R. fin (conc L R) (False#p) = fin R p"
by (simp add:conc_def)

(** True/False in step **)

lemma True_step_conc[iff]:
 "\<And>L R. (True#p,q) : step (conc L R) a = 
       ((\<exists>r. q=True#r \<and> (p,r): step L a) | 
        (fin L p \<and> a=None \<and> q=False#start R))"
by (simp add:conc_def step_def) (blast)

lemma False_step_conc[iff]:
 "\<And>L R. (False#p,q) : step (conc L R) a = 
       (\<exists>r. q = False#r \<and> (p,r) : step R a)"
by (simp add:conc_def step_def) (blast)

(** False in epsclosure **)

lemma lemma1b':
 "(tp,tq) : (eps(conc L R))\<^sup>* \<Longrightarrow> 
  (\<And>p. tp = False#p \<Longrightarrow> \<exists>q. (p,q) : (eps R)\<^sup>* \<and> tq = False#q)"
apply (induct rule: rtrancl_induct)
 apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma lemma2b':
 "(p,q) : (eps R)\<^sup>* \<Longrightarrow> (False#p, False#q) : (eps(conc L R))\<^sup>*"
apply (induct rule: rtrancl_induct)
 apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma False_epsclosure_conc[iff]:
 "((False # p, q) : (eps (conc L R))\<^sup>*) = 
 (\<exists>r. q = False # r \<and> (p, r) : (eps R)\<^sup>*)"
apply (rule iffI)
 apply (blast dest: lemma1b')
apply (blast dest: lemma2b')
done

(** False in steps **)

lemma False_steps_conc[iff]:
 "\<And>p. (False#p,q): steps (conc L R) w = (\<exists>r. q=False#r \<and> (p,r): steps R w)"
apply (induct "w")
 apply (simp)
apply (simp)
apply (fast)  (*MUCH faster than blast*)
done

(** True in epsclosure **)

lemma True_True_eps_concI:
 "(p,q): (eps L)\<^sup>* \<Longrightarrow> (True#p,True#q) : (eps(conc L R))\<^sup>*"
apply (induct rule: rtrancl_induct)
 apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma True_True_steps_concI:
 "\<And>p. (p,q) : steps L w \<Longrightarrow> (True#p,True#q) : steps (conc L R) w"
apply (induct "w")
 apply (simp add: True_True_eps_concI)
apply (simp)
apply (blast intro: True_True_eps_concI)
done

lemma lemma1a':
 "(tp,tq) : (eps(conc L R))\<^sup>* \<Longrightarrow> 
 (\<And>p. tp = True#p \<Longrightarrow> 
  (\<exists>q. tq = True#q \<and> (p,q) : (eps L)\<^sup>*) | 
  (\<exists>q r. tq = False#q \<and> (p,r):(eps L)\<^sup>* \<and> fin L r \<and> (start R,q) : (eps R)\<^sup>*))"
apply (induct rule: rtrancl_induct)
 apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma lemma2a':
 "(p, q) : (eps L)\<^sup>* \<Longrightarrow> (True#p, True#q) : (eps(conc L R))\<^sup>*"
apply (induct rule: rtrancl_induct)
 apply (blast)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma lem:
 "\<And>L R. (p,q) : step R None \<Longrightarrow> (False#p, False#q) : step (conc L R) None"
by(simp add: conc_def step_def)

lemma lemma2b'':
 "(p,q) : (eps R)\<^sup>* \<Longrightarrow> (False#p, False#q) : (eps(conc L R))\<^sup>*"
apply (induct rule: rtrancl_induct)
 apply (blast)
apply (drule lem)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma True_False_eps_concI:
 "\<And>L R. fin L p \<Longrightarrow> (True#p, False#start R) : eps(conc L R)"
by(simp add: conc_def step_def)

lemma True_epsclosure_conc[iff]:
 "((True#p,q) \<in> (eps(conc L R))\<^sup>*) = 
 ((\<exists>r. (p,r) \<in> (eps L)\<^sup>* \<and> q = True#r) \<or>
  (\<exists>r. (p,r) \<in> (eps L)\<^sup>* \<and> fin L r \<and>
        (\<exists>s. (start R, s) \<in> (eps R)\<^sup>* \<and> q = False#s)))"
apply (rule iffI)
 apply (blast dest: lemma1a')
apply (erule disjE)
 apply (blast intro: lemma2a')
apply (clarify)
apply (rule rtrancl_trans)
apply (erule lemma2a')
apply (rule converse_rtrancl_into_rtrancl)
apply (erule True_False_eps_concI)
apply (erule lemma2b'')
done

(** True in steps **)

lemma True_steps_concD[rule_format]:
 "\<forall>p. (True#p,q) : steps (conc L R) w \<longrightarrow> 
     ((\<exists>r. (p,r) : steps L w \<and> q = True#r)  \<or>
      (\<exists>u v. w = u@v \<and> (\<exists>r. (p,r) \<in> steps L u \<and> fin L r \<and>
              (\<exists>s. (start R,s) \<in> steps R v \<and> q = False#s))))"
apply (induct "w")
 apply (simp)
apply (simp)
apply (clarify del: disjCI)
 apply (erule disjE)
 apply (clarify del: disjCI)
 apply (erule disjE)
  apply (clarify del: disjCI)
  apply (erule allE, erule impE, assumption)
  apply (erule disjE)
   apply (blast)
  apply (rule disjI2)
  apply (clarify)
  apply (simp)
  apply (rule_tac x = "a#u" in exI)
  apply (simp)
  apply (blast)
 apply (blast)
apply (rule disjI2)
apply (clarify)
apply (simp)
apply (rule_tac x = "[]" in exI)
apply (simp)
apply (blast)
done

lemma True_steps_conc:
 "(True#p,q) \<in> steps (conc L R) w = 
 ((\<exists>r. (p,r) \<in> steps L w \<and> q = True#r)  | 
  (\<exists>u v. w = u@v \<and> (\<exists>r. (p,r) : steps L u \<and> fin L r \<and> 
          (\<exists>s. (start R,s) : steps R v \<and> q = False#s))))"
by (blast dest: True_steps_concD
    intro: True_True_steps_concI in_steps_epsclosure)

(** starting from the start **)

lemma start_conc:
  "\<And>L R. start(conc L R) = True#start L"
by (simp add: conc_def)

lemma final_conc:
 "\<And>L R. fin(conc L R) p = (\<exists>s. p = False#s \<and> fin R s)"
by (simp add:conc_def split: list.split)

lemma accepts_conc:
 "accepts (conc L R) w = (\<exists>u v. w = u@v \<and> accepts L u \<and> accepts R v)"
apply (simp add: accepts_def True_steps_conc final_conc start_conc)
apply (blast)
done

(******************************************************)
(*                       star                         *)
(******************************************************)

lemma True_in_eps_star[iff]:
 "\<And>A. (True#p,q) \<in> eps(star A) = 
     ( (\<exists>r. q = True#r \<and> (p,r) \<in> eps A) \<or> (fin A p \<and> q = True#start A) )"
by (simp add:star_def step_def) (blast)

lemma True_True_step_starI:
  "\<And>A. (p,q) : step A a \<Longrightarrow> (True#p, True#q) : step (star A) a"
by (simp add:star_def step_def)

lemma True_True_eps_starI:
  "(p,r) : (eps A)\<^sup>* \<Longrightarrow> (True#p, True#r) : (eps(star A))\<^sup>*"
apply (induct rule: rtrancl_induct)
 apply (blast)
apply (blast intro: True_True_step_starI rtrancl_into_rtrancl)
done

lemma True_start_eps_starI:
 "\<And>A. fin A p \<Longrightarrow> (True#p,True#start A) : eps(star A)"
by (simp add:star_def step_def)

lemma lem':
 "(tp,s) : (eps(star A))\<^sup>* \<Longrightarrow> (\<forall>p. tp = True#p \<longrightarrow>
 (\<exists>r. ((p,r) \<in> (eps A)\<^sup>* \<or>
        (\<exists>q. (p,q) \<in> (eps A)\<^sup>* \<and> fin A q \<and> (start A,r) : (eps A)\<^sup>*)) \<and> 
       s = True#r))"
apply (induct rule: rtrancl_induct)
 apply (simp)
apply (clarify)
apply (simp)
apply (blast intro: rtrancl_into_rtrancl)
done

lemma True_eps_star[iff]:
 "((True#p,s) \<in> (eps(star A))\<^sup>*) = 
 (\<exists>r. ((p,r) \<in> (eps A)\<^sup>* \<or>
        (\<exists>q. (p,q) : (eps A)\<^sup>* \<and> fin A q \<and> (start A,r) : (eps A)\<^sup>*)) \<and>
       s = True#r)"
apply (rule iffI)
 apply (drule lem')
 apply (blast)
(* Why can't blast do the rest? *)
apply (clarify)
apply (erule disjE)
apply (erule True_True_eps_starI)
apply (clarify)
apply (rule rtrancl_trans)
apply (erule True_True_eps_starI)
apply (rule rtrancl_trans)
apply (rule r_into_rtrancl)
apply (erule True_start_eps_starI)
apply (erule True_True_eps_starI)
done

(** True in step Some **)

lemma True_step_star[iff]:
 "\<And>A. (True#p,r) \<in> step (star A) (Some a) =
     (\<exists>q. (p,q) \<in> step A (Some a) \<and> r=True#q)"
by (simp add:star_def step_def) (blast)


(** True in steps **)

(* reverse list induction! Complicates matters for conc? *)
lemma True_start_steps_starD[rule_format]:
 "\<forall>rr. (True#start A,rr) \<in> steps (star A) w \<longrightarrow>
 (\<exists>us v. w = concat us @ v \<and>
             (\<forall>u\<in>set us. accepts A u) \<and>
             (\<exists>r. (start A,r) \<in> steps A v \<and> rr = True#r))"
apply (induct w rule: rev_induct)
 apply (simp)
 apply (clarify)
 apply (rule_tac x = "[]" in exI)
 apply (erule disjE)
  apply (simp)
 apply (clarify)
 apply (simp)
apply (simp add: O_assoc[symmetric] epsclosure_steps)
apply (clarify)
apply (erule allE, erule impE, assumption)
apply (clarify)
apply (erule disjE)
 apply (rule_tac x = "us" in exI)
 apply (rule_tac x = "v@[x]" in exI)
 apply (simp add: O_assoc[symmetric] epsclosure_steps)
 apply (blast)
apply (clarify)
apply (rule_tac x = "us@[v@[x]]" in exI)
apply (rule_tac x = "[]" in exI)
apply (simp add: accepts_def)
apply (blast)
done

lemma True_True_steps_starI:
  "\<And>p. (p,q) : steps A w \<Longrightarrow> (True#p,True#q) : steps (star A) w"
apply (induct "w")
 apply (simp)
apply (simp)
apply (blast intro: True_True_eps_starI True_True_step_starI)
done

lemma steps_star_cycle:
 "(\<forall>u \<in> set us. accepts A u) \<Longrightarrow>
 (True#start A,True#start A) \<in> steps (star A) (concat us)"
apply (induct "us")
 apply (simp add:accepts_def)
apply (simp add:accepts_def)
by(blast intro: True_True_steps_starI True_start_eps_starI in_epsclosure_steps)

(* Better stated directly with start(star A)? Loop in star A back to start(star A)?*)
lemma True_start_steps_star:
 "(True#start A,rr) : steps (star A) w = 
 (\<exists>us v. w = concat us @ v \<and>
             (\<forall>u\<in>set us. accepts A u) \<and>
             (\<exists>r. (start A,r) \<in> steps A v \<and> rr = True#r))"
apply (rule iffI)
 apply (erule True_start_steps_starD)
apply (clarify)
apply (blast intro: steps_star_cycle True_True_steps_starI)
done

(** the start state **)

lemma start_step_star[iff]:
  "\<And>A. (start(star A),r) : step (star A) a = (a=None \<and> r = True#start A)"
by (simp add:star_def step_def)

lemmas epsclosure_start_step_star =
  in_unfold_rtrancl2[where ?p = "start (star A)"] for A

lemma start_steps_star:
 "(start(star A),r) : steps (star A) w = 
 ((w=[] \<and> r= start(star A)) | (True#start A,r) : steps (star A) w)"
apply (rule iffI)
 apply (case_tac "w")
  apply (simp add: epsclosure_start_step_star)
 apply (simp)
 apply (clarify)
 apply (simp add: epsclosure_start_step_star)
 apply (blast)
apply (erule disjE)
 apply (simp)
apply (blast intro: in_steps_epsclosure)
done

lemma fin_star_True[iff]: "\<And>A. fin (star A) (True#p) = fin A p"
by (simp add:star_def)

lemma fin_star_start[iff]: "\<And>A. fin (star A) (start(star A))"
by (simp add:star_def)

(* too complex! Simpler if loop back to start(star A)? *)
lemma accepts_star:
 "accepts (star A) w = 
 (\<exists>us. (\<forall>u \<in> set(us). accepts A u) \<and> (w = concat us))"
apply(unfold accepts_def)
apply (simp add: start_steps_star True_start_steps_star)
apply (rule iffI)
 apply (clarify)
 apply (erule disjE)
  apply (clarify)
  apply (simp)
  apply (rule_tac x = "[]" in exI)
  apply (simp)
 apply (clarify)
 apply (rule_tac x = "us@[v]" in exI)
 apply (simp add: accepts_def)
 apply (blast)
apply (clarify)
apply (rule_tac xs = "us" in rev_exhaust)
 apply (simp)
 apply (blast)
apply (clarify)
apply (simp add: accepts_def)
apply (blast)
done


(***** Correctness of r2n *****)

lemma accepts_rexp2nae:
 "\<And>w. accepts (rexp2nae r) w = (w : lang r)"
apply (induct "r")
     apply (simp add: accepts_def)
    apply simp
   apply (simp add: accepts_atom)
  apply (simp add: accepts_or)
 apply (simp add: accepts_conc Regular_Set.conc_def)
apply (simp add: accepts_star in_star_iff_concat subset_iff Ball_def)
done

end
