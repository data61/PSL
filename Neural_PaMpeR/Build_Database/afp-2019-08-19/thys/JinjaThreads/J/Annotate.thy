(*  Title:      Jinja/J/Annotate.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

section \<open>Program annotation\<close>

theory Annotate
imports
  WellType
begin

abbreviation (output)
  unanFAcc :: "'addr expr \<Rightarrow> vname \<Rightarrow> 'addr expr" ("(_\<bullet>_)" [10,10] 90)
where
  "unanFAcc e F \<equiv> FAcc e F (STR '''')"

abbreviation (output)
  unanFAss :: "'addr expr \<Rightarrow> vname \<Rightarrow> 'addr expr \<Rightarrow> 'addr expr" ("(_\<bullet>_ := _)" [10,0,90] 90)
where
  "unanFAss e F e' \<equiv> FAss e F (STR '''') e'"

definition array_length_field_name :: vname
where "array_length_field_name = STR ''length''"

notation (output) array_length_field_name ("length")

definition super :: vname
where "super = STR ''super''"

lemma super_neq_this [simp]: "super \<noteq> this" "this \<noteq> super"
by(simp_all add: this_def super_def)

inductive Anno :: "(ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool) \<Rightarrow> 'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr \<Rightarrow> 'addr expr \<Rightarrow> bool" 
  ("_,_,_ \<turnstile> _ \<leadsto> _"   [51,51,0,0,51]50)
  and Annos :: "(ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool) \<Rightarrow> 'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr list \<Rightarrow> 'addr expr list \<Rightarrow> bool"
  ("_,_,_ \<turnstile> _ [\<leadsto>] _" [51,51,0,0,51]50)
for is_lub :: "ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" and P :: "'addr J_prog"
where
  AnnoNew: "is_lub,P,E \<turnstile> new C \<leadsto> new C"
| AnnoNewArray: "is_lub,P,E \<turnstile> i \<leadsto> i' \<Longrightarrow> is_lub,P,E \<turnstile> newA T\<lfloor>i\<rceil> \<leadsto> newA T\<lfloor>i'\<rceil>"
| AnnoCast: "is_lub,P,E \<turnstile> e \<leadsto> e' \<Longrightarrow> is_lub,P,E \<turnstile> Cast C e \<leadsto> Cast C e'"
| AnnoInstanceOf: "is_lub,P,E \<turnstile> e \<leadsto> e' \<Longrightarrow> is_lub,P,E \<turnstile> e instanceof T \<leadsto> e' instanceof T"
| AnnoVal: "is_lub,P,E \<turnstile> Val v \<leadsto> Val v"
| AnnoVarVar: "\<lbrakk> E V = \<lfloor>T\<rfloor>; V \<noteq> super \<rbrakk> \<Longrightarrow> is_lub,P,E \<turnstile> Var V \<leadsto> Var V"
| AnnoVarField:
  \<comment> \<open>There is no need to handle access of array fields explicitly,
    because arrays do not implement methods, i.e. @{term "this"} is
    always of a @{term "Class"} type.\<close>
  "\<lbrakk> E V = None; V \<noteq> super; E this = \<lfloor>Class C\<rfloor>; P \<turnstile> C sees V:T (fm) in D \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> Var V \<leadsto> Var this\<bullet>V{D}"
| AnnoBinOp:
  "\<lbrakk> is_lub,P,E \<turnstile> e1 \<leadsto> e1';  is_lub,P,E \<turnstile> e2 \<leadsto> e2' \<rbrakk>
   \<Longrightarrow> is_lub,P,E \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 \<leadsto> e1' \<guillemotleft>bop\<guillemotright> e2'"
| AnnoLAssVar:
  "\<lbrakk> E V = \<lfloor>T\<rfloor>; V \<noteq> super; is_lub,P,E \<turnstile> e \<leadsto> e' \<rbrakk> \<Longrightarrow> is_lub,P,E \<turnstile> V:=e \<leadsto> V:=e'"
| AnnoLAssField:
  "\<lbrakk> E V = None; V \<noteq> super; E this = \<lfloor>Class C\<rfloor>; P \<turnstile> C sees V:T (fm) in D; is_lub,P,E \<turnstile> e \<leadsto> e' \<rbrakk>
   \<Longrightarrow> is_lub,P,E \<turnstile> V:=e \<leadsto> Var this\<bullet>V{D} := e'"
| AnnoAAcc:
  "\<lbrakk> is_lub,P,E \<turnstile> a \<leadsto> a'; is_lub,P,E \<turnstile> i \<leadsto> i' \<rbrakk> \<Longrightarrow> is_lub,P,E \<turnstile> a\<lfloor>i\<rceil> \<leadsto> a'\<lfloor>i'\<rceil>"
| AnnoAAss:
  "\<lbrakk> is_lub,P,E \<turnstile> a \<leadsto> a'; is_lub,P,E \<turnstile> i \<leadsto> i'; is_lub,P,E \<turnstile> e \<leadsto> e' \<rbrakk> \<Longrightarrow> is_lub,P,E \<turnstile> a\<lfloor>i\<rceil> := e \<leadsto> a'\<lfloor>i'\<rceil> := e'"
| AnnoALength:
  "is_lub,P,E \<turnstile> a \<leadsto> a' \<Longrightarrow> is_lub,P,E \<turnstile> a\<bullet>length \<leadsto> a'\<bullet>length"
| \<comment> \<open>All arrays implicitly declare a final field called @{term "array_length_field_name"} to
    store the array length, which hides a potential field of the same name in @{term "Object"} (cf. JLS 6.4.5).
    The last premise implements the hiding because field lookup does does not model the implicit declaration.\<close>
  AnnoFAcc:
  "\<lbrakk> is_lub,P,E \<turnstile> e \<leadsto> e';  is_lub,P,E \<turnstile> e' :: U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C sees F:T (fm) in D; 
     is_Array U \<longrightarrow> F \<noteq> array_length_field_name \<rbrakk>
   \<Longrightarrow> is_lub,P,E \<turnstile> e\<bullet>F{STR ''''} \<leadsto> e'\<bullet>F{D}"
| AnnoFAccALength:
  "\<lbrakk> is_lub,P,E \<turnstile> e \<leadsto> e'; is_lub,P,E \<turnstile> e' :: T\<lfloor>\<rceil> \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> e\<bullet>array_length_field_name{STR ''''} \<leadsto> e'\<bullet>length"
| AnnoFAccSuper:
  \<comment> \<open>In class C with super class D, "super" is syntactic sugar for "((D) this)" (cf. JLS, 15.11.2)\<close>
  "\<lbrakk> E this = \<lfloor>Class C\<rfloor>; C \<noteq> Object; class P C = \<lfloor>(D, fs, ms)\<rfloor>; 
     P \<turnstile> D sees F:T (fm) in D' \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> Var super\<bullet>F{STR ''''} \<leadsto> (Cast (Class D) (Var this))\<bullet>F{D'}"
|  AnnoFAss:
  "\<lbrakk> is_lub,P,E \<turnstile> e1 \<leadsto> e1';  is_lub,P,E \<turnstile> e2 \<leadsto> e2';
     is_lub,P,E \<turnstile> e1' :: U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C sees F:T (fm) in D;
     is_Array U \<longrightarrow> F \<noteq> array_length_field_name \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> e1\<bullet>F{STR ''''} := e2 \<leadsto> e1'\<bullet>F{D} := e2'"
| AnnoFAssSuper:
  "\<lbrakk> E this = \<lfloor>Class C\<rfloor>; C \<noteq> Object; class P C = \<lfloor>(D, fs, ms)\<rfloor>;
     P \<turnstile> D sees F:T (fm) in D'; is_lub,P,E \<turnstile> e \<leadsto> e' \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> Var super\<bullet>F{STR ''''} := e \<leadsto> (Cast (Class D) (Var this))\<bullet>F{D'} := e'"
| AnnoCAS:
  "\<lbrakk> is_lub,P,E \<turnstile> e1 \<leadsto> e1'; is_lub,P,E \<turnstile> e2 \<leadsto> e2'; is_lub,P,E \<turnstile> e3 \<leadsto> e3' \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3) \<leadsto> e1'\<bullet>compareAndSwap(D\<bullet>F, e2', e3')"
| AnnoCall:
  "\<lbrakk> is_lub,P,E \<turnstile> e \<leadsto> e';  is_lub,P,E \<turnstile> es [\<leadsto>] es' \<rbrakk>
   \<Longrightarrow> is_lub,P,E \<turnstile> Call e M es \<leadsto> Call e' M es'"
| AnnoBlock:
  "is_lub,P,E(V \<mapsto> T) \<turnstile> e \<leadsto> e'  \<Longrightarrow>  is_lub,P,E \<turnstile> {V:T=vo; e} \<leadsto> {V:T=vo; e'}"
| AnnoSync:
  "\<lbrakk> is_lub,P,E \<turnstile> e1 \<leadsto> e1'; is_lub,P,E \<turnstile> e2 \<leadsto> e2' \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> sync(e1) e2 \<leadsto> sync(e1') e2'"
| AnnoComp:
  "\<lbrakk> is_lub,P,E \<turnstile> e1 \<leadsto> e1';  is_lub,P,E \<turnstile> e2 \<leadsto> e2' \<rbrakk>
  \<Longrightarrow>  is_lub,P,E \<turnstile> e1;;e2 \<leadsto> e1';;e2'"
| AnnoCond:
  "\<lbrakk> is_lub,P,E \<turnstile> e \<leadsto> e'; is_lub,P,E \<turnstile> e1 \<leadsto> e1';  is_lub,P,E \<turnstile> e2 \<leadsto> e2' \<rbrakk>
   \<Longrightarrow> is_lub,P,E \<turnstile> if (e) e1 else e2 \<leadsto> if (e') e1' else e2'"
| AnnoLoop:
  "\<lbrakk> is_lub,P,E \<turnstile> e \<leadsto> e';  is_lub,P,E \<turnstile> c \<leadsto> c' \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> while (e) c \<leadsto> while (e') c'"
| AnnoThrow:
  "is_lub,P,E \<turnstile> e \<leadsto> e' \<Longrightarrow> is_lub,P,E \<turnstile> throw e \<leadsto> throw e'"
| AnnoTry:
  "\<lbrakk> is_lub,P,E \<turnstile> e1 \<leadsto> e1';  is_lub,P,E(V \<mapsto> Class C) \<turnstile> e2 \<leadsto> e2' \<rbrakk>
   \<Longrightarrow> is_lub,P,E \<turnstile> try e1 catch(C V) e2 \<leadsto> try e1' catch(C V) e2'"

| AnnoNil:
  "is_lub,P,E \<turnstile> [] [\<leadsto>] []"
| AnnoCons:
  "\<lbrakk> is_lub,P,E \<turnstile> e \<leadsto> e';  is_lub,P,E \<turnstile> es [\<leadsto>] es' \<rbrakk> \<Longrightarrow>  is_lub,P,E \<turnstile> e#es [\<leadsto>] e'#es'"

inductive_cases Anno_cases [elim!]:
  "is_lub',P,E \<turnstile> new C \<leadsto> e"
  "is_lub',P,E \<turnstile> newA T\<lfloor>e\<rceil> \<leadsto> e'"
  "is_lub',P,E \<turnstile> Cast T e \<leadsto> e'"
  "is_lub',P,E \<turnstile> e instanceof T \<leadsto> e'"
  "is_lub',P,E \<turnstile> Val v \<leadsto> e'"
  "is_lub',P,E \<turnstile> Var V \<leadsto> e'"
  "is_lub',P,E \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 \<leadsto> e'"
  "is_lub',P,E \<turnstile> V := e \<leadsto> e'"
  "is_lub',P,E \<turnstile> e1\<lfloor>e2\<rceil> \<leadsto> e'"
  "is_lub',P,E \<turnstile> e1\<lfloor>e2\<rceil> := e3 \<leadsto> e'"
  "is_lub',P,E \<turnstile> e\<bullet>length \<leadsto> e'"
  "is_lub',P,E \<turnstile> e\<bullet>F{D} \<leadsto> e'"
  "is_lub',P,E \<turnstile> e1\<bullet>F{D} := e2 \<leadsto> e'"
  "is_lub',P,E \<turnstile> e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3) \<leadsto> e'"
  "is_lub',P,E \<turnstile> e\<bullet>M(es) \<leadsto> e'"
  "is_lub',P,E \<turnstile> {V:T=vo; e} \<leadsto> e'"
  "is_lub',P,E \<turnstile> sync(e1) e2 \<leadsto> e'"
  "is_lub',P,E \<turnstile> insync(a) e2 \<leadsto> e'"
  "is_lub',P,E \<turnstile> e1;; e2 \<leadsto> e'"
  "is_lub',P,E \<turnstile> if (e) e1 else e2 \<leadsto> e'"
  "is_lub',P,E \<turnstile> while(e1) e2 \<leadsto> e'"
  "is_lub',P,E \<turnstile> throw e \<leadsto> e'"
  "is_lub',P,E \<turnstile> try e1 catch(C V) e2 \<leadsto> e'"

inductive_cases Annos_cases [elim!]:
  "is_lub',P,E \<turnstile> [] [\<leadsto>] es'"
  "is_lub',P,E \<turnstile> e # es [\<leadsto>] es'"

abbreviation Anno' :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr \<Rightarrow> 'addr expr \<Rightarrow> bool"  ("_,_ \<turnstile> _ \<leadsto> _"   [51,0,0,51]50)
where "Anno' P \<equiv> Anno (TypeRel.is_lub P) P"

abbreviation Annos' :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr list \<Rightarrow> 'addr expr list \<Rightarrow> bool"  ("_,_ \<turnstile> _ [\<leadsto>] _" [51,0,0,51]50)
where "Annos' P \<equiv> Annos (TypeRel.is_lub P) P"

definition annotate :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr \<Rightarrow> 'addr expr"
where "annotate P E e = THE_default e (\<lambda>e'. P,E \<turnstile> e \<leadsto> e')"

lemma fixes is_lub :: "ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile> lub'((_,/ _)') = _" [51,51,51] 50)
  assumes is_lub_unique: "\<And>T1 T2 T3 T4. \<lbrakk> \<turnstile> lub(T1, T2) = T3; \<turnstile> lub(T1, T2) = T4 \<rbrakk> \<Longrightarrow> T3 = T4"
  shows Anno_fun: "\<lbrakk> is_lub,P,E \<turnstile> e \<leadsto> e'; is_lub,P,E \<turnstile> e \<leadsto> e'' \<rbrakk> \<Longrightarrow> e' = e''"
  and Annos_fun: "\<lbrakk> is_lub,P,E \<turnstile> es [\<leadsto>] es'; is_lub,P,E \<turnstile> es [\<leadsto>] es'' \<rbrakk> \<Longrightarrow> es' = es''"
proof(induct arbitrary: e'' and es'' rule: Anno_Annos.inducts)
  case (AnnoFAcc E e e' U C F T fm D)
  from \<open>is_lub,P,E \<turnstile> e\<bullet>F{STR ''''} \<leadsto> e''\<close> show ?case
  proof(rule Anno_cases)
    fix e''' U' C' T' fm' D'
    assume "is_lub,P,E \<turnstile> e \<leadsto> e'''" "is_lub,P,E \<turnstile> e''' :: U'"
      and "class_type_of' U' = \<lfloor>C'\<rfloor>"
      and "P \<turnstile> C' sees F:T' (fm') in D'" "e'' = e'''\<bullet>F{D'}"
    from \<open>is_lub,P,E \<turnstile> e \<leadsto> e'''\<close> have "e' = e'''" by(rule AnnoFAcc)
    with \<open>is_lub,P,E \<turnstile> e' :: U\<close> \<open>is_lub,P,E \<turnstile> e''' :: U'\<close>
    have "U = U'" by(auto intro: WT_unique is_lub_unique)
    with \<open>class_type_of' U = \<lfloor>C\<rfloor>\<close> \<open>class_type_of' U' = \<lfloor>C'\<rfloor>\<close>
    have "C = C'" by(auto)
    with \<open>P \<turnstile> C' sees F:T' (fm') in D'\<close> \<open>P \<turnstile> C sees F:T (fm) in D\<close>
    have "D' = D" by(auto dest: sees_field_fun)
    with \<open>e'' = e'''\<bullet>F{D'}\<close> \<open>e' = e'''\<close> show ?thesis by simp
  next
    fix e''' T
    assume "e'' = e'''\<bullet>length"
      and "is_lub,P,E \<turnstile> e''' :: T\<lfloor>\<rceil>"
      and "is_lub,P,E \<turnstile> e \<leadsto> e'''"
      and "F = array_length_field_name"
    from \<open>is_lub,P,E \<turnstile> e \<leadsto> e'''\<close> have "e' = e'''" by(rule AnnoFAcc)
    with \<open>is_lub,P,E \<turnstile> e' :: U\<close> \<open>is_lub,P,E \<turnstile> e''' :: T\<lfloor>\<rceil>\<close> have "U = T\<lfloor>\<rceil>" by(auto intro: WT_unique is_lub_unique)
    with \<open>class_type_of' U = \<lfloor>C\<rfloor>\<close> \<open>is_Array U \<longrightarrow> F \<noteq> array_length_field_name\<close>
    show ?thesis using \<open>F = array_length_field_name\<close> by simp
  next
    fix C' D' fs ms T D''
    assume "E this = \<lfloor>Class C'\<rfloor>"
      and "class P C' = \<lfloor>(D', fs, ms)\<rfloor>"
      and "e = Var super"
      and "e'' = Cast (Class D') (Var this)\<bullet>F{D''}"
    with \<open>is_lub,P,E \<turnstile> e \<leadsto> e'\<close> have False by(auto)
    thus ?thesis ..
  qed
next
  case AnnoFAccALength thus ?case by(fastforce intro: WT_unique[OF is_lub_unique])
next
  case (AnnoFAss E e1 e1' e2 e2' U C F T fm D)
  from \<open>is_lub,P,E \<turnstile> e1\<bullet>F{STR ''''} := e2 \<leadsto> e''\<close> 
  show ?case
  proof(rule Anno_cases)
    fix e1'' e2'' U' C' T' fm' D'
    assume "is_lub,P,E \<turnstile> e1 \<leadsto> e1''" "is_lub,P,E \<turnstile> e2 \<leadsto> e2''"
      and "is_lub,P,E \<turnstile> e1'' :: U'" and "class_type_of' U' = \<lfloor>C'\<rfloor>"
      and "P \<turnstile> C' sees F:T' (fm') in D'"
      and "e'' = e1''\<bullet>F{D'} := e2''"
    from \<open>is_lub,P,E \<turnstile> e1 \<leadsto> e1''\<close> have "e1' = e1''" by(rule AnnoFAss)
    moreover with \<open>is_lub,P,E \<turnstile> e1' :: U\<close> \<open>is_lub,P,E \<turnstile> e1'' :: U'\<close>
    have "U = U'" by(auto intro: WT_unique is_lub_unique)
    with \<open>class_type_of' U = \<lfloor>C\<rfloor>\<close> \<open>class_type_of' U' = \<lfloor>C'\<rfloor>\<close>
    have "C = C'" by(auto)
    with \<open>P \<turnstile> C' sees F:T' (fm') in D'\<close> \<open>P \<turnstile> C sees F:T (fm) in D\<close>
    have "D' = D" by(auto dest: sees_field_fun)
    moreover from \<open>is_lub,P,E \<turnstile> e2 \<leadsto> e2''\<close> have "e2' = e2''" by(rule AnnoFAss)
    ultimately show ?thesis using \<open>e'' = e1''\<bullet>F{D'} := e2''\<close> by simp
  next
    fix C' D' fs ms T' fm' D'' e'''
    assume "e'' = Cast (Class D') (Var this)\<bullet>F{D''} := e'''"
      and "E this = \<lfloor>Class C'\<rfloor>"
      and "class P C' = \<lfloor>(D', fs, ms)\<rfloor>"
      and "P \<turnstile> D' sees F:T' (fm') in D''"
      and "is_lub,P,E \<turnstile> e2 \<leadsto> e'''"
      and "e1 = Var super"
    with \<open>is_lub,P,E \<turnstile> e1 \<leadsto> e1'\<close> have False by(auto elim: Anno_cases)
    thus ?thesis ..
  qed
qed(fastforce dest: sees_field_fun)+

subsection \<open>Code generation\<close>

definition Anno_code :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr \<Rightarrow> 'addr expr \<Rightarrow> bool" ("_,_ \<turnstile> _ \<leadsto>' _"   [51,0,0,51]50)
where "Anno_code P = Anno (is_lub_sup P) P"

definition Annos_code :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr list \<Rightarrow> 'addr expr list \<Rightarrow> bool" ("_,_ \<turnstile> _ [\<leadsto>''] _" [51,0,0,51]50)
where "Annos_code P = Annos (is_lub_sup P) P"

primrec block_types :: "('a, 'b, 'addr) exp \<Rightarrow> ty list" 
  and blocks_types :: "('a, 'b, 'addr) exp list \<Rightarrow> ty list"
where 
  "block_types (new C) = []"
| "block_types (newA T\<lfloor>e\<rceil>) = block_types e"
| "block_types (Cast U e) = block_types e"
| "block_types (e instanceof U) = block_types e"
| "block_types (e1\<guillemotleft>bop\<guillemotright>e2) = block_types e1 @ block_types e2"
| "block_types (Val v) = []"
| "block_types (Var V) = []"
| "block_types (V := e) = block_types e"
| "block_types (a\<lfloor>i\<rceil>) = block_types a @ block_types i"
| "block_types (a\<lfloor>i\<rceil> := e) = block_types a @ block_types i @ block_types e"
| "block_types (a\<bullet>length) = block_types a"
| "block_types (e\<bullet>F{D}) = block_types e"
| "block_types (e\<bullet>F{D} := e') = block_types e @ block_types e'"
| "block_types (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = block_types e @ block_types e' @ block_types e''"
| "block_types (e\<bullet>M(es)) = block_types e @ blocks_types es"
| "block_types {V:T=vo; e} = T # block_types e"
| "block_types (sync\<^bsub>V\<^esub>(e) e') = block_types e @ block_types e'"
| "block_types (insync\<^bsub>V\<^esub>(a) e) = block_types e"
| "block_types (e;;e') = block_types e @ block_types e'"
| "block_types (if (e) e1 else e2) = block_types e @ block_types e1 @ block_types e2"
| "block_types (while (b) c) = block_types b @ block_types c"
| "block_types (throw e) = block_types e"
| "block_types (try e catch(C V) e') = block_types e @ Class C # block_types e'"

| "blocks_types [] = []"
| "blocks_types (e#es) = block_types e @ blocks_types es"

lemma fixes is_lub1 :: "ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile>1 lub'((_,/ _)') = _" [51,51,51] 50)
  and is_lub2 :: "ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile>2 lub'((_,/ _)') = _" [51,51,51] 50)
  assumes wf: "wf_prog wf_md P"
  and is_lub1_into_is_lub2: "\<And>T1 T2 T3. \<lbrakk> \<turnstile>1 lub(T1, T2) = T3; is_type P T1; is_type P T2 \<rbrakk> \<Longrightarrow> \<turnstile>2 lub(T1, T2) = T3"
  and is_lub2_is_type: "\<And>T1 T2 T3. \<lbrakk> \<turnstile>2 lub(T1, T2) = T3; is_type P T1; is_type P T2 \<rbrakk> \<Longrightarrow> is_type P T3"
  shows Anno_change_is_lub:
  "\<lbrakk> is_lub1,P,E \<turnstile> e \<leadsto> e'; ran E \<union> set (block_types e) \<subseteq> types P \<rbrakk> \<Longrightarrow> is_lub2,P,E \<turnstile> e \<leadsto> e'"
  and Annos_change_is_lub:
  "\<lbrakk> is_lub1,P,E \<turnstile> es [\<leadsto>] es'; ran E \<union> set (blocks_types es) \<subseteq> types P \<rbrakk> \<Longrightarrow> is_lub2,P,E \<turnstile> es [\<leadsto>] es'"
proof(induct rule: Anno_Annos.inducts)
  case (AnnoBlock E V T e e' vo)
  from \<open>ran E \<union> set (block_types {V:T=vo; e}) \<subseteq> types P\<close>
  have "ran (E(V \<mapsto> T)) \<union> set (block_types e) \<subseteq> types P"
    by(auto simp add: ran_def)
  thus ?case using AnnoBlock by(blast intro: Anno_Annos.intros)
next
  case (AnnoTry E e1 e1' V C e2 e2')
  from \<open>ran E \<union> set (block_types (try e1 catch(C V) e2)) \<subseteq> types P\<close>
  have "ran (E(V \<mapsto> Class C)) \<union> set (block_types e2) \<subseteq> types P"
    by(auto simp add: ran_def)
  thus ?case using AnnoTry by(simp del: fun_upd_apply)(blast intro: Anno_Annos.intros)
qed(simp_all del: is_Array.simps is_Array_conv, (blast intro: Anno_Annos.intros WT_change_is_lub[OF wf, where ?is_lub1.0=is_lub1 and ?is_lub2.0=is_lub2] is_lub1_into_is_lub2 is_lub2_is_type)+)

lemma assumes wf: "wf_prog wf_md P"
  shows Anno_into_Anno_code: "\<lbrakk> P,E \<turnstile> e \<leadsto> e'; ran E \<union> set (block_types e) \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> e \<leadsto>' e'"
  and Annos_into_Annos_code: "\<lbrakk> P,E \<turnstile> es [\<leadsto>] es'; ran E \<union> set (blocks_types es) \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> es [\<leadsto>'] es'"
proof -
  assume anno: "P,E \<turnstile> e \<leadsto> e'" 
    and ran: "ran E \<union> set (block_types e) \<subseteq> types P"
  show "P,E \<turnstile> e \<leadsto>' e'" unfolding Anno_code_def
    by(rule Anno_change_is_lub[OF wf _ _ anno ran])(blast intro!: is_lub_sup.intros intro: is_lub_subD[OF wf] sup_is_type[OF wf] elim!: is_lub_sup.cases)+ 
next
  assume annos: "P,E \<turnstile> es [\<leadsto>] es'"
    and ran: "ran E \<union> set (blocks_types es) \<subseteq> types P"
  show "P,E \<turnstile> es [\<leadsto>'] es'" unfolding Annos_code_def
    by(rule Annos_change_is_lub[OF wf _ _ annos ran])(blast intro!: is_lub_sup.intros intro: is_lub_subD[OF wf] sup_is_type[OF wf] elim!: is_lub_sup.cases)+
qed 

lemma assumes wf: "wf_prog wf_md P"
  shows Anno_code_into_Anno: "\<lbrakk> P,E \<turnstile> e \<leadsto>' e'; ran E \<union> set (block_types e) \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> e \<leadsto> e'"
  and Annos_code_into_Annos: "\<lbrakk> P,E \<turnstile> es [\<leadsto>'] es'; ran E \<union> set (blocks_types es) \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> es [\<leadsto>] es'"
proof -
  assume anno: "P,E \<turnstile> e \<leadsto>' e'" 
    and ran: "ran E \<union> set (block_types e) \<subseteq> types P"
  show "P,E \<turnstile> e \<leadsto> e'"
    by(rule Anno_change_is_lub[OF wf _ _ anno[unfolded Anno_code_def] ran])(blast elim!: is_lub_sup.cases intro: sup_is_lubI[OF wf] is_lub_is_type[OF wf])+
next
  assume annos: "P,E \<turnstile> es [\<leadsto>'] es'"
    and ran: "ran E \<union> set (blocks_types es) \<subseteq> types P"
  show "P,E \<turnstile> es [\<leadsto>] es'"
    by(rule Annos_change_is_lub[OF wf _ _ annos[unfolded Annos_code_def] ran])(blast elim!: is_lub_sup.cases intro: sup_is_lubI[OF wf] is_lub_is_type[OF wf])+
qed

lemma fixes is_lub
  assumes wf: "wf_prog wf_md P"
  shows WT_block_types_is_type: "is_lub,P,E \<turnstile> e :: T \<Longrightarrow> set (block_types e) \<subseteq> types P"
  and WTs_blocks_types_is_type: "is_lub,P,E \<turnstile> es [::] Ts \<Longrightarrow> set (blocks_types es) \<subseteq> types P"
apply(induct rule: WT_WTs.inducts)
apply(auto intro: is_class_sub_Throwable[OF wf])
done

lemma fixes is_lub
  shows Anno_block_types: "is_lub,P,E \<turnstile> e \<leadsto> e' \<Longrightarrow> block_types e = block_types e'"
  and Annos_blocks_types: "is_lub,P,E \<turnstile> es [\<leadsto>] es' \<Longrightarrow> blocks_types es = blocks_types es'"
by(induct rule: Anno_Annos.inducts) auto

code_pred 
  (modes: (i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  [detect_switches, skip_proof]
  Anno
.

definition annotate_code :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr \<Rightarrow> 'addr expr"
where "annotate_code P E e = THE_default e (\<lambda>e'. P,E \<turnstile> e \<leadsto>' e')"

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  [inductify]
  Anno_code 
.

lemma eval_Anno_i_i_i_o_conv:
  "Predicate.eval (Anno_code_i_i_i_o P E e) = (\<lambda>e'. P,E \<turnstile> e \<leadsto>' e')"
by(auto intro!: ext intro: Anno_code_i_i_i_oI elim: Anno_code_i_i_i_oE)
 
lemma annotate_code [code]:
  "annotate_code P E e = Predicate.singleton (\<lambda>_. Code.abort (STR ''annotate'') (\<lambda>_. e)) (Anno_code_i_i_i_o P E e)"
by(simp add: THE_default_def Predicate.singleton_def annotate_code_def eval_Anno_i_i_i_o_conv)

end
