(*  Title:      JinjaThreads/J/Expr.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

section \<open>Expressions\<close>

theory Expr
imports
  "../Common/BinOp"
begin

datatype (dead 'a, dead 'b, dead 'addr) exp
  = new cname      \<comment> \<open>class instance creation\<close>
  | newArray ty "('a,'b,'addr) exp" ("newA _\<lfloor>_\<rceil>" [99,0] 90)    \<comment> \<open>array instance creation: type, size in outermost dimension\<close>
  | Cast ty "('a,'b,'addr) exp"      \<comment> \<open>type cast\<close>
  | InstanceOf "('a,'b,'addr) exp" ty ("_ instanceof _" [99, 99] 90) \<comment> \<open>instance of\<close>
  | Val "'addr val"      \<comment> \<open>value\<close>
  | BinOp "('a,'b,'addr) exp" bop "('a,'b,'addr) exp"     ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80)      \<comment> \<open>binary operation\<close>
  | Var 'a                                               \<comment> \<open>local variable (incl. parameter)\<close>
  | LAss 'a "('a,'b,'addr) exp"            ("_:=_" [90,90]90)                    \<comment> \<open>local assignment\<close>
  | AAcc "('a,'b,'addr) exp" "('a,'b,'addr) exp"            ("_\<lfloor>_\<rceil>" [99,0] 90)          \<comment> \<open>array cell read\<close>
  | AAss "('a,'b,'addr) exp" "('a,'b,'addr) exp" "('a,'b,'addr) exp" ("_\<lfloor>_\<rceil> := _" [10,99,90] 90)    \<comment> \<open>array cell assignment\<close>
  | ALen "('a,'b,'addr) exp"                 ("_\<bullet>length" [10] 90)          \<comment> \<open>array length\<close>
  | FAcc "('a,'b,'addr) exp" vname cname     ("_\<bullet>_{_}" [10,90,99]90)       \<comment> \<open>field access\<close>
  | FAss "('a,'b,'addr) exp" vname cname "('a,'b,'addr) exp"     ("_\<bullet>_{_} := _" [10,90,99,90]90)      \<comment> \<open>field assignment\<close>
  | CompareAndSwap "('a,'b,'addr) exp" cname vname "('a,'b,'addr) exp" "('a,'b,'addr) exp" ("_\<bullet>compareAndSwap('(_\<bullet>_, _, _'))" [10,90,90,90,90] 90) \<comment> \<open>compare and swap\<close>
  | Call "('a,'b,'addr) exp" mname "('a,'b,'addr) exp list"     ("_\<bullet>_'(_')" [90,99,0] 90)            \<comment> \<open>method call\<close>
  | Block 'a ty "'addr val option" "('a,'b,'addr) exp"    ("'{_:_=_; _}")
  | Synchronized 'b "('a,'b,'addr) exp" "('a,'b,'addr) exp" ("sync\<^bsub>_\<^esub> '(_') _" [99,99,90] 90)
  | InSynchronized 'b 'addr "('a,'b,'addr) exp" ("insync\<^bsub>_\<^esub> '(_') _" [99,99,90] 90)
  | Seq "('a,'b,'addr) exp" "('a,'b,'addr) exp"     ("_;;/ _"             [61,60]60)
  | Cond "('a,'b,'addr) exp" "('a,'b,'addr) exp" "('a,'b,'addr) exp"     ("if '(_') _/ else _" [80,79,79]70)
  | While "('a,'b,'addr) exp" "('a,'b,'addr) exp"     ("while '(_') _"     [80,79]70)
  | throw "('a,'b,'addr) exp"
  | TryCatch "('a,'b,'addr) exp" cname 'a "('a,'b,'addr) exp"     ("try _/ catch'(_ _') _"  [0,99,80,79] 70)

type_synonym
  'addr expr = "(vname, unit, 'addr) exp"    \<comment> \<open>Jinja expression\<close>
type_synonym
  'addr J_mb = "vname list \<times> 'addr expr"    \<comment> \<open>Jinja method body: parameter names and expression\<close>
type_synonym
  'addr J_prog = "'addr J_mb prog"          \<comment> \<open>Jinja program\<close>

translations
  (type) "'addr expr" <= (type) "(String.literal, unit, 'addr) exp"
  (type) "'addr J_prog" <= (type) "(String.literal list \<times> 'addr expr) prog"

subsection "Syntactic sugar"

abbreviation unit :: "('a,'b,'addr) exp"
where "unit \<equiv> Val Unit"

abbreviation null :: "('a,'b,'addr) exp"
where "null \<equiv> Val Null"

abbreviation addr :: "'addr \<Rightarrow> ('a,'b,'addr) exp"
where "addr a == Val (Addr a)"

abbreviation true :: "('a,'b,'addr) exp"
where "true == Val (Bool True)"

abbreviation false :: "('a,'b,'addr) exp"
where "false == Val (Bool False)"

abbreviation Throw :: "'addr \<Rightarrow> ('a,'b,'addr) exp"
where "Throw a == throw (Val (Addr a))"

abbreviation (in heap_base) THROW :: "cname \<Rightarrow> ('a,'b,'addr) exp"
where "THROW xc == Throw (addr_of_sys_xcpt xc)"

abbreviation sync_unit_syntax :: "('a,unit,'addr) exp \<Rightarrow> ('a,unit,'addr) exp \<Rightarrow> ('a,unit,'addr) exp" ("sync'(_') _" [99,90] 90)
where "sync(e1) e2 \<equiv> sync\<^bsub>()\<^esub> (e1) e2"

abbreviation insync_unit_syntax :: "'addr \<Rightarrow> ('a,unit,'addr) exp \<Rightarrow> ('a,unit,'addr) exp" ("insync'(_') _" [99,90] 90)
where "insync(a) e2 \<equiv> insync\<^bsub>()\<^esub> (a) e2"

text \<open>Java syntax for binary operators\<close>

abbreviation BinOp_Eq :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
  ("_ \<guillemotleft>==\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>==\<guillemotright> e' \<equiv> e \<guillemotleft>Eq\<guillemotright> e'"

abbreviation BinOp_NotEq :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>!=\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>!=\<guillemotright> e' \<equiv> e \<guillemotleft>NotEq\<guillemotright> e'"

abbreviation BinOp_LessThan :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft><\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft><\<guillemotright> e' \<equiv> e \<guillemotleft>LessThan\<guillemotright> e'"

abbreviation BinOp_LessOrEqual :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft><=\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft><=\<guillemotright> e' \<equiv> e \<guillemotleft>LessOrEqual\<guillemotright> e'"

abbreviation BinOp_GreaterThan :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>>\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>>\<guillemotright> e' \<equiv> e \<guillemotleft>GreaterThan\<guillemotright> e'"

abbreviation BinOp_GreaterOrEqual :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>>=\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>>=\<guillemotright> e' \<equiv> e \<guillemotleft>GreaterOrEqual\<guillemotright> e'"

abbreviation BinOp_Add :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>+\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>+\<guillemotright> e' \<equiv> e \<guillemotleft>Add\<guillemotright> e'"

abbreviation BinOp_Subtract :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>-\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>-\<guillemotright> e' \<equiv> e \<guillemotleft>Subtract\<guillemotright> e'"

abbreviation BinOp_Mult :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>*\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>*\<guillemotright> e' \<equiv> e \<guillemotleft>Mult\<guillemotright> e'"

abbreviation BinOp_Div :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>'/\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>/\<guillemotright> e' \<equiv> e \<guillemotleft>Div\<guillemotright> e'"

abbreviation BinOp_Mod :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>%\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>%\<guillemotright> e' \<equiv> e \<guillemotleft>Mod\<guillemotright> e'"

abbreviation BinOp_BinAnd :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>&\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>&\<guillemotright> e' \<equiv> e \<guillemotleft>BinAnd\<guillemotright> e'"

abbreviation BinOp_BinOr :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>|\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>|\<guillemotright> e' \<equiv> e \<guillemotleft>BinOr\<guillemotright> e'"

abbreviation BinOp_BinXor :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>^\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>^\<guillemotright> e' \<equiv> e \<guillemotleft>BinXor\<guillemotright> e'"

abbreviation BinOp_ShiftLeft :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft><<\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft><<\<guillemotright> e' \<equiv> e \<guillemotleft>ShiftLeft\<guillemotright> e'"

abbreviation BinOp_ShiftRightZeros :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>>>>\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>>>>\<guillemotright> e' \<equiv> e \<guillemotleft>ShiftRightZeros\<guillemotright> e'"

abbreviation BinOp_ShiftRightSigned :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>>>\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>>>\<guillemotright> e' \<equiv> e \<guillemotleft>ShiftRightSigned\<guillemotright> e'"

abbreviation BinOp_CondAnd :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>&&\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>&&\<guillemotright> e' \<equiv> if (e) e' else false"

abbreviation BinOp_CondOr :: "('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp \<Rightarrow> ('a, 'b, 'c) exp"
   ("_ \<guillemotleft>||\<guillemotright> _" [80,81] 80)
where "e \<guillemotleft>||\<guillemotright> e' \<equiv> if (e) true else e'"

lemma inj_Val [simp]: "inj Val"
by(rule inj_onI)(simp)

lemma expr_ineqs [simp]: "Val v ;; e \<noteq> e" "if (e1) e else e2 \<noteq> e" "if (e1) e2 else e \<noteq> e"
by(induct e) auto

subsection\<open>Free Variables\<close>

primrec fv  :: "('a,'b,'addr) exp      \<Rightarrow> 'a set"
  and fvs :: "('a,'b,'addr) exp list \<Rightarrow> 'a set"
where
  "fv(new C) = {}"
| "fv(newA T\<lfloor>e\<rceil>) = fv e"
| "fv(Cast C e) = fv e"
| "fv(e instanceof T) = fv e"
| "fv(Val v) = {}"
| "fv(e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(Var V) = {V}"
| "fv(a\<lfloor>i\<rceil>) = fv a \<union> fv i"
| "fv(AAss a i e) = fv a \<union> fv i \<union> fv e"
| "fv(a\<bullet>length) = fv a"
| "fv(LAss V e) = {V} \<union> fv e"
| "fv(e\<bullet>F{D}) = fv e"
| "fv(FAss e\<^sub>1 F D e\<^sub>2) = fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(e\<^sub>1\<bullet>compareAndSwap(D\<bullet>F, e\<^sub>2, e\<^sub>3)) = fv e\<^sub>1 \<union> fv e\<^sub>2 \<union> fv e\<^sub>3"
| "fv(e\<bullet>M(es)) = fv e \<union> fvs es"
| "fv({V:T=vo; e}) = fv e - {V}"
| "fv(sync\<^bsub>V\<^esub> (h) e) = fv h \<union> fv e"
| "fv(insync\<^bsub>V\<^esub> (a) e) = fv e"
| "fv(e\<^sub>1;;e\<^sub>2) = fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(if (b) e\<^sub>1 else e\<^sub>2) = fv b \<union> fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(while (b) e) = fv b \<union> fv e"
| "fv(throw e) = fv e"
| "fv(try e\<^sub>1 catch(C V) e\<^sub>2) = fv e\<^sub>1 \<union> (fv e\<^sub>2 - {V})"

| "fvs([]) = {}"
| "fvs(e#es) = fv e \<union> fvs es"

lemma [simp]: "fvs(es @ es') = fvs es \<union> fvs es'"
by(induct es) auto

lemma [simp]: "fvs(map Val vs) = {}"
by (induct vs) auto

subsection\<open>Locks and addresses\<close>

primrec expr_locks :: "('a,'b,'addr) exp \<Rightarrow> 'addr \<Rightarrow> nat"
  and expr_lockss :: "('a,'b,'addr) exp list \<Rightarrow> 'addr \<Rightarrow> nat"
where
  "expr_locks (new C) = (\<lambda>ad. 0)"
| "expr_locks (newA T\<lfloor>e\<rceil>) = expr_locks e"
| "expr_locks (Cast T e) = expr_locks e"
| "expr_locks (e instanceof T) = expr_locks e"
| "expr_locks (Val v) = (\<lambda>ad. 0)"
| "expr_locks (Var v) = (\<lambda>ad. 0)"
| "expr_locks (e \<guillemotleft>bop\<guillemotright> e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
| "expr_locks (V := e) = expr_locks e"
| "expr_locks (a\<lfloor>i\<rceil>) = (\<lambda>ad. expr_locks a ad + expr_locks i ad)"
| "expr_locks (AAss a i e) = (\<lambda>ad. expr_locks a ad + expr_locks i ad + expr_locks e ad)"
| "expr_locks (a\<bullet>length) = expr_locks a"
| "expr_locks (e\<bullet>F{D}) = expr_locks e"
| "expr_locks (FAss e F D e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
| "expr_locks (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = (\<lambda>ad. expr_locks e ad + expr_locks e' ad + expr_locks e'' ad)"
| "expr_locks (e\<bullet>m(ps)) = (\<lambda>ad. expr_locks e ad + expr_lockss ps ad)"
| "expr_locks ({V : T=vo; e}) = expr_locks e"
| "expr_locks (sync\<^bsub>V\<^esub> (o') e) = (\<lambda>ad. expr_locks o' ad + expr_locks e ad)"
| "expr_locks (insync\<^bsub>V\<^esub> (a) e) = (\<lambda>ad. if (a = ad) then Suc (expr_locks e ad) else expr_locks e ad)"
| "expr_locks (e;;e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
| "expr_locks (if (b) e else e') = (\<lambda>ad. expr_locks b ad + expr_locks e ad + expr_locks e' ad)"
| "expr_locks (while (b) e) = (\<lambda>ad. expr_locks b ad + expr_locks e ad)"
| "expr_locks (throw e) = expr_locks e"
| "expr_locks (try e catch(C v) e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"

| "expr_lockss [] = (\<lambda>a. 0)"
| "expr_lockss (x#xs) = (\<lambda>ad. expr_locks x ad + expr_lockss xs ad)"

lemma expr_lockss_append [simp]:
  "expr_lockss (es @ es') = (\<lambda>ad. expr_lockss es ad + expr_lockss es' ad)"
by(induct es) auto

lemma expr_lockss_map_Val [simp]: "expr_lockss (map Val vs) = (\<lambda>ad. 0)"
by(induct vs) auto

primrec contains_insync :: "('a,'b,'addr) exp \<Rightarrow> bool"
  and contains_insyncs :: "('a,'b,'addr) exp list \<Rightarrow> bool"
where
  "contains_insync (new C) = False"
| "contains_insync (newA T\<lfloor>i\<rceil>) = contains_insync i"
| "contains_insync (Cast T e) = contains_insync e"
| "contains_insync (e instanceof T) = contains_insync e"
| "contains_insync (Val v) = False"
| "contains_insync (Var v) = False"
| "contains_insync (e \<guillemotleft>bop\<guillemotright> e') = (contains_insync e \<or> contains_insync e')"
| "contains_insync (V := e) = contains_insync e"
| "contains_insync (a\<lfloor>i\<rceil>) = (contains_insync a \<or> contains_insync i)"
| "contains_insync (AAss a i e) = (contains_insync a \<or> contains_insync i \<or> contains_insync e)"
| "contains_insync (a\<bullet>length) = contains_insync a"
| "contains_insync (e\<bullet>F{D}) = contains_insync e"
| "contains_insync (FAss e F D e') = (contains_insync e \<or> contains_insync e')"
| "contains_insync (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = (contains_insync e \<or> contains_insync e' \<or> contains_insync e'')"
| "contains_insync (e\<bullet>m(pns)) = (contains_insync e \<or> contains_insyncs pns)"
| "contains_insync ({V : T=vo; e}) = contains_insync e"
| "contains_insync (sync\<^bsub>V\<^esub> (o') e) = (contains_insync o' \<or> contains_insync e)"
| "contains_insync (insync\<^bsub>V\<^esub> (a) e) = True"
| "contains_insync (e;;e') = (contains_insync e \<or> contains_insync e')"
| "contains_insync (if (b) e else e') = (contains_insync b \<or> contains_insync e \<or> contains_insync e')"
| "contains_insync (while (b) e) = (contains_insync b \<or> contains_insync e)"
| "contains_insync (throw e) = contains_insync e"
| "contains_insync (try e catch(C v) e') = (contains_insync e \<or> contains_insync e')"

| "contains_insyncs [] = False"
| "contains_insyncs (x # xs) = (contains_insync x \<or> contains_insyncs xs)"
  
lemma contains_insyncs_append [simp]:
  "contains_insyncs (es @ es') \<longleftrightarrow> contains_insyncs es \<or> contains_insyncs es'"
by(induct es, auto)

lemma fixes e :: "('a, 'b, 'addr) exp"
  and es :: "('a, 'b, 'addr) exp list"
  shows contains_insync_conv: "(contains_insync e \<longleftrightarrow> (\<exists>ad. expr_locks e ad > 0))"
    and contains_insyncs_conv: "(contains_insyncs es \<longleftrightarrow> (\<exists>ad. expr_lockss es ad > 0))"
by(induct e and es rule: expr_locks.induct expr_lockss.induct)(auto)

lemma contains_insyncs_map_Val [simp]: "\<not> contains_insyncs (map Val vs)"
by(induct vs) auto

subsection \<open>Value expressions\<close>

inductive is_val :: "('a,'b,'addr) exp \<Rightarrow> bool" where
  "is_val (Val v)"

declare is_val.intros [simp]
declare is_val.cases [elim!]

lemma is_val_iff: "is_val e \<longleftrightarrow> (\<exists>v. e = Val v)"
by(auto)

code_pred is_val .

fun is_vals :: "('a,'b,'addr) exp list \<Rightarrow> bool" where
  "is_vals [] = True"
| "is_vals (e#es) = (is_val e \<and> is_vals es)"

lemma is_vals_append [simp]: "is_vals (es @ es') \<longleftrightarrow> is_vals es \<and> is_vals es'"
by(induct es) auto

lemma is_vals_conv: "is_vals es = (\<exists>vs. es = map Val vs)"
by(induct es)(auto simp add: Cons_eq_map_conv)

lemma is_vals_map_Vals [simp]: "is_vals (map Val vs) = True"
unfolding is_vals_conv by auto

inductive is_addr :: "('a,'b,'addr) exp \<Rightarrow> bool"
where "is_addr (addr a)"

declare is_addr.intros[intro!]
declare is_addr.cases[elim!]

lemma [simp]: "(is_addr e) \<longleftrightarrow> (\<exists>a. e = addr a)"
by auto

primrec the_Val :: "('a, 'b, 'addr) exp \<Rightarrow> 'addr val"
where
  "the_Val (Val v) = v"

inductive is_Throws :: "('a, 'b, 'addr) exp list \<Rightarrow> bool"
where
  "is_Throws (Throw a # es)"
| "is_Throws es \<Longrightarrow> is_Throws (Val v # es)"

inductive_simps is_Throws_simps:
  "is_Throws []"
  "is_Throws (e # es)"

code_pred is_Throws .

lemma is_Throws_conv: "is_Throws es \<longleftrightarrow> (\<exists>vs a es'. es = map Val vs @ Throw a # es')"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs
    by(induct)(fastforce simp add: Cons_eq_append_conv Cons_eq_map_conv)+
next
  assume ?rhs thus ?lhs
    by(induct es)(auto simp add: is_Throws_simps Cons_eq_map_conv Cons_eq_append_conv)
qed

subsection \<open>\<open>blocks\<close>\<close>

fun blocks :: "'a list \<Rightarrow> ty list \<Rightarrow> 'addr val list \<Rightarrow> ('a,'b,'addr) exp \<Rightarrow> ('a,'b,'addr) exp"
where
  "blocks (V # Vs) (T # Ts) (v # vs) e = {V:T=\<lfloor>v\<rfloor>; blocks Vs Ts vs e}"
| "blocks []       []       []       e = e"

lemma [simp]:
  "\<lbrakk> size vs = size Vs; size Ts = size Vs \<rbrakk> \<Longrightarrow> fv (blocks Vs Ts vs e) = fv e - set Vs"
by(induct rule:blocks.induct)(simp_all, blast)

lemma expr_locks_blocks:
  "\<lbrakk> length vs = length pns; length Ts = length pns \<rbrakk>
  \<Longrightarrow> expr_locks (blocks pns Ts vs e) = expr_locks e"
by(induct pns Ts vs e rule: blocks.induct)(auto)

subsection \<open>Final expressions\<close>

inductive final :: "('a,'b,'addr) exp \<Rightarrow> bool" where
  "final (Val v)"
| "final (Throw a)"

declare final.cases [elim]
declare final.intros[simp]

lemmas finalE[consumes 1, case_names Val Throw] = final.cases

lemma final_iff: "final e \<longleftrightarrow> (\<exists>v. e = Val v) \<or> (\<exists>a. e = Throw a)"
by(auto)

lemma final_locks: "final e \<Longrightarrow> expr_locks e l = 0"
by(auto elim: finalE)

inductive finals :: "('a,'b,'addr) exp list \<Rightarrow> bool"
where
  "finals []"
| "finals (Throw a # es)"
| "finals es \<Longrightarrow> finals (Val v # es)"

inductive_simps finals_simps:
  "finals (e # es)"

lemma [iff]: "finals []"
by(rule finals.intros)

lemma [iff]: "finals (Val v # es) = finals es"
by(simp add: finals_simps)

lemma finals_app_map [iff]: "finals (map Val vs @ es) = finals es"
by(induct vs) simp_all

lemma [iff]: "finals (throw e # es) = (\<exists>a. e = addr a)"
by(simp add: finals_simps)

lemma not_finals_ConsI: "\<not> final e \<Longrightarrow> \<not> finals (e # es)"
by(simp add: finals_simps final_iff)

lemma finals_iff: "finals es \<longleftrightarrow> (\<exists>vs. es = map Val vs) \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es')"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs
    by induct(auto simp add: Cons_eq_append_conv Cons_eq_map_conv, metis)
next
  assume ?rhs thus ?lhs by(induct es) auto
qed

code_pred final .

subsection \<open>converting results from external calls\<close>

primrec extRet2J :: "('a, 'b, 'addr) exp \<Rightarrow> 'addr extCallRet \<Rightarrow> ('a, 'b, 'addr) exp"
where
  "extRet2J e (RetVal v) = Val v"
| "extRet2J e (RetExc a) = Throw a"
| "extRet2J e RetStaySame = e"

lemma fv_extRet2J [simp]: "fv (extRet2J e va) \<subseteq> fv e"
by(cases va) simp_all

subsection \<open>expressions at a call\<close>

primrec call :: "('a,'b,'addr) exp \<Rightarrow> ('addr \<times> mname \<times> 'addr val list) option"
  and calls :: "('a,'b,'addr) exp list \<Rightarrow> ('addr \<times> mname \<times> 'addr val list) option"
where
  "call (new C) = None"
| "call (newA T\<lfloor>e\<rceil>) = call e"
| "call (Cast C e) = call e"
| "call (e instanceof T) = call e"
| "call (Val v) = None"
| "call (Var V) = None"
| "call (V:=e) = call e"
| "call (e \<guillemotleft>bop\<guillemotright> e') = (if is_val e then call e' else call e)"
| "call (a\<lfloor>i\<rceil>) = (if is_val a then call i else call a)"
| "call (AAss a i e) = (if is_val a then (if is_val i then call e else call i) else call a)"
| "call (a\<bullet>length) = call a"
| "call (e\<bullet>F{D}) = call e"
| "call (FAss e F D e') = (if is_val e then call e' else call e)"
| "call (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = (if is_val e then if is_val e' then call e'' else call e' else call e)"
| "call (e\<bullet>M(es)) = (if is_val e then
                     (if is_vals es \<and> is_addr e then \<lfloor>(THE a. e = addr a, M, THE vs. es = map Val vs)\<rfloor> else calls es) 
                     else call e)"
| "call ({V:T=vo; e}) = call e"
| "call (sync\<^bsub>V\<^esub> (o') e) = call o'"
| "call (insync\<^bsub>V\<^esub> (a) e) = call e"
| "call (e;;e') = call e"
| "call (if (e) e1 else e2) = call e"
| "call (while(b) e) = None"
| "call (throw e) = call e"
| "call (try e1 catch(C V) e2) = call e1"

| "calls [] = None"
| "calls (e#es) = (if is_val e then calls es else call e)"

lemma calls_append [simp]:
  "calls (es @ es') = (if calls es = None \<and> is_vals es then calls es' else calls es)"
by(induct es) auto

lemma call_callE [consumes 1, case_names CallObj CallParams Call]:
  "\<lbrakk> call (obj\<bullet>M(pns)) = \<lfloor>(a, M', vs)\<rfloor>;
     call obj = \<lfloor>(a, M', vs)\<rfloor> \<Longrightarrow> thesis; 
     \<And>v. \<lbrakk> obj = Val v; calls pns = \<lfloor>(a, M', vs)\<rfloor> \<rbrakk> \<Longrightarrow> thesis;
     \<lbrakk> obj = addr a; pns = map Val vs; M = M' \<rbrakk> \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(auto split: if_split_asm simp add: is_vals_conv)

lemma calls_map_Val [simp]:
  "calls (map Val vs) = None"
by(induct vs) auto

lemma call_not_is_val [dest]: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<not> is_val e"
by(cases e) auto

lemma is_calls_not_is_vals [dest]: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<not> is_vals es"
by(induct es) auto

end
