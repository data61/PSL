theory "USubst"
imports
  Complex_Main
  "Syntax"          
  "Static_Semantics"
  "Coincidence"
  "Denotational_Semantics"
begin 
section \<open>Uniform Substitution\<close>

text \<open>uniform substitution representation as tuple of partial maps from identifiers to type-compatible replacements.\<close>
type_synonym usubst =
 "(ident \<rightharpoonup> trm) \<times> (ident \<rightharpoonup> trm) \<times> (ident \<rightharpoonup> fml) \<times> (ident \<rightharpoonup> game)"

abbreviation SConst:: "usubst \<Rightarrow> (ident \<rightharpoonup> trm)" 
where "SConst \<equiv> (\<lambda>(F0, _, _, _). F0)"
abbreviation SFuncs:: "usubst \<Rightarrow> (ident \<rightharpoonup> trm)" 
where "SFuncs \<equiv> (\<lambda>(_, F, _, _). F)"
abbreviation SPreds:: "usubst \<Rightarrow> (ident \<rightharpoonup> fml)" 
where "SPreds \<equiv> (\<lambda>(_, _, P, _). P)"
abbreviation SGames:: "usubst \<Rightarrow> (ident \<rightharpoonup> game)" 
where "SGames \<equiv> (\<lambda>(_, _, _, G). G)"

text \<open>crude approximation of size which is enough for termination arguments\<close>
definition usubstsize:: "usubst \<Rightarrow> nat"
where "usubstsize \<sigma> = (if (dom (SFuncs \<sigma>) = {} \<and> dom (SPreds \<sigma>) = {}) then 1 else 2)"


text \<open>dot is some fixed constant function symbol that is reserved for the purposes of the substitution\<close>
definition dot:: "trm"
  where "dot = Const (dotid)"


subsection \<open>Strict Mechanism for Handling Substitution Partiality in Isabelle\<close>

text \<open>Optional terms that result from a substitution, either actually a term or just none to indicate that the substitution clashed\<close>
type_synonym trmo = "trm option"

abbreviation undeft:: trmo where "undeft \<equiv> None"
abbreviation Aterm:: "trm \<Rightarrow> trmo" where "Aterm \<equiv> Some"

lemma undeft_None: "undeft=None" by simp
lemma Aterm_Some: "Aterm \<theta>=Some \<theta>" by simp

lemma undeft_equiv: "(\<theta>\<noteq>undeft) = (\<exists>t. \<theta>=Aterm t)"
  by simp

text \<open>Plus on defined terms, strict undeft otherwise \<close>
fun Pluso :: "trmo \<Rightarrow> trmo \<Rightarrow> trmo"
where
  "Pluso (Aterm \<theta>) (Aterm \<eta>) = Aterm(Plus \<theta> \<eta>)"
| "Pluso undeft \<eta> = undeft"
| "Pluso \<theta> undeft = undeft"

text \<open>Times on defined terms, strict undeft otherwise \<close>
fun Timeso :: "trmo \<Rightarrow> trmo \<Rightarrow> trmo"
where
  "Timeso (Aterm \<theta>) (Aterm \<eta>) = Aterm(Times \<theta> \<eta>)"
| "Timeso undeft \<eta> = undeft"
| "Timeso \<theta> undeft = undeft"

fun Differentialo :: "trmo \<Rightarrow> trmo"
where
  "Differentialo (Aterm \<theta>) = Aterm(Differential \<theta>)"
| "Differentialo undeft = undeft"

lemma Pluso_undef: "(Pluso \<theta> \<eta> = undeft) = (\<theta>=undeft \<or> \<eta>=undeft)"    by (metis Pluso.elims option.distinct(1))
lemma Timeso_undef: "(Timeso \<theta> \<eta> = undeft) = (\<theta>=undeft \<or> \<eta>=undeft)"  by (metis Timeso.elims option.distinct(1)) 
lemma Differentialo_undef: "(Differentialo \<theta> = undeft) = (\<theta>=undeft)" by (metis Differentialo.elims option.distinct(1)) 


type_synonym fmlo = "fml option"

abbreviation undeff:: fmlo where "undeff \<equiv> None"
abbreviation Afml:: "fml \<Rightarrow> fmlo" where "Afml \<equiv> Some"

type_synonym gameo = "game option"

abbreviation undefg:: gameo where "undefg \<equiv> None"
abbreviation Agame:: "game \<Rightarrow> gameo" where "Agame \<equiv> Some"

lemma undeff_equiv: "(\<phi>\<noteq>undeff) = (\<exists>f. \<phi>=Afml f)"
  by simp

lemma undefg_equiv: "(\<alpha>\<noteq>undefg) = (\<exists>g. \<alpha>=Agame g)"
  by simp


text \<open>Geq on defined terms, strict undeft otherwise \<close>
fun Geqo :: "trmo \<Rightarrow> trmo \<Rightarrow> fmlo"
where
  "Geqo (Aterm \<theta>) (Aterm \<eta>) = Afml(Geq \<theta> \<eta>)"
| "Geqo undeft \<eta> = undeff"
| "Geqo \<theta> undeft = undeff"

text \<open>Not on defined formulas, strict undeft otherwise \<close>
fun Noto :: "fmlo \<Rightarrow> fmlo"
where
  "Noto (Afml \<phi>) = Afml(Not \<phi>)"
| "Noto undeff = undeff"

text \<open>And on defined formulas, strict undeft otherwise \<close>
fun Ando :: "fmlo \<Rightarrow> fmlo \<Rightarrow> fmlo"
where
  "Ando (Afml \<phi>) (Afml \<psi>) = Afml(And \<phi> \<psi>)"
| "Ando undeff \<psi> = undeff"
| "Ando \<phi> undeff = undeff"

text \<open>Exists on defined formulas, strict undeft otherwise \<close>
fun Existso :: "variable \<Rightarrow> fmlo \<Rightarrow> fmlo"
where
  "Existso x (Afml \<phi>) = Afml(Exists x \<phi>)"
| "Existso x undeff = undeff"

text \<open>Diamond on defined games/formulas, strict undeft otherwise \<close>
fun Diamondo :: "gameo \<Rightarrow> fmlo \<Rightarrow> fmlo"
where
  "Diamondo (Agame \<alpha>) (Afml \<phi>) = Afml(Diamond \<alpha> \<phi>)"
| "Diamondo undefg \<phi> = undeff"
| "Diamondo \<alpha> undeff = undeff"

lemma Geqo_undef: "(Geqo \<theta> \<eta> = undeff) = (\<theta>=undeft \<or> \<eta>=undeft)"
  by (metis Geqo.elims option.distinct(1)) 
lemma Noto_undef: "(Noto \<phi> = undeff) = (\<phi>=undeff)"
  by (metis Noto.elims option.distinct(1)) 
lemma Ando_undef: "(Ando \<phi> \<psi> = undeff) = (\<phi>=undeff \<or> \<psi>=undeff)"
  by (metis Ando.elims option.distinct(1)) 
lemma Existso_undef: "(Existso x \<phi> = undeff) = (\<phi>=undeff)"
  by (metis Existso.elims option.distinct(1)) 
lemma Diamondo_undef: "(Diamondo \<alpha> \<phi> = undeff) = (\<alpha>=undefg \<or> \<phi>=undeff)"
  by (metis Diamondo.elims option.distinct(1)) 


text \<open>Assign on defined terms, strict undefg otherwise \<close>
fun Assigno :: "variable \<Rightarrow> trmo \<Rightarrow> gameo"
where
  "Assigno x (Aterm \<theta>) = Agame(Assign x \<theta>)"
| "Assigno x undeft = undefg"

fun ODEo :: "ident \<Rightarrow> trmo \<Rightarrow> gameo"
where
  "ODEo x (Aterm \<theta>) = Agame(ODE x \<theta>)"
| "ODEo x undeft = undefg"

text \<open>Test on defined formulas, strict undefg otherwise \<close>
fun Testo :: "fmlo \<Rightarrow> gameo"
where
  "Testo (Afml \<phi>) = Agame(Test \<phi>)"
| "Testo undeff = undefg"

text \<open>Choice on defined games, strict undefg otherwise \<close>
fun Choiceo :: "gameo \<Rightarrow> gameo \<Rightarrow> gameo"
where
  "Choiceo (Agame \<alpha>) (Agame \<beta>) = Agame(Choice \<alpha> \<beta>)"
| "Choiceo \<alpha> undefg = undefg"
| "Choiceo undefg \<beta> = undefg"

text \<open>Compose on defined games, strict undefg otherwise \<close>
fun Composeo :: "gameo \<Rightarrow> gameo \<Rightarrow> gameo"
where
  "Composeo (Agame \<alpha>) (Agame \<beta>) = Agame(Compose \<alpha> \<beta>)"
| "Composeo \<alpha> undefg = undefg"
| "Composeo undefg \<beta> = undefg"

text \<open>Loop on defined games, strict undefg otherwise \<close>
fun Loopo :: "gameo \<Rightarrow> gameo"
where
  "Loopo (Agame \<alpha>) = Agame(Loop \<alpha>)"
| "Loopo undefg = undefg"

text \<open>Dual on defined games, strict undefg otherwise \<close>
fun Dualo :: "gameo \<Rightarrow> gameo"
where
  "Dualo (Agame \<alpha>) = Agame(Dual \<alpha>)"
| "Dualo undefg = undefg"


lemma Assigno_undef: "(Assigno x \<theta> = undefg) = (\<theta>=undeft)"  by (metis Assigno.elims option.distinct(1)) 
lemma ODEo_undef: "(ODEo x \<theta> = undefg) = (\<theta>=undeft)"        by (metis ODEo.elims option.distinct(1)) 
lemma Testo_undef: "(Testo \<phi> = undefg) = (\<phi>=undeff)"        by (metis Testo.elims option.distinct(1)) 
lemma Choiceo_undef: "(Choiceo \<alpha> \<beta> = undefg) = (\<alpha>=undefg \<or> \<beta>=undefg)"   by (metis Choiceo.elims option.distinct(1))
lemma Composeo_undef: "(Composeo \<alpha> \<beta> = undefg) = (\<alpha>=undefg \<or> \<beta>=undefg)" by (metis Composeo.elims option.distinct(1))
lemma Loopo_undef: "(Loopo \<alpha> = undefg) = (\<alpha>=undefg)"        by (metis Loopo.elims option.distinct(1))
lemma Dualo_undef: "(Dualo \<alpha> = undefg) = (\<alpha>=undefg)"        by (metis Dualo.elims option.distinct(1))
  


subsection \<open>Recursive Application of One-Pass Uniform Substitution\<close>

text \<open>\<open>dotsubstt \<theta>\<close> is the dot substitution \<open>{. ~> \<theta>}\<close> substituting a term for the . function symbol\<close>
definition dotsubstt:: "trm \<Rightarrow> usubst"
  where "dotsubstt \<theta> = (
         (\<lambda>f. (if f=dotid then (Some(\<theta>)) else None)),
         (\<lambda>_. None),
         (\<lambda>_. None),
         (\<lambda>_. None)
  )"

definition usappconst:: "usubst \<Rightarrow> variable set \<Rightarrow> ident \<Rightarrow> (trmo)"
where "usappconst \<sigma> U f \<equiv> (case SConst \<sigma> f of Some r \<Rightarrow> if FVT(r)\<inter>U={} then Aterm(r) else undeft | None \<Rightarrow> Aterm(Const f))"

function usubstappt:: "usubst \<Rightarrow> variable set \<Rightarrow> (trm \<Rightarrow> trmo)"
where
  "usubstappt \<sigma> U (Var x)     = Aterm (Var x)"
| "usubstappt \<sigma> U (Number r)  = Aterm (Number r)"
| "usubstappt \<sigma> U (Const f)   = usappconst \<sigma> U f"
| "usubstappt \<sigma> U (Func f \<theta>)  =
  (case usubstappt \<sigma> U \<theta> of undeft   \<Rightarrow> undeft
                          | Aterm \<sigma>\<theta> \<Rightarrow> (case SFuncs \<sigma> f of Some r \<Rightarrow> if FVT(r)\<inter>U={} then usubstappt(dotsubstt \<sigma>\<theta>) {} r else undeft | None \<Rightarrow> Aterm(Func f \<sigma>\<theta>)))"
| "usubstappt \<sigma> U (Plus \<theta> \<eta>)  = Pluso (usubstappt \<sigma> U \<theta>) (usubstappt \<sigma> U \<eta>)"
| "usubstappt \<sigma> U (Times \<theta> \<eta>) = Timeso (usubstappt \<sigma> U \<theta>) (usubstappt \<sigma> U \<eta>)"
| "usubstappt \<sigma> U (Differential \<theta>) = Differentialo (usubstappt \<sigma> allvars \<theta>)"
  by pat_completeness auto
termination
  by (relation "measures [\<lambda>(\<sigma>,U,\<theta>). usubstsize \<sigma> , \<lambda>(\<sigma>,U,\<theta>). size \<theta>]")
  (auto simp add: usubstsize_def dotsubstt_def)
  
(* Expand let constructs automatically *)
declare Let_def [simp]
  
function usubstappf:: "usubst \<Rightarrow> variable set \<Rightarrow> (fml \<Rightarrow> fmlo)"
     and usubstappp:: "usubst \<Rightarrow> variable set \<Rightarrow> (game \<Rightarrow> variable set \<times> gameo)"
where
  "usubstappf \<sigma> U (Pred p \<theta>)   = 
  (case usubstappt \<sigma> U \<theta> of undeft   \<Rightarrow> undeff
                          | Aterm \<sigma>\<theta> \<Rightarrow> (case SPreds \<sigma> p of Some r \<Rightarrow> if FVF(r)\<inter>U={} then usubstappf(dotsubstt \<sigma>\<theta>) {} r else undeff | None \<Rightarrow> Afml(Pred p \<sigma>\<theta>)))"
| "usubstappf \<sigma> U (Geq \<theta> \<eta>)    = Geqo (usubstappt \<sigma> U \<theta>) (usubstappt \<sigma> U \<eta>)"
| "usubstappf \<sigma> U (Not \<phi>)      = Noto (usubstappf \<sigma> U \<phi>)"
| "usubstappf \<sigma> U (And \<phi> \<psi>)    = Ando (usubstappf \<sigma> U \<phi>) (usubstappf \<sigma> U \<psi>)"
| "usubstappf \<sigma> U (Exists x \<phi>) = Existso x (usubstappf \<sigma> (U\<union>{x}) \<phi>)"
| "usubstappf \<sigma> U (Diamond \<alpha> \<phi>) = (let V\<alpha> = usubstappp \<sigma> U \<alpha> in Diamondo (snd V\<alpha>) (usubstappf \<sigma> (fst V\<alpha>) \<phi>))"

| "usubstappp \<sigma> U (Game a)   =
  (case SGames \<sigma> a of Some r \<Rightarrow> (U\<union>BVG(r),Agame r)
                    | None   \<Rightarrow> (allvars,Agame(Game a)))"
| "usubstappp \<sigma> U (Assign x \<theta>) = (U\<union>{x}, Assigno x (usubstappt \<sigma> U \<theta>))"
| "usubstappp \<sigma> U (Test \<phi>) = (U, Testo (usubstappf \<sigma> U \<phi>))"
| "usubstappp \<sigma> U (Choice \<alpha> \<beta>) =
    (let V\<alpha> = usubstappp \<sigma> U \<alpha> in
     let W\<beta> = usubstappp \<sigma> U \<beta> in
     (fst V\<alpha>\<union>fst W\<beta>, Choiceo (snd V\<alpha>) (snd W\<beta>)))"
| "usubstappp \<sigma> U (Compose \<alpha> \<beta>) =
    (let V\<alpha> = usubstappp \<sigma> U \<alpha> in
     let W\<beta> = usubstappp \<sigma> (fst V\<alpha>) \<beta> in
     (fst W\<beta>, Composeo (snd V\<alpha>) (snd W\<beta>)))"
| "usubstappp \<sigma> U (Loop \<alpha>) =
    (let V = fst(usubstappp \<sigma> U \<alpha>) in
     (V, Loopo (snd(usubstappp \<sigma> V \<alpha>))))"
| "usubstappp \<sigma> U (Dual \<alpha>) =
    (let V\<alpha> = usubstappp \<sigma> U \<alpha> in (fst V\<alpha>, Dualo (snd V\<alpha>)))"
| "usubstappp \<sigma> U (ODE x \<theta>) = (U\<union>{RVar x,DVar x}, ODEo x (usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta>))"
by pat_completeness auto
termination 
  by (relation "measures [(\<lambda>k. usubstsize (case k of Inl(\<sigma>,U,\<phi>) \<Rightarrow> \<sigma> | Inr(\<sigma>,U,\<alpha>) \<Rightarrow> \<sigma>)) , (\<lambda>k. case k of Inl (\<sigma>,U,\<phi>) \<Rightarrow> size \<phi> | Inr (\<sigma>,U,\<alpha>) \<Rightarrow> size \<alpha>)]") 
  (auto simp add: usubstsize_def dotsubstt_def)

text \<open>Induction Principles for Uniform Substitutions\<close>
lemmas usubstappt_induct = usubstappt.induct [case_names Var Number Const FuncMatch Plus Times Differential]
lemmas usubstappfp_induct = usubstappf_usubstappp.induct [case_names Pred Geq Not And Exists Diamond  Game Assign Test Choice Compose Loop Dual ODE]


paragraph \<open>Simple Observations for Automation\<close>

text \<open>More automation for Case\<close>

lemma usappconst_simp [simp]: "SConst \<sigma> f = Some r \<Longrightarrow> FVT(r)\<inter>U={} \<Longrightarrow> usappconst \<sigma> U f = Aterm(r)"
  and "SConst \<sigma> f = None \<Longrightarrow> usappconst \<sigma> U f = Aterm(Const f)"
  and "SConst \<sigma> f = Some r \<Longrightarrow> FVT(r)\<inter>U\<noteq>{} \<Longrightarrow> usappconst \<sigma> U f = undeft"
  unfolding usappconst_def by auto

lemma usappconst_conv: "usappconst \<sigma> U f\<noteq>undeft \<Longrightarrow>
  SConst \<sigma> f = None \<or> (\<exists>r. SConst \<sigma> f = Some r \<and> FVT(r)\<inter>U={})"
  (*by (smt option.case_eq_if option.collapse usappconst_def)*)
proof-
  assume as: "usappconst \<sigma> U f\<noteq>undeft"
  show "SConst \<sigma> f = None \<or> (\<exists>r. SConst \<sigma> f = Some r \<and> FVT(r)\<inter>U={})"
  proof (cases "SConst \<sigma> f")
    case None
    then show ?thesis
    by auto 
  next
    case (Some a)
    then show ?thesis using as usappconst_def[where \<sigma>=\<sigma> and U=U and f=f] option.distinct(1) by fastforce
  qed
qed

lemma usubstappt_const [simp]: "SConst \<sigma> f = Some r \<Longrightarrow> FVT(r)\<inter>U={} \<Longrightarrow> usubstappt \<sigma> U (Const f) = Aterm(r)"
  and "SConst \<sigma> f = None \<Longrightarrow> usubstappt \<sigma> U (Const f) = Aterm(Const f)"
  and "SConst \<sigma> f = Some r \<Longrightarrow> FVT(r)\<inter>U\<noteq>{} \<Longrightarrow> usubstappt \<sigma> U (Const f) = undeft"
  by (auto simp add: usappconst_def)

lemma usubstappt_const_conv: "usubstappt \<sigma> U (Const f)\<noteq>undeft \<Longrightarrow>
  SConst \<sigma> f = None \<or> (\<exists>r. SConst \<sigma> f = Some r \<and> FVT(r)\<inter>U={})"
  using usappconst_conv by auto

lemma usubstappt_func [simp]: "SFuncs \<sigma> f = Some r \<Longrightarrow> FVT(r)\<inter>U={} \<Longrightarrow> usubstappt \<sigma> U \<theta> = Aterm \<sigma>\<theta> \<Longrightarrow>
  usubstappt \<sigma> U (Func f \<theta>) = usubstappt (dotsubstt \<sigma>\<theta>) {} r"
  and "SFuncs \<sigma> f=None \<Longrightarrow>  usubstappt \<sigma> U \<theta> = Aterm \<sigma>\<theta> \<Longrightarrow> usubstappt \<sigma> U (Func f \<theta>) = Aterm(Func f \<sigma>\<theta>)"
  and "usubstappt \<sigma> U \<theta> = undeft \<Longrightarrow> usubstappt \<sigma> U (Func f \<theta>) = undeft"
  by auto

lemma usubstappt_func2 [simp]: "SFuncs \<sigma> f = Some r \<Longrightarrow> FVT(r)\<inter>U\<noteq>{} \<Longrightarrow> usubstappt \<sigma> U (Func f \<theta>) = undeft"
  by (cases "usubstappt \<sigma> U \<theta>") (auto)

lemma usubstappt_func_conv: "usubstappt \<sigma> U (Func f \<theta>) \<noteq> undeft \<Longrightarrow>
  usubstappt \<sigma> U \<theta> \<noteq> undeft \<and>
    (SFuncs \<sigma> f = None \<or> (\<exists>r. SFuncs \<sigma> f = Some r \<and> FVT(r)\<inter>U={}))"
  by (metis (lifting) option.simps(4) undeft_equiv usubstappt.simps(4) usubstappt_func2)
  (*by (cases "usubstappt \<sigma> U \<theta>") (auto) *)

lemma usubstappt_plus_conv: "usubstappt \<sigma> U (Plus \<theta> \<eta>) \<noteq> undeft \<Longrightarrow>
  usubstappt \<sigma> U \<theta> \<noteq> undeft \<and> usubstappt \<sigma> U \<eta> \<noteq> undeft"
  by (simp add: Pluso_undef)
  
lemma usubstappt_times_conv: "usubstappt \<sigma> U (Times \<theta> \<eta>) \<noteq> undeft \<Longrightarrow>
  usubstappt \<sigma> U \<theta> \<noteq> undeft \<and> usubstappt \<sigma> U \<eta> \<noteq> undeft"
  by (simp add: Timeso_undef)

lemma usubstappt_differential_conv: "usubstappt \<sigma> U (Differential \<theta>) \<noteq> undeft \<Longrightarrow>
  usubstappt \<sigma> allvars \<theta> \<noteq> undeft"
  by (simp add: Differentialo_undef)
  

lemma usubstappf_pred [simp]: "SPreds \<sigma> p = Some r \<Longrightarrow> FVF(r)\<inter>U={} \<Longrightarrow> usubstappt \<sigma> U \<theta> = Aterm \<sigma>\<theta> \<Longrightarrow>
  usubstappf \<sigma> U (Pred p \<theta>) = usubstappf (dotsubstt \<sigma>\<theta>) {} r"
  and "SPreds \<sigma> p = None \<Longrightarrow> usubstappt \<sigma> U \<theta> = Aterm \<sigma>\<theta> \<Longrightarrow> usubstappf \<sigma> U (Pred p \<theta>) = Afml(Pred p \<sigma>\<theta>)"
  and "usubstappt \<sigma> U \<theta> = undeft \<Longrightarrow> usubstappf \<sigma> U (Pred p \<theta>) = undeff"
  by auto
  
lemma usubstappf_pred2 [simp]: "SPreds \<sigma> p = Some r \<Longrightarrow> FVF(r)\<inter>U\<noteq>{} \<Longrightarrow> usubstappf \<sigma> U (Pred p \<theta>) = undeff"
  by (cases "usubstappt \<sigma> U \<theta>") (auto)

lemma usubstappf_pred_conv: "usubstappf \<sigma> U (Pred p \<theta>) \<noteq> undeff \<Longrightarrow>
  usubstappt \<sigma> U \<theta> \<noteq> undeft \<and>
    (SPreds \<sigma> p = None \<or> (\<exists>r. SPreds \<sigma> p = Some r \<and> FVF(r)\<inter>U={}))"
  by (metis (lifting) option.simps(4) undeff_equiv usubstappf.simps(1) usubstappf_pred2)

lemma usubstappf_geq: "usubstappt \<sigma> U \<theta> \<noteq> undeft \<Longrightarrow> usubstappt \<sigma> U \<eta> \<noteq> undeft \<Longrightarrow>
  usubstappf \<sigma> U (Geq \<theta> \<eta>) = Afml(Geq (the (usubstappt \<sigma> U \<theta>)) (the (usubstappt \<sigma> U \<eta>)))"
  by fastforce

lemma usubstappf_geq_conv: "usubstappf \<sigma> U (Geq \<theta> \<eta>) \<noteq> undeff \<Longrightarrow>
  usubstappt \<sigma> U \<theta> \<noteq> undeft \<and> usubstappt \<sigma> U \<eta> \<noteq> undeft"
  by (simp add: Geqo_undef) 

lemma usubstappf_geqr: "usubstappf \<sigma> U (Geq \<theta> \<eta>) \<noteq> undeff \<Longrightarrow>
  usubstappf \<sigma> U (Geq \<theta> \<eta>) = Afml(Geq (the (usubstappt \<sigma> U \<theta>)) (the (usubstappt \<sigma> U \<eta>)))"
  using usubstappf_geq usubstappf_geq_conv by blast

lemma usubstappf_exists: "usubstappf \<sigma> U (Exists x \<phi>) \<noteq> undeff \<Longrightarrow>
  usubstappf \<sigma> U (Exists x \<phi>) = Afml(Exists x (the (usubstappf \<sigma> (U\<union>{x}) \<phi>)))"
  using Existso_undef by auto

lemma usubstappp_game [simp]: "SGames \<sigma> a = Some r \<Longrightarrow> usubstappp \<sigma> U (Game a) = (U\<union>BVG(r),Agame(r))"
  and "SGames \<sigma> a = None \<Longrightarrow> usubstappp \<sigma> U (Game a) = (allvars,Agame(Game a))"
   by auto  

lemma usubstappp_choice [simp]: "usubstappp \<sigma> U (Choice \<alpha> \<beta>) =
  (fst(usubstappp \<sigma> U \<alpha>)\<union>fst(usubstappp \<sigma> U \<beta>), Choiceo (snd(usubstappp \<sigma> U \<alpha>)) (snd(usubstappp \<sigma> U \<beta>)))"
   by auto

lemma usubstappp_choice_conv : "snd(usubstappp \<sigma> U (Choice \<alpha> \<beta>)) \<noteq> undefg \<Longrightarrow>
  snd(usubstappp \<sigma> U \<alpha>) \<noteq> undefg \<and> snd(usubstappp \<sigma> U \<beta>) \<noteq> undefg"
  by (simp add: Choiceo_undef)

lemma usubstappp_compose [simp]: "usubstappp \<sigma> U (Compose \<alpha> \<beta>) =
  (fst(usubstappp \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<beta>), Composeo (snd(usubstappp \<sigma> U \<alpha>)) (snd(usubstappp \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<beta>)))"
  by simp

lemma usubstappp_loop: "usubstappp \<sigma> U (Loop \<alpha>) =
  (fst(usubstappp \<sigma> U \<alpha>), Loopo (snd(usubstappp \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<alpha>)))"
  by auto

lemma usubstappp_dual [simp]: "usubstappp \<sigma> U (Dual \<alpha>) =
  (fst(usubstappp \<sigma> U \<alpha>), Dualo (snd (usubstappp \<sigma> U \<alpha>)))"
  by simp


  
section \<open>Soundness of Uniform Substitution\<close>


subsection \<open>USubst Application is a Function of Deterministic Result\<close>

lemma usubstappt_det: "usubstappt \<sigma> U \<theta> \<noteq> undeft \<Longrightarrow> usubstappt \<sigma> V \<theta> \<noteq> undeft \<Longrightarrow>
  usubstappt \<sigma> U \<theta> = usubstappt \<sigma> V \<theta>"
proof (induction \<theta>)
  case (Var x)
  then show ?case by simp
next
  case (Number x)
  then show ?case by simp
next
  case (Const f)
  then show ?case
    (*by (smt option.case_eq_if usappconst_def usubstappt.simps(3))*)
  proof - (*sledgehammer*)
    have f1: "usubstappt \<sigma> U (Const f) = (case SConst \<sigma> f of None \<Rightarrow> Aterm (Const f) | Some t \<Rightarrow> if FVT t \<inter> U = {} then Aterm t else undeft)"
      by (simp add: usappconst_def)
    have f2: "\<forall>z f za. if za = undeft then (case za of None \<Rightarrow> z::trm option | Some x \<Rightarrow> f x) = z else (case za of None \<Rightarrow> z | Some x \<Rightarrow> f x) = f (the za)"
      by force
    then have "SConst \<sigma> f \<noteq> undeft \<longrightarrow> (if FVT (the (SConst \<sigma> f)) \<inter> U = {} then Aterm (the (SConst \<sigma> f)) else undeft) = usappconst \<sigma> U f"
      by (simp add: usappconst_def)
    then have f3: "SConst \<sigma> f \<noteq> undeft \<longrightarrow> FVT (the (SConst \<sigma> f)) \<inter> U = {}"
      by (metis Const.prems(1) usubstappt.simps(3))
    have "SConst \<sigma> f \<noteq> undeft \<longrightarrow> (if FVT (the (SConst \<sigma> f)) \<inter> V = {} then Aterm (the (SConst \<sigma> f)) else undeft) = usappconst \<sigma> V f"
      using f2 usappconst_def by presburger
    then have "SConst \<sigma> f \<noteq> undeft \<longrightarrow> FVT (the (SConst \<sigma> f)) \<inter> V = {}"
      by (metis (no_types) Const.prems(2) usubstappt.simps(3))
    then have f4: "SConst \<sigma> f \<noteq> undeft \<longrightarrow> usubstappt \<sigma> U (Const f) = usappconst \<sigma> V f"
      using f3 f2 f1 usappconst_def by presburger
    { assume "usubstappt \<sigma> U (Const f) \<noteq> usubstappt \<sigma> V (Const f)"
      then have "usubstappt \<sigma> U (Const f) \<noteq> (case SConst \<sigma> f of None \<Rightarrow> Aterm (Const f) | Some t \<Rightarrow> if FVT t \<inter> V = {} then Aterm t else undeft)"
        by (simp add: usappconst_def)
      then have "SConst \<sigma> f \<noteq> undeft"
        using f2 f1 by (metis (no_types))
      then have ?thesis
        using f4 by simp }
    then show ?thesis
      by blast
  qed
next
  case (Func f \<theta>)
  then show ?case using usubstappt_func
      (*by (cases "SFuncs \<sigma> f") (auto simp add: usubstappt_func)*)
      (*by (smt option.case_eq_if usubstappt.simps(4))*)
  proof - (*sledgehammer*)
    have f1: "(case usubstappt \<sigma> U \<theta> of None \<Rightarrow> undeft | Some t \<Rightarrow> (case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f t) | Some ta \<Rightarrow> if FVT ta \<inter> U = {} then usubstappt (dotsubstt t) {} ta else undeft)) \<noteq> undeft"
      using Func(2) by auto
    have f2: "\<forall>z f za. if za = undeft then (case za of None \<Rightarrow> z::trm option | Some x \<Rightarrow> f x) = z else (case za of None \<Rightarrow> z | Some x \<Rightarrow> f x) = f (the za)"
      by force
    then have f3: "usubstappt \<sigma> U \<theta> \<noteq> undeft"
      using f1 by meson
    have "(case usubstappt \<sigma> V \<theta> of None \<Rightarrow> undeft | Some t \<Rightarrow> (case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f t) | Some ta \<Rightarrow> if FVT ta \<inter> V = {} then usubstappt (dotsubstt t) {} ta else undeft)) \<noteq> undeft"
      using Func(3) by auto
    then have f4: "usubstappt \<sigma> V \<theta> \<noteq> undeft"
      using f2 by meson
    then have f5: "usubstappt \<sigma> U (trm.Func f \<theta>) = (case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f (the (usubstappt \<sigma> V \<theta>))) | Some t \<Rightarrow> if FVT t \<inter> U = {} then usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} t else undeft)"
      using f3 f2 Func(1) usubstappt.simps(4) by presburger
    have "SFuncs \<sigma> f \<noteq> undeft \<longrightarrow> (if FVT (the (SFuncs \<sigma> f)) \<inter> U = {} then usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SFuncs \<sigma> f)) else undeft) = usubstappt \<sigma> U (trm.Func f \<theta>)"
      using f4 f3 f2 Func(1) usubstappt.simps(4) by presburger
    then have f6: "SFuncs \<sigma> f \<noteq> undeft \<longrightarrow> FVT (the (SFuncs \<sigma> f)) \<inter> U = {}"
      by (metis Func(2))
    have f7: "(case usubstappt \<sigma> V \<theta> of None \<Rightarrow> undeft | Some t \<Rightarrow> (case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f t) | Some ta \<Rightarrow> if FVT ta \<inter> V = {} then usubstappt (dotsubstt t) {} ta else undeft)) = (case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f (the (usubstappt \<sigma> V \<theta>))) | Some t \<Rightarrow> if FVT t \<inter> V = {} then usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} t else undeft)"
      using f4 f2 by presburger
    then have "SFuncs \<sigma> f \<noteq> undeft \<longrightarrow> (if FVT (the (SFuncs \<sigma> f)) \<inter> V = {} then usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SFuncs \<sigma> f)) else undeft) = usubstappt \<sigma> V (trm.Func f \<theta>)"
      using f2 by simp
    then have f8: "SFuncs \<sigma> f \<noteq> undeft \<longrightarrow> FVT (the (SFuncs \<sigma> f)) \<inter> V = {}"
      by (metis (full_types) Func(3))
    { assume "usubstappt \<sigma> U (trm.Func f \<theta>) \<noteq> usubstappt \<sigma> V (trm.Func f \<theta>)"
      moreover
      { assume "(case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f (the (usubstappt \<sigma> V \<theta>))) | Some t \<Rightarrow> if FVT t \<inter> V = {} then usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} t else undeft) \<noteq> Aterm (trm.Func f (the (usubstappt \<sigma> V \<theta>)))"
        then have "SFuncs \<sigma> f \<noteq> undeft"
          using f2 by meson }
      ultimately have "SFuncs \<sigma> f \<noteq> undeft"
        using f7 f5 by fastforce
      then have ?thesis
        using f8 f7 f6 f5 f2 by simp }
    then show ?thesis
      by blast
  qed 
next
  case (Plus \<theta>1 \<theta>2)
  then show ?case using Pluso_undef by auto 
next
  case (Times \<theta>1 \<theta>2)
  then show ?case using Timeso_undef by auto
next
  case (Differential \<theta>)
  then show ?case using Differentialo_undef by auto
qed


lemma usubstappf_and_usubstappp_det: 
shows "usubstappf \<sigma> U \<phi> \<noteq> undeff \<Longrightarrow> usubstappf \<sigma> V \<phi> \<noteq> undeff \<Longrightarrow> usubstappf \<sigma> U \<phi> = usubstappf \<sigma> V \<phi>"
and "snd(usubstappp \<sigma> U \<alpha>) \<noteq> undefg \<Longrightarrow> snd(usubstappp \<sigma> V \<alpha>) \<noteq> undefg \<Longrightarrow> snd(usubstappp \<sigma> U \<alpha>) = snd(usubstappp \<sigma> V \<alpha>)"
proof (induction \<phi> and \<alpha> arbitrary: U V and U V)
  case (Pred p \<theta>)
  then show ?case using usubstappt_det usubstappf_pred
  (*by (metis usubstappf.simps(1)) *)
  (*by (smt option.case_eq_if usubstappf.simps(1)) *)
    proof - (*sledgehammer*)
    have f1: "(case usubstappt \<sigma> U \<theta> of None \<Rightarrow> undeff | Some t \<Rightarrow> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p t) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt t) {} f else undeff)) \<noteq> undeff"
    using Pred.prems(1) by auto
    have f2: "\<forall>z f za. if za = undeft then (case za of None \<Rightarrow> z::fml option | Some x \<Rightarrow> f x) = z else (case za of None \<Rightarrow> z | Some x \<Rightarrow> f x) = f (the za)"
    by (simp add: option.case_eq_if)
    then have f3: "(case usubstappt \<sigma> U \<theta> of None \<Rightarrow> undeff | Some t \<Rightarrow> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p t) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt t) {} f else undeff)) = (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> U \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> U \<theta>))) {} f else undeff)"
    using f1 by meson
    have f4: "(case usubstappt \<sigma> V \<theta> of None \<Rightarrow> undeff | Some t \<Rightarrow> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p t) | Some f \<Rightarrow> if FVF f \<inter> V = {} then usubstappf (dotsubstt t) {} f else undeff)) \<noteq> undeff"
    using Pred.prems(2) by auto
    then have f5: "usubstappt \<sigma> U \<theta> = usubstappt \<sigma> V \<theta>"
    using f2 f1 by (meson usubstappt_det)
    then have f6: "usubstappf \<sigma> U (Pred p \<theta>) = (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff)"
    using f3 usubstappf.simps(1) by presburger
    have f7: "\<forall>z f za. if za = undeff then (case za of None \<Rightarrow> z::fml option | Some x \<Rightarrow> f x) = z else (case za of None \<Rightarrow> z | Some x \<Rightarrow> f x) = f (the za)"
    by (simp add: option.case_eq_if)
    have f8: "(case usubstappt \<sigma> V \<theta> of None \<Rightarrow> undeff | Some t \<Rightarrow> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p t) | Some f \<Rightarrow> if FVF f \<inter> V = {} then usubstappf (dotsubstt t) {} f else undeff)) = (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff)"
    using f4 f2 by meson
    then have f9: "SPreds \<sigma> p = undeff \<longrightarrow> usubstappf \<sigma> U (Pred p \<theta>) = usubstappf \<sigma> V (Pred p \<theta>)"
    using f6 by fastforce
    { assume "usubstappf \<sigma> U (Pred p \<theta>) \<noteq> usubstappf \<sigma> V (Pred p \<theta>)"
      then have "usubstappf \<sigma> U (Pred p \<theta>) \<noteq> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff)"
      using f8 by simp
      moreover
      { assume "usubstappf \<sigma> U (Pred p \<theta>) \<noteq> (if FVF (the (SPreds \<sigma> p)) \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff)"
        moreover
        { assume "usubstappf \<sigma> U (Pred p \<theta>) \<noteq> usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p))"
          moreover
          { assume "usubstappf \<sigma> U (Pred p \<theta>) \<noteq> (if FVF (the (SPreds \<sigma> p)) \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff)"
            then have "(case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff) \<noteq> (if FVF (the (SPreds \<sigma> p)) \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff)"
            using f6 by force
            then have "SPreds \<sigma> p = undeff"
            using f7 by (metis (no_types, lifting) Pred.prems(1) calculation f5 option.collapse usubstappf_pred usubstappf_pred2 usubstappf_pred_conv) }
          moreover
          { assume "(if FVF (the (SPreds \<sigma> p)) \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff) \<noteq> usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p))"
            then have "(if FVF (the (SPreds \<sigma> p)) \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff) \<noteq> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> U \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> U \<theta>))) {} f else undeff)"
            using f3 Pred.prems(1) by auto
            then have "(if FVF (the (SPreds \<sigma> p)) \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff) \<noteq> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff)"
            using f5 using Pred.prems(1) \<open>(if FVF (the (SPreds \<sigma> p)) \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff) \<noteq> usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p))\<close> f6 by auto
            then have "(case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff) \<noteq> (if FVF (the (SPreds \<sigma> p)) \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff)"
            by simp
            then have "SPreds \<sigma> p = undeff"
            using f7 proof -
              show ?thesis
                using \<open>(case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff) \<noteq> (if FVF (the (SPreds \<sigma> p)) \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff)\<close> calculation(2) f6 by presburger
            qed}
          ultimately have "SPreds \<sigma> p = undeff"
          by fastforce }
        moreover
        { assume "(if FVF (the (SPreds \<sigma> p)) \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff) \<noteq> usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p))"
          then have "(case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff) \<noteq> (if FVF (the (SPreds \<sigma> p)) \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff)"
          using f8 Pred.prems(2) by auto
          then have "SPreds \<sigma> p = undeff"
          using f7 by (metis (no_types, lifting) Pred.prems(2) \<open>(if FVF (the (SPreds \<sigma> p)) \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff) \<noteq> usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p))\<close> option.collapse usubstappf_pred2)}
        ultimately have "SPreds \<sigma> p = undeff"
        by fastforce }
      moreover
      { assume "(case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff) \<noteq> (if FVF (the (SPreds \<sigma> p)) \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff)"
        then have "SPreds \<sigma> p = undeff"
        using f7 by (metis (no_types, lifting) Pred.prems(1) Pred.prems(2) \<open>usubstappf \<sigma> U (Pred p \<theta>) \<noteq> usubstappf \<sigma> V (Pred p \<theta>)\<close> calculation(2) option.collapse usubstappf_pred usubstappf_pred_conv)}
      ultimately have ?thesis
      using f9 by fastforce }
    then show ?thesis
    by blast
    qed
  next
  case (Geq \<theta> \<eta>)
  then show ?case using usubstappt_det by (metis Geqo_undef usubstappf.simps(2))
  next
  case (Not x)
  then show ?case by (metis Noto.simps(2) usubstappf.simps(3))
  next
  case (And x1 x2)
  then show ?case by (metis Ando_undef usubstappf.simps(4))
  next
  case (Exists x1 x2)
  then show ?case by (metis Existso_undef usubstappf.simps(5))
  next
  case (Diamond x1 x2)
  then show ?case by (metis Diamondo_undef usubstappf.simps(6))
  next
  case (Game a)
  then show ?case by (cases "SGames \<sigma> a") (auto)
  next
  case (Assign x \<theta>)
  then show ?case using usubstappt_det by (metis Assigno_undef snd_conv usubstappp.simps(2))
  next
  case (ODE x \<theta>)
  then show ?case using usubstappt_det by (metis ODEo_undef snd_conv usubstappp.simps(8))
  next
  case (Test \<phi>)
  then show ?case by (metis Testo_undef snd_conv usubstappp.simps(3))
  next
  case (Choice \<alpha> \<beta>)
  then show ?case by (metis Choiceo_undef snd_conv usubstappp.simps(4))
  next
  case (Compose \<alpha> \<beta>)
  then show ?case by (metis Composeo_undef snd_conv usubstappp.simps(5))
  next
  case (Loop \<alpha>)
  then show ?case by (metis Loopo_undef snd_conv usubstappp.simps(6))
  next
  case (Dual \<alpha>)
  then show ?case by (metis Dualo_undef snd_conv usubstappp.simps(7))
qed

lemma usubstappf_det: "usubstappf \<sigma> U \<phi> \<noteq> undeff \<Longrightarrow> usubstappf \<sigma> V \<phi> \<noteq> undeff \<Longrightarrow> usubstappf \<sigma> U \<phi> = usubstappf \<sigma> V \<phi>"
  using usubstappf_and_usubstappp_det by simp

lemma usubstappp_det: "snd(usubstappp \<sigma> U \<alpha>) \<noteq> undefg \<Longrightarrow> snd(usubstappp \<sigma> V \<alpha>) \<noteq> undefg \<Longrightarrow> snd(usubstappp \<sigma> U \<alpha>) = snd(usubstappp \<sigma> V \<alpha>)"
  using usubstappf_and_usubstappp_det by simp


subsection \<open>Uniform Substitutions are Antimonotone in Taboos\<close>


lemma usubst_taboos_mon: "fst(usubstappp \<sigma> U \<alpha>) \<supseteq> U"
proof (induction \<alpha> arbitrary: U rule: game_induct)
  case (Game a)
  then show ?case by (cases "SGames \<sigma> a") (auto)
next
  case (Assign x \<theta>)
  then show ?case by fastforce
next
  case (ODE x \<theta>)
  then show ?case by fastforce
next
  case (Test \<phi>)
  then show ?case by fastforce
next
  case (Choice \<alpha> \<beta>)
  then show ?case by fastforce
next
  case (Compose \<alpha> \<beta>)
  then show ?case by fastforce
next
  case (Loop \<alpha>)
  then show ?case by fastforce
next
  case (Dual \<alpha>)
  then show ?case by fastforce
qed

lemma fst_pair [simp]: "fst (a,b) = a" 
  by simp

lemma snd_pair [simp]: "snd (a,b) = b" 
  by simp

  
lemma usubstappt_antimon: "V\<subseteq>U \<Longrightarrow> usubstappt \<sigma> U \<theta> \<noteq> undeft \<Longrightarrow>
  usubstappt \<sigma> U \<theta> = usubstappt \<sigma> V \<theta>"
proof (induction \<theta>)
  case (Var x)
  then show ?case by simp
next
  case (Number x)
  then show ?case by simp
next
  case (Const f)
  then show ?case
    (*by (smt disjoint_iff_not_equal option.case_eq_if set_rev_mp usappconst_def usubstappt.simps(3))*)
  proof - (*sledgehammer*)
    have f1: "usubstappt \<sigma> U (Const f) = (case SConst \<sigma> f of None \<Rightarrow> Aterm (Const f) | Some t \<Rightarrow> if FVT t \<inter> U = {} then Aterm t else undeft)"
      by (simp add: usappconst_def)
    have f2: "\<forall>z f za. if za = undeft then (case za of None \<Rightarrow> z::trm option | Some x \<Rightarrow> f x) = z else (case za of None \<Rightarrow> z | Some x \<Rightarrow> f x) = f (the za)"
      by force
    then have "SConst \<sigma> f \<noteq> undeft \<longrightarrow> (if FVT (the (SConst \<sigma> f)) \<inter> U = {} then Aterm (the (SConst \<sigma> f)) else undeft) = usappconst \<sigma> U f"
      using usappconst_def by presburger
    then have f3: "SConst \<sigma> f \<noteq> undeft \<longrightarrow> FVT (the (SConst \<sigma> f)) \<inter> U = {}"
      by (metis (no_types) Const.prems(2) usubstappt.simps(3))
    have f4: "\<forall>V Va. (V \<inter> Va = {}) = (\<forall>v. (v::variable) \<in> V \<longrightarrow> (\<forall>va. va \<in> Va \<longrightarrow> v \<noteq> va))"
      by blast
    { assume "usubstappt \<sigma> U (Const f) \<noteq> usubstappt \<sigma> V (Const f)"
      then have "usubstappt \<sigma> U (Const f) \<noteq> (case SConst \<sigma> f of None \<Rightarrow> Aterm (Const f) | Some t \<Rightarrow> if FVT t \<inter> V = {} then Aterm t else undeft)"
        by (simp add: usappconst_def)
      then have "SConst \<sigma> f \<noteq> undeft"
        using f2 f1 by metis
      then have "SConst \<sigma> f \<noteq> undeft \<and> FVT (the (SConst \<sigma> f)) \<inter> V = {}"
        using f4 f3 by (meson Const.prems(1) subsetD)
      then have ?thesis
        using f3 f2 usappconst_def usubstappt.simps(3) by presburger }
    then show ?thesis
      by blast
  qed 
next
  case (Func f \<theta>)
  then show ?case using usubstappt_func
      (*by (smt disjoint_iff_not_equal option.case_eq_if subset_iff usubstappt.simps(4))*)
  proof - (*sledgehammer*)
    have f1: "(case usubstappt \<sigma> U \<theta> of None \<Rightarrow> undeft | Some t \<Rightarrow> (case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f t) | Some ta \<Rightarrow> if FVT ta \<inter> U = {} then usubstappt (dotsubstt t) {} ta else undeft)) \<noteq> undeft"
      using Func.prems(2) by fastforce
    have f2: "\<forall>z f za. if za = undeft then (case za of None \<Rightarrow> z::trm option | Some x \<Rightarrow> f x) = z else (case za of None \<Rightarrow> z | Some x \<Rightarrow> f x) = f (the za)"
      by fastforce
    then have f3: "usubstappt \<sigma> U \<theta> \<noteq> undeft"
      using f1 by meson
    then have f4: "(case usubstappt \<sigma> U \<theta> of None \<Rightarrow> undeft | Some t \<Rightarrow> (case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f t) | Some ta \<Rightarrow> if FVT ta \<inter> U = {} then usubstappt (dotsubstt t) {} ta else undeft)) = (case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f (the (usubstappt \<sigma> U \<theta>))) | Some t \<Rightarrow> if FVT t \<inter> U = {} then usubstappt (dotsubstt (the (usubstappt \<sigma> U \<theta>))) {} t else undeft)"
      using f2 by presburger
    have f5: "usubstappt \<sigma> U \<theta> = undeft \<or> usubstappt \<sigma> U \<theta> = usubstappt \<sigma> V \<theta>"
      using Func.IH Func.prems(1) by fastforce
    have "SFuncs \<sigma> f \<noteq> undeft \<longrightarrow> (if FVT (the (SFuncs \<sigma> f)) \<inter> U = {} then usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SFuncs \<sigma> f)) else undeft) = (case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f (the (usubstappt \<sigma> V \<theta>))) | Some t \<Rightarrow> if FVT t \<inter> U = {} then usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} t else undeft)"
      using f2 by presburger
    then have "SFuncs \<sigma> f \<noteq> undeft \<longrightarrow> (if FVT (the (SFuncs \<sigma> f)) \<inter> U = {} then usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SFuncs \<sigma> f)) else undeft) = usubstappt \<sigma> U (trm.Func f \<theta>)"
      using f5 f4 f3 usubstappt.simps(4) by presburger
    then have f6: "SFuncs \<sigma> f \<noteq> undeft \<longrightarrow> FVT (the (SFuncs \<sigma> f)) \<inter> U = {}"
      by (metis (no_types) Func.prems(2))
    then have f7: "SFuncs \<sigma> f \<noteq> undeft \<longrightarrow> V \<subseteq> - FVT (the (SFuncs \<sigma> f))"
      using Func.prems(1) by blast
    have f8: "(case usubstappt \<sigma> V \<theta> of None \<Rightarrow> undeft | Some t \<Rightarrow> (case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f t) | Some ta \<Rightarrow> if FVT ta \<inter> V = {} then usubstappt (dotsubstt t) {} ta else undeft)) = (case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f (the (usubstappt \<sigma> V \<theta>))) | Some t \<Rightarrow> if FVT t \<inter> V = {} then usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} t else undeft)"
      using f5 f3 f2 by presburger
    have "SFuncs \<sigma> f \<noteq> undeft \<longrightarrow> usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SFuncs \<sigma> f)) = (case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f (the (usubstappt \<sigma> V \<theta>))) | Some t \<Rightarrow> if FVT t \<inter> U = {} then usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} t else undeft)"
      using f6 f2 by presburger
    then have f9: "SFuncs \<sigma> f \<noteq> undeft \<longrightarrow> usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SFuncs \<sigma> f)) = usubstappt \<sigma> U (trm.Func f \<theta>)"
      using f5 f4 f3 usubstappt.simps(4) by presburger
    { assume "usubstappt \<sigma> U (trm.Func f \<theta>) \<noteq> usubstappt \<sigma> V (trm.Func f \<theta>)"
      moreover
      { assume "(case SFuncs \<sigma> f of None \<Rightarrow> Aterm (trm.Func f (the (usubstappt \<sigma> V \<theta>))) | Some t \<Rightarrow> if FVT t \<inter> V = {} then usubstappt (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} t else undeft) \<noteq> Aterm (trm.Func f (the (usubstappt \<sigma> V \<theta>)))"
        then have "SFuncs \<sigma> f \<noteq> undeft"
          using f2 by meson }
      ultimately have "SFuncs \<sigma> f \<noteq> undeft"
        using f5 f3 by fastforce
      then have ?thesis
        using f9 f8 f7 f2 by (simp add: disjoint_eq_subset_Compl inf.commute) }
    then show ?thesis
      by blast
  qed
next
  case (Plus \<theta>1 \<theta>2)
  then show ?case using Pluso_undef by auto 
next
  case (Times \<theta>1 \<theta>2)
  then show ?case using Timeso_undef by auto
next
  case (Differential \<theta>)
  then show ?case using Differentialo_undef by auto
qed

text \<open>Uniform Substitutions of Games have monotone taboo output\<close>

lemma usubstappp_fst_mon: "U\<subseteq>V \<Longrightarrow> fst(usubstappp \<sigma> U \<alpha>) \<subseteq> fst(usubstappp \<sigma> V \<alpha>)"
proof (induction \<alpha> arbitrary: U V rule: game_induct)
  case (Game a)
  then show ?case by (cases "SGames \<sigma> a") (auto)
next
  case (Assign x \<theta>)
  then show ?case by auto
next
  case (ODE x \<theta>)
  then show ?case by auto
next
  case (Test \<phi>)
  then show ?case by auto
next
  case (Choice \<alpha> \<beta>)
  then show ?case by (metis Un_mono fst_pair usubstappp_choice) 
next
  case (Compose \<alpha> \<beta>)
  then show ?case by (metis fst_pair usubstappp_compose) 
next
  case (Loop \<alpha>)
  then show ?case by (metis fst_pair usubstappp_loop) 
next
  case (Dual \<alpha>)
  then show ?case by (metis fst_pair usubstappp_dual) 
qed


lemma usubstappf_and_usubstappp_antimon: 
shows "V\<subseteq>U \<Longrightarrow> usubstappf \<sigma> U \<phi> \<noteq> undeff \<Longrightarrow> usubstappf \<sigma> U \<phi> = usubstappf \<sigma> V \<phi>"
and "V\<subseteq>U \<Longrightarrow> snd(usubstappp \<sigma> U \<alpha>) \<noteq> undefg \<Longrightarrow> snd(usubstappp \<sigma> U \<alpha>) = snd(usubstappp \<sigma> V \<alpha>)"
proof-
  have "V\<subseteq>U \<Longrightarrow> usubstappf \<sigma> U \<phi> \<noteq> undeff \<Longrightarrow> usubstappf \<sigma> V \<phi> \<noteq> undeff"
  and "V\<subseteq>U \<Longrightarrow> snd(usubstappp \<sigma> U \<alpha>) \<noteq> undefg \<Longrightarrow> snd(usubstappp \<sigma> V \<alpha>) \<noteq> undefg"
  proof (induction \<phi> and \<alpha> arbitrary: U V and U V)
    case (Pred p \<theta>)
    then show ?case using usubstappt_antimon usubstappf_pred
    (*by (smt Un_mono disjoint_eq_subset_Compl empty_subsetI inf.commute option.case_eq_if sup.absorb_iff1 sup.absorb_iff2 usubstappf.simps(1)) *)
      proof - (*sledgehammer*)
      have f1: "\<forall>v. v \<notin> V \<or> v \<in> U"
      using Pred.prems(1) by auto
      have f2: "\<forall>z f za. if za = undeff then (case za of None \<Rightarrow> z::fml option | Some x \<Rightarrow> f x) = z else (case za of None \<Rightarrow> z | Some x \<Rightarrow> f x) = f (the za)"
      by (simp add: option.case_eq_if)
      have f3: "(case usubstappt \<sigma> U \<theta> of None \<Rightarrow> undeff | Some t \<Rightarrow> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p t) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt t) {} f else undeff)) \<noteq> undeff"
      using Pred.prems(2) by auto
      have f4: "\<forall>z f za. if za = undeft then (case za of None \<Rightarrow> z::fml option | Some x \<Rightarrow> f x) = z else (case za of None \<Rightarrow> z | Some x \<Rightarrow> f x) = f (the za)"
      by (simp add: option.case_eq_if)
      then have f5: "usubstappt \<sigma> U \<theta> \<noteq> undeft"
      using f3 by meson
      then have f6: "(case usubstappt \<sigma> U \<theta> of None \<Rightarrow> undeff | Some t \<Rightarrow> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p t) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt t) {} f else undeff)) = (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> U \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> U \<theta>))) {} f else undeff)"
      using f4 by presburger
      have f7: "usubstappt \<sigma> U \<theta> = usubstappt \<sigma> V \<theta>"
      using f5 by (meson Pred.prems(1) usubstappt_antimon)
      then have f8: "SPreds \<sigma> p = undeff \<longrightarrow> usubstappf \<sigma> U (Pred p \<theta>) = usubstappf \<sigma> V (Pred p \<theta>)"
      using f2 usubstappf.simps(1) by presburger
      obtain vv :: "variable set \<Rightarrow> variable set \<Rightarrow> variable" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> (\<exists>v3. v3 \<in> x0 \<and> v2 = v3)) = (vv x0 x1 \<in> x1 \<and> (\<exists>v3. v3 \<in> x0 \<and> vv x0 x1 = v3))"
      by moura
      then obtain vva :: "variable set \<Rightarrow> variable set \<Rightarrow> variable" where
      f9: "\<forall>V Va. (V \<inter> Va \<noteq> {} \<or> (\<forall>v. v \<notin> V \<or> (\<forall>va. va \<notin> Va \<or> v \<noteq> va))) \<and> (V \<inter> Va = {} \<or> vv Va V \<in> V \<and> vva Va V \<in> Va \<and> vv Va V = vva Va V)"
      by moura
      then have f10: "(FVF (the (SPreds \<sigma> p)) \<inter> V \<noteq> {} \<or> (\<forall>v. v \<notin> FVF (the (SPreds \<sigma> p)) \<or> (\<forall>va. va \<notin> V \<or> v \<noteq> va))) \<and> (FVF (the (SPreds \<sigma> p)) \<inter> V = {} \<or> vv V (FVF (the (SPreds \<sigma> p))) \<in> FVF (the (SPreds \<sigma> p)) \<and> vva V (FVF (the (SPreds \<sigma> p))) \<in> V \<and> vv V (FVF (the (SPreds \<sigma> p))) = vva V (FVF (the (SPreds \<sigma> p))))"
      by presburger
      { assume "vv V (FVF (the (SPreds \<sigma> p))) \<notin> FVF (the (SPreds \<sigma> p)) \<or> vva V (FVF (the (SPreds \<sigma> p))) \<notin> V \<or> vv V (FVF (the (SPreds \<sigma> p))) \<noteq> vva V (FVF (the (SPreds \<sigma> p)))"
        moreover
        { assume "(if FVF (the (SPreds \<sigma> p)) \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff) \<noteq> undeff"
          moreover
          { assume "(if FVF (the (SPreds \<sigma> p)) \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff) \<noteq> usubstappf \<sigma> V (Pred p \<theta>)"
            then have "(case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff) \<noteq> (if FVF (the (SPreds \<sigma> p)) \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff)"
            using f7 f5 f4 by simp
            then have "SPreds \<sigma> p = undeff"
            using f2 by (metis (no_types, lifting) \<open>(if FVF (the (SPreds \<sigma> p)) \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff) \<noteq> usubstappf \<sigma> V (Pred p \<theta>)\<close> calculation f5 f7 option.collapse usubstappf_pred)}
          ultimately have "usubstappf \<sigma> V (Pred p \<theta>) = undeff \<longrightarrow> SPreds \<sigma> p = undeff"
          by fastforce }
        moreover
        { assume "usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) \<noteq> usubstappf \<sigma> U (Pred p \<theta>)"
          then have "usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) \<noteq> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> U \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> U \<theta>))) {} f else undeff)"
          using f6 by simp
          then have "usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) \<noteq> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff)"
          using f7 by (metis f7)
          moreover
          { assume "(case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff) \<noteq> (if FVF (the (SPreds \<sigma> p)) \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff)"
            then have "SPreds \<sigma> p = undeff"
            using f2  by (metis (no_types, lifting) Pred.prems(2) \<open>usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) \<noteq> usubstappf \<sigma> U (Pred p \<theta>)\<close> f5 f7 option.collapse usubstappf_pred usubstappf_pred2)}
          ultimately have "FVF (the (SPreds \<sigma> p)) \<inter> U = {} \<longrightarrow> SPreds \<sigma> p = undeff"
          by force }
        ultimately have "FVF (the (SPreds \<sigma> p)) \<inter> U = {} \<and> usubstappf \<sigma> V (Pred p \<theta>) = undeff \<longrightarrow> SPreds \<sigma> p = undeff"
        using f10 by (metis Pred.prems(2)) }
      moreover
      { assume "FVF (the (SPreds \<sigma> p)) \<inter> U \<noteq> {}"
        then have "(if FVF (the (SPreds \<sigma> p)) \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff) \<noteq> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> U \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> U \<theta>))) {} f else undeff)"
        using f6 Pred.prems(2) by auto
        then have "(if FVF (the (SPreds \<sigma> p)) \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff) \<noteq> (case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff)"
        using f7 by (metis  \<open>FVF (the (SPreds \<sigma> p)) \<inter> U \<noteq> {}\<close>)
        then have "(case SPreds \<sigma> p of None \<Rightarrow> Afml (Pred p (the (usubstappt \<sigma> V \<theta>))) | Some f \<Rightarrow> if FVF f \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} f else undeff) \<noteq> (if FVF (the (SPreds \<sigma> p)) \<inter> U = {} then usubstappf (dotsubstt (the (usubstappt \<sigma> V \<theta>))) {} (the (SPreds \<sigma> p)) else undeff)"
        by simp
        then have "SPreds \<sigma> p = undeff"
        using f2
          proof -
          show ?thesis
          by (metis (no_types) Pred.prems(2) \<open>FVF (the (SPreds \<sigma> p)) \<inter> U \<noteq> {}\<close> option.discI option.expand option.sel usubstappf_pred2)
          qed }
      ultimately have "usubstappf \<sigma> V (Pred p \<theta>) = undeff \<longrightarrow> SPreds \<sigma> p = undeff"
      using f9 f1 by meson
      then show ?thesis
      using f8 by (metis (full_types) Pred.prems(2))
      qed

    next
      case (Geq \<theta> \<eta>)
      then show ?case using usubstappt_antimon using Geqo_undef by auto
    next
      case (Not x)
      then show ?case using Noto_undef by auto
    next
      case (And x1 x2)
      then show ?case using Ando_undef by auto
    next
      case (Exists x1 x2)
      then show ?case using Existso_undef
        by (metis (no_types, lifting) Un_mono subsetI usubstappf.simps(5))
    next
      case (Diamond x1 x2)
      then show ?case using Diamondo_undef usubstappf.simps(6) usubstappp_fst_mon by metis
    next
      case (Game a)
      then show ?case by (cases "SGames \<sigma> a") (auto)
    next
      case (Assign x \<theta>)
      then show ?case using usubstappt_antimon by (metis Assigno_undef snd_conv usubstappp.simps(2))
    next
      case (ODE x \<theta>)
      then show ?case using usubstappt_antimon ODEo_undef
        by (metis (no_types, hide_lams) Un_mono order_refl snd_conv usubstappp.simps(8))
    next
      case (Test \<phi>)
      then show ?case by (metis Testo_undef snd_conv usubstappp.simps(3))
    next
      case (Choice \<alpha> \<beta>)
      then show ?case using Choiceo_undef by auto 
    next
      case (Compose \<alpha> \<beta>)
      then show ?case 
        using usubstappp_compose[where \<sigma>=\<sigma> and U=U and \<alpha>=\<alpha> and \<beta>=\<beta>] usubstappp_compose[where \<sigma>=\<sigma> and U=V and \<alpha>=\<alpha> and \<beta>=\<beta>]
          Composeo_undef[where \<alpha>=\<open>snd (usubstappp \<sigma> U \<alpha>)\<close> and \<beta>=\<open>snd (usubstappp \<sigma> (fst (usubstappp \<sigma> U \<alpha>)) \<beta>)\<close>]
          Composeo_undef[where \<alpha>=\<open>snd (usubstappp \<sigma> V \<alpha>)\<close> and \<beta>=\<open>snd (usubstappp \<sigma> (fst (usubstappp \<sigma> V \<alpha>)) \<beta>)\<close>]
          snd_conv usubstappp_fst_mon by metis
          (*proof-
            from Compose have ca: "snd (usubstappp \<sigma> U (\<alpha> ;; \<beta>)) \<noteq> undefg" by simp
            have decU: "snd (usubstappp \<sigma> U (\<alpha> ;; \<beta>)) = Composeo (snd(usubstappp \<sigma> U \<alpha>)) (snd(usubstappp \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<beta>))" using usubstappp_compose by simp
            have decV: "snd (usubstappp \<sigma> V (\<alpha> ;; \<beta>)) = Composeo (snd(usubstappp \<sigma> V \<alpha>)) (snd(usubstappp \<sigma> (fst(usubstappp \<sigma> V \<alpha>)) \<beta>))" using usubstappp_compose by simp
            from Compose have fact1: "snd(usubstappp \<sigma> V \<alpha>) \<noteq> undefg" using Composeo_undef by auto 
            from Compose have fact2: "snd(usubstappp \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<beta>) \<noteq> undefg" using Composeo_undef by auto 
            have rel: "fst(usubstappp \<sigma> V \<alpha>) \<subseteq> fst(usubstappp \<sigma> U \<alpha>)" using \<open>V\<subseteq>U\<close> usubstappp_fst_mon by auto
            from Compose have fact3: "snd(usubstappp \<sigma> (fst(usubstappp \<sigma> V \<alpha>)) \<beta>) \<noteq> undefg" using fact2 rel by auto 
            then show ?thesis by (simp add: Composeo_undef fact1)
          qed*)
    next
      case (Loop \<alpha>)
      then show ?case using Loopo_undef snd_conv usubstappp.simps(6) usubstappp_fst_mon by metis
    next
      case (Dual \<alpha>)
      then show ?case by (metis Dualo_undef snd_conv usubstappp.simps(7))
    qed
    from this show "V\<subseteq>U \<Longrightarrow> usubstappf \<sigma> U \<phi> \<noteq> undeff \<Longrightarrow> usubstappf \<sigma> U \<phi> = usubstappf \<sigma> V \<phi>"
      and "V\<subseteq>U \<Longrightarrow> snd(usubstappp \<sigma> U \<alpha>) \<noteq> undefg \<Longrightarrow> snd(usubstappp \<sigma> U \<alpha>) = snd(usubstappp \<sigma> V \<alpha>)" using usubstappf_and_usubstappp_det by auto
  qed

lemma usubstappf_antimon: "V\<subseteq>U \<Longrightarrow> usubstappf \<sigma> U \<phi> \<noteq> undeff \<Longrightarrow> usubstappf \<sigma> U \<phi> = usubstappf \<sigma> V \<phi>"
  using usubstappf_and_usubstappp_antimon by simp

lemma usubstappp_antimon: "V\<subseteq>U \<Longrightarrow> snd(usubstappp \<sigma> U \<alpha>) \<noteq> undefg \<Longrightarrow> snd(usubstappp \<sigma> U \<alpha>) = snd(usubstappp \<sigma> V \<alpha>)"
  using usubstappf_and_usubstappp_antimon by simp

  
subsection \<open>Taboo Lemmas\<close>

lemma usubstappp_loop_conv: "snd (usubstappp \<sigma> U (Loop \<alpha>)) \<noteq> undefg \<Longrightarrow>
  snd(usubstappp \<sigma> U \<alpha>) \<noteq> undefg \<and>
  snd(usubstappp \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<alpha>) \<noteq> undefg"
  (*using usubstappp_loop Loopo_undef*)
proof
  assume a: "snd (usubstappp \<sigma> U (Loop \<alpha>)) \<noteq> undefg"
  have fact: "fst(usubstappp \<sigma> U \<alpha>) \<supseteq> U" using usubst_taboos_mon by simp
  show "snd(usubstappp \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<alpha>) \<noteq> undefg" using a usubstappp_loop Loopo_undef by simp
  then show "snd(usubstappp \<sigma> U \<alpha>) \<noteq> undefg" using a usubstappp_loop Loopo_undef fact usubstappp_antimon by auto
qed


text \<open>Lemma 13 of \<^url>\<open>http://arxiv.org/abs/1902.07230\<close>\<close>

lemma usubst_taboos: "snd(usubstappp \<sigma> U \<alpha>)\<noteq>undefg \<Longrightarrow> fst(usubstappp \<sigma> U \<alpha>) \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U \<alpha>)))"
proof (induction \<alpha> arbitrary: U rule: game_induct)
  case (Game a)
  then show ?case by (cases "SGames \<sigma> a") (auto)
next
  case (Assign x \<theta>)
  then show ?case 
    using BVG_assign Assigno_undef
    by (metis (no_types, lifting) Assigno.elims BVG_assign_other fst_pair option.sel singletonI snd_pair subsetI union_or usubstappp.simps(2))
next
  case (ODE x \<theta>)
  then show ?case
    using BVG_ODE ODEo_undef
    by (metis (no_types, lifting) ODEo.elims Un_least fst_pair option.sel snd_conv sup.coboundedI2 usubst_taboos_mon usubstappp.simps(8))
next
  case (Test p)
  then show ?case
    using BVG_test Testo_undef usubst_taboos_mon by auto 
next
  case (Choice \<alpha> \<beta>)
  then show ?case (*using usubstappp.simps Product_Type.fst_conv Product_Type.snd_conv BVG_choice*)
  proof-
    from Choice have IHa: "fst(usubstappp \<sigma> U \<alpha>) \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U \<alpha>)))" by (simp add: Choiceo_undef)
    from Choice have IHb: "fst(usubstappp \<sigma> U \<beta>) \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U \<beta>)))" by (simp add: Choiceo_undef)
    have fact: "BVG(the (snd(usubstappp \<sigma> U \<alpha>))) \<union> BVG(the (snd(usubstappp \<sigma> U \<beta>))) \<supseteq> BVG(the (snd(usubstappp \<sigma> U (Choice \<alpha> \<beta>))))" using BVG_choice
        (*by (smt Choice.prems Choiceo.simps(1) Choiceo_undef option.collapse option.sel snd_pair usubstappp_choice)*)
    proof -
      have "Agame (the (snd (usubstappp \<sigma> U \<alpha>)) \<union>\<union> the (snd (usubstappp \<sigma> U \<beta>))) = Choiceo (snd (usubstappp \<sigma> U \<alpha>)) (snd (usubstappp \<sigma> U \<beta>))"
        by (metis (no_types) Choice.prems Choiceo.simps(1) option.collapse usubstappp_choice_conv)
      then show ?thesis
        by (metis (no_types) BVG_choice Choice.prems Pair_inject option.collapse option.inject surjective_pairing usubstappp.simps(4))
    qed
    from IHa and IHb have "fst(usubstappp \<sigma> U \<alpha>) \<union> fst(usubstappp \<sigma> U \<beta>) \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U \<alpha>))) \<union> BVG(the (snd(usubstappp \<sigma> U \<beta>)))" by auto
    then have "fst(usubstappp \<sigma> U (Choice \<alpha> \<beta>)) \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U \<alpha>))) \<union> BVG(the (snd(usubstappp \<sigma> U \<beta>)))" using usubstappp.simps Let_def by auto
    then show "fst(usubstappp \<sigma> U (Choice \<alpha> \<beta>)) \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U (Choice \<alpha> \<beta>))))" using usubstappp.simps fact by auto
  qed
next
  case (Compose \<alpha> \<beta>)
  then show ?case
  proof-
    let ?V = "fst(usubstappp \<sigma> U \<alpha>)"
    let ?W = "fst(usubstappp \<sigma> ?V \<beta>)"
    from Compose have IHa: "?V \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U \<alpha>)))" by (simp add: Composeo_undef)
    from Compose have IHb: "?W \<supseteq> ?V \<union> BVG(the (snd(usubstappp \<sigma> ?V \<beta>)))" by (simp add: Composeo_undef)
    have fact: "BVG(the (snd(usubstappp \<sigma> U \<alpha>))) \<union> BVG(the (snd(usubstappp \<sigma> ?V \<beta>))) \<supseteq> BVG(the (snd(usubstappp \<sigma> U (Compose \<alpha> \<beta>))))" using usubstappp.simps BVG_compose
        (*by (smt Compose.prems Composeo.simps(1) Composeo_undef option.collapse option.sel snd_pair)*)
    proof -
      have f1: "\<forall>z. z = undefg \<or> Agame (the z) = z"
        using option.collapse by blast
      then have "Agame (the (snd (usubstappp \<sigma> U \<alpha>)) ;; the (snd (usubstappp \<sigma> (fst (usubstappp \<sigma> U \<alpha>)) \<beta>))) = snd (usubstappp \<sigma> U (\<alpha> ;; \<beta>))"
        using Compose.prems Composeo_undef by auto
      then show ?thesis
        using f1 by (metis (no_types) BVG_compose Compose.prems option.inject)
    qed
    have "?W \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U \<alpha>))) \<union> BVG(the (snd(usubstappp \<sigma> ?V \<beta>)))" using usubstappp.simps Let_def IHa IHb by auto
    then have "?W \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U (Compose \<alpha> \<beta>))))" using fact by auto
    then show "fst(usubstappp \<sigma> U (Compose \<alpha> \<beta>)) \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U (Compose \<alpha> \<beta>))))" using usubstappp.simps Let_def by simp
  qed
next
  case (Loop \<alpha>)
  then show ?case
  proof-
    let ?V = "fst(usubstappp \<sigma> U \<alpha>)"
    let ?W = "fst(usubstappp \<sigma> ?V \<alpha>)"
    from Loop have def\<alpha>: "snd(usubstappp \<sigma> U \<alpha>) \<noteq> undefg" using usubstappp_loop_conv by simp
    from Loop have IHdef: "?V \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U \<alpha>)))" 
      using def\<alpha> usubstappp_loop[where \<sigma>=\<sigma> and U=U and \<alpha>=\<alpha>] Loopo_undef[where \<alpha>=\<open>snd (usubstappp \<sigma> (fst (usubstappp \<sigma> U \<alpha>)) \<alpha>)\<close>]   by auto
    from Loop have IH: "?W \<supseteq> ?V \<union> BVG(the (snd(usubstappp \<sigma> ?V \<alpha>)))" by (simp add: Loopo_undef)
    then have Vfix: "?V \<supseteq> BVG(the (snd(usubstappp \<sigma> ?V \<alpha>)))"
      using usubstappp_det by (metis IHdef Loop.prems le_sup_iff usubstappp_loop_conv)
    then have "?V \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U (Loop \<alpha>))))"
      using usubstappp.simps Vfix IHdef BVG_loop usubst_taboos_mon usubstappp_loop_conv
        (*by (smt Loop.prems Loopo.simps(1) Un_mono option.collapse option.sel snd_pair sup.absorb_iff1)*)
    proof - (*sledgehammer*)
      have f1: "\<forall>z. z = undefg \<or> Agame (the z) = z"
        using option.collapse by blast
      have "snd (usubstappp \<sigma> U \<alpha>) \<noteq> undefg \<and> snd (usubstappp \<sigma> (fst (usubstappp \<sigma> U \<alpha>)) \<alpha>) \<noteq> undefg"
        using Loop.prems usubstappp_loop_conv by blast
      then have "Agame (Loop (the (snd (usubstappp \<sigma> (fst (usubstappp \<sigma> U \<alpha>)) \<alpha>)))) = snd (usubstappp \<sigma> U (Loop \<alpha>))"
        by force
      then show ?thesis
        using f1 by (metis (no_types) BVG_loop Loop.prems Vfix option.inject sup.absorb_iff1 sup.mono usubst_taboos_mon)
    qed
    then show "fst(usubstappp \<sigma> U (Loop \<alpha>)) \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U (Loop \<alpha>))))" using usubstappp.simps Let_def by simp
  qed
next
  case (Dual \<alpha>)
  then show ?case
    (*using BVG_dual usubstappp.simps Let_def by auto*)
  proof-
    let ?V = "fst(usubstappp \<sigma> U \<alpha>)"
    from Dual have IH: "?V \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U \<alpha>)))" by (simp add: Dualo_undef)
    have fact: "BVG(the (snd(usubstappp \<sigma> U \<alpha>))) \<supseteq> BVG(the (snd(usubstappp \<sigma> U (Dual \<alpha>))))" using usubstappp.simps BVG_dual
      by (metis (no_types, lifting) Dual.prems Dualo.simps(1) Dualo.simps(2) option.collapse option.sel snd_pair)
    then have "?V \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U (Dual \<alpha>))))" using IH fact by auto
    then show "fst(usubstappp \<sigma> U (Dual \<alpha>)) \<supseteq> U \<union> BVG(the (snd(usubstappp \<sigma> U (Dual \<alpha>))))" using usubstappp.simps Let_def by simp
  qed
qed



subsection \<open>Substitution Adjoints\<close>

text \<open>Modified interpretation \<open>repI I f d\<close> replaces the interpretation of constant function \<open>f\<close> in the interpretation \<open>I\<close> with \<open>d\<close>\<close>
definition repc :: " interp \<Rightarrow> ident \<Rightarrow> real \<Rightarrow> interp"
  where "repc I f d \<equiv>  mkinterp((\<lambda>c. if c = f then d else Consts I c), Funcs I, Preds I, Games I)"

lemma repc_consts [simp]: "Consts (repc I f d) c = (if (c=f) then d else Consts I c)"
  unfolding repc_def by auto
lemma repc_funcs [simp]: "Funcs (repc I f d) = Funcs I"
  unfolding repc_def by simp
lemma repc_preds [simp]: "Preds (repc I f d) = Preds I"
  unfolding repc_def by simp
lemma repc_games [simp]: "Games (repc I f d) = Games I"
  unfolding repc_def by (simp add: mon_mono)
  
lemma adjoint_stays_mon: "mono (case SGames \<sigma> a of None \<Rightarrow> Games I a | Some r \<Rightarrow> \<lambda>X. game_sem I r X)"
  using game_sem_mono game_sem.simps(1)
  by (metis disjE_realizer2 option.case_distrib) 
  (*proof -
  have "\<forall>z p b i f. (mono (case z of None \<Rightarrow> f | Some x \<Rightarrow> game_sem i x) \<or> \<not> (case z of None \<Rightarrow> b | Some x \<Rightarrow> p x)) \<or> \<not> mono f"
  by (metis (no_types) disjE_realizer2 game_sem_mono)
  then show ?thesis
  by (metis (no_types) game_sem.simps(1) game_sem_mono option.case_distrib)
  qed*)

text \<open>adjoint interpretation \<open>adjoint \<sigma> I \<omega>\<close> to \<open>\<sigma>\<close> of interpretation \<open>I\<close> in state \<open>\<omega>\<close>\<close> 

definition adjoint:: "usubst \<Rightarrow> (interp \<Rightarrow> state \<Rightarrow> interp)"
where "adjoint \<sigma> I \<omega> = mkinterp(
         (\<lambda>f. (case SConst \<sigma> f of None \<Rightarrow> Consts I f| Some r \<Rightarrow> term_sem I r \<omega>)),
         (\<lambda>f. (case SFuncs \<sigma> f of None \<Rightarrow> Funcs I f | Some r \<Rightarrow> \<lambda>d. term_sem (repc I dotid d) r \<omega>)),
         (\<lambda>p. (case SPreds \<sigma> p of None \<Rightarrow> Preds I p | Some r \<Rightarrow> \<lambda>d. \<omega>\<in>fml_sem (repc I dotid d) r)),
         (\<lambda>a. (case SGames \<sigma> a of None \<Rightarrow> Games I a | Some r \<Rightarrow> \<lambda>X. game_sem I r X))
  )"


paragraph \<open>Simple Observations about Adjoints\<close>
  
lemma adjoint_consts: "Consts (adjoint \<sigma> I \<omega>) f = term_sem I (case SConst \<sigma> f of Some r \<Rightarrow> r | None \<Rightarrow> Const f) \<omega>"
  unfolding adjoint_def by (cases "SConst \<sigma> f=None") (auto)

lemma adjoint_funcs: "Funcs (adjoint \<sigma> I \<omega>) f = (case SFuncs \<sigma> f of None \<Rightarrow> Funcs I f | Some r \<Rightarrow> \<lambda>d. term_sem (repc I dotid d) r \<omega>)"
  unfolding adjoint_def by auto

lemma adjoint_funcs_match: "SFuncs \<sigma> f=Some r \<Longrightarrow> Funcs (adjoint \<sigma> I \<omega>) f = (\<lambda>d. term_sem (repc I dotid d) r \<omega>)"
  using adjoint_funcs by auto

lemma adjoint_funcs_skip: "SFuncs \<sigma> f=None \<Longrightarrow> Funcs (adjoint \<sigma> I \<omega>) f = Funcs I f"
  using adjoint_funcs by auto

lemma adjoint_preds: "Preds (adjoint \<sigma> I \<omega>) p = (case SPreds \<sigma> p of None \<Rightarrow> Preds I p | Some r \<Rightarrow> \<lambda>d. \<omega>\<in>fml_sem (repc I dotid d) r)"
  unfolding adjoint_def by auto

lemma adjoint_preds_skip: "SPreds \<sigma> p=None \<Longrightarrow> Preds (adjoint \<sigma> I \<omega>) p = Preds I p"
  using adjoint_preds by simp

lemma adjoint_preds_match: "SPreds \<sigma> p=Some r \<Longrightarrow> Preds (adjoint \<sigma> I \<omega>) p = (\<lambda>d. \<omega>\<in>fml_sem (repc I dotid d) r)"
  using adjoint_preds by simp

lemma adjoint_games [simp]: "Games (adjoint \<sigma> I \<omega>) a = (case SGames \<sigma> a of None \<Rightarrow> Games I a | Some r \<Rightarrow> \<lambda>X. game_sem I r X)"
  unfolding adjoint_def using adjoint_stays_mon Games_mkinterp by simp 

lemma adjoint_dotsubstt: "adjoint (dotsubstt \<theta>) I \<omega> = repc I dotid (term_sem I \<theta> \<omega>)"
  (*unfolding adjoint_def dotsubstt_def adjoint_consts adjoint_funcs_skip adjoint_preds adjoint_games*)
proof-
  let ?lhs = "adjoint (dotsubstt \<theta>) I \<omega>"
  let ?rhs = "repc I dotid (term_sem I \<theta> \<omega>)"
  have feq: "Funcs ?lhs = Funcs ?rhs" using repc_funcs adjoint_funcs dotsubstt_def by auto
  moreover have peq: "Preds ?lhs = Preds ?rhs" using repc_preds adjoint_preds dotsubstt_def by auto
  moreover have geq: "Games ?lhs = Games ?rhs" using repc_games adjoint_games dotsubstt_def by auto
  moreover have ceq: "Consts ?lhs = Consts ?rhs" using repc_consts  adjoint_consts dotsubstt_def by auto
  show ?thesis using mkinterp_eq[where I=\<open>?lhs\<close> and J=\<open>?rhs\<close>] feq peq geq ceq by simp
qed

  
subsection \<open>Uniform Substitution for Terms\<close>

text \<open>Lemma 15 of \<^url>\<open>http://arxiv.org/abs/1902.07230\<close>\<close>
theorem usubst_term: "Uvariation \<nu> \<omega> U \<Longrightarrow> usubstappt \<sigma> U \<theta>\<noteq>undeft \<Longrightarrow>
    term_sem I (the (usubstappt \<sigma> U \<theta>)) \<nu> = term_sem (adjoint \<sigma> I \<omega>) \<theta> \<nu>"
proof- 
  assume vaouter: "Uvariation \<nu> \<omega> U"
  assume defouter: "usubstappt \<sigma> U \<theta>\<noteq>undeft"
  show "usubstappt \<sigma> U \<theta>\<noteq>undeft \<Longrightarrow> term_sem I (the (usubstappt \<sigma> U \<theta>)) \<nu> = term_sem (adjoint \<sigma> I \<omega>) \<theta> \<nu>" for \<sigma> \<theta>
    using vaouter proof (induction arbitrary: \<nu> \<omega> rule: usubstappt_induct)
    case (Var \<sigma> U x)
    then show ?case by simp
  next
    case (Number \<sigma> U r)
    then show ?case by simp
  next
    case (Const \<sigma> U f)
    then show ?case 
    proof (cases "SConst \<sigma> f")
      case None
      then show ?thesis using adjoint_consts by (simp add: usappconst_def)
    next
      case (Some r)
      then have varcond: "FVT(r)\<inter>U={}" using Const usubstappt_const usubstappt_const_conv by (metis option.inject option.simps(3))
      from Some have "term_sem I (the (usubstappt \<sigma> U (Const f))) \<nu> = term_sem I r \<nu>" by (simp add: varcond)
      also have "... = term_sem I r \<omega>" using Const coincidence_term_cor[of \<nu> \<omega> U r] varcond by simp
      also have "... = Consts (adjoint \<sigma> I \<omega>) f" using Some adjoint_consts by simp
      also have "... = term_sem (adjoint \<sigma> I \<omega>) (Const f) \<nu>" by auto
      finally show "term_sem I (the (usubstappt \<sigma> U (Const f))) \<nu> = term_sem (adjoint \<sigma> I \<omega>) (Const f) \<nu>" .
    qed
  next
    case (FuncMatch \<sigma> U f \<theta>)
    then have va: "Uvariation \<nu> \<omega> U" by simp
    then show ?case
    proof (cases "SFuncs \<sigma> f")
      case None 
      from FuncMatch and None have IHsubterm: "term_sem I (the (usubstappt \<sigma> U \<theta>)) \<nu> = term_sem (adjoint \<sigma> I \<omega>) \<theta> \<nu>" using va
        by (simp add: FuncMatch.IH(1) usubstappt_func_conv)
      from None show ?thesis using usubstappt_func IHsubterm adjoint_funcs
        by (metis (no_types, lifting) FuncMatch.prems(1) option.case_eq_if option.sel term_sem.simps(4) usubstappt.simps(4))
    next
      case (Some r)
      then have varcond: "FVT(r)\<inter>U={}" using FuncMatch usubstappt_func usubstappt_func2 usubstappt_func_conv by meson
      from FuncMatch have subdef: "usubstappt \<sigma> U \<theta> \<noteq> undeft" using usubstappt_func_conv by auto
      from FuncMatch and Some
      have IHsubterm: "term_sem I (the (usubstappt \<sigma> U \<theta>)) \<nu> = term_sem (adjoint \<sigma> I \<omega>) \<theta> \<nu>" using va subdef by blast
      from FuncMatch and Some
      have IHsubsubst: "\<And>\<nu> \<omega>. Uvariation \<nu> \<omega> {} \<Longrightarrow> term_sem I (the (usubstappt (dotsubstt (the (usubstappt \<sigma> U \<theta>))) {} r)) \<nu> = term_sem (adjoint (dotsubstt (the (usubstappt \<sigma> U \<theta>))) I \<omega>) r \<nu>"
        using subdef varcond by fastforce 

      let ?d = "term_sem I (the (usubstappt \<sigma> U \<theta>)) \<nu>"
      have deq: "?d = term_sem (adjoint \<sigma> I \<omega>) \<theta> \<nu>" by (rule IHsubterm)
      let ?dotIa = "adjoint (dotsubstt (the (usubstappt \<sigma> U \<theta>))) I \<nu>"

      from Some 
      have "term_sem I (the (usubstappt \<sigma> U (Func f \<theta>))) \<nu> = term_sem I (the (usubstappt (dotsubstt (the (usubstappt \<sigma> U \<theta>))) {} r)) \<nu>" using subdef varcond by force
      also have "... = term_sem ?dotIa r \<nu>" using IHsubsubst[where \<nu>=\<nu> and \<omega>=\<nu>] Uvariation_empty by auto
      also have "... = term_sem (repc I dotid ?d) r \<nu>" using adjoint_dotsubstt[where \<theta>=\<open>the (usubstappt \<sigma> U \<theta>)\<close> and I=I and \<omega>=\<nu>] by simp
      also have "... = term_sem (repc I dotid ?d) r \<omega>" using coincidence_term_cor[where \<omega>=\<nu> and \<omega>'=\<omega> and U=U and \<theta>=r and I=\<open>repc I dotid ?d\<close>] va varcond by simp
          (*I.^d\<omega>\<lbrakk>\<sigma>f(\<cdot>)\<rbrakk>  also have "... = term_sem ?dotIa r \<omega>" using coincidence_term_cor[of \<nu> \<omega> U r ?dotIa] uv varcond by simp*)
      also have "... = (Funcs (adjoint \<sigma> I \<omega>) f)(?d)" using adjoint_funcs_match Some by simp
      also have "... = (Funcs (adjoint \<sigma> I \<omega>) f)(term_sem (adjoint \<sigma> I \<omega>) \<theta> \<nu>)" using deq by simp
      also have "... = term_sem (adjoint \<sigma> I \<omega>) (Func f \<theta>) \<nu>" by simp
      finally show "term_sem I (the (usubstappt \<sigma> U (Func f \<theta>))) \<nu> = term_sem (adjoint \<sigma> I \<omega>) (Func f \<theta>) \<nu>" .
    qed
  next
    case (Plus \<sigma> U \<theta> \<eta>)
    then show ?case using Pluso_undef by auto
  next
    case (Times \<sigma> U \<theta> \<eta>)
    then show ?case using Timeso_undef by auto
  next
    case (Differential \<sigma> U \<theta>)
    from Differential have subdef: "usubstappt \<sigma> allvars \<theta> \<noteq> undeft" using usubstappt_differential_conv by simp
    from Differential have IH: "\<And>\<nu>. term_sem I (the (usubstappt \<sigma> allvars \<theta>)) \<nu> = term_sem (adjoint \<sigma> I \<omega>) \<theta> \<nu>" using subdef Uvariation_univ by blast (*by auto*)

    have "term_sem I (the (usubstappt \<sigma> U (Differential \<theta>))) \<nu> = term_sem I (Differential (the (usubstappt \<sigma> allvars \<theta>))) \<nu>" using subdef by force
    also have "... = sum(\<lambda>x. \<nu>(DVar x)*deriv(\<lambda>X. term_sem I (the (usubstappt \<sigma> allvars \<theta>)) (repv \<nu> (RVar x) X))(\<nu>(RVar x)))(allidents)" by simp
    also have "... = sum(\<lambda>x. \<nu>(DVar x)*deriv(\<lambda>X. term_sem (adjoint \<sigma> I \<omega>) \<theta> (repv \<nu> (RVar x) X))(\<nu>(RVar x)))(allidents)" using IH by auto
    also have "... = term_sem (adjoint \<sigma> I \<omega>) (Differential \<theta>) \<nu>" by simp
    finally show "term_sem I (the (usubstappt \<sigma> U (Differential \<theta>))) \<nu> = term_sem (adjoint \<sigma> I \<omega>) (Differential \<theta>) \<nu>" .
  qed
qed

subsection \<open>Uniform Substitution for Formulas and Games\<close>

paragraph \<open>Separately Prove Crucial Ingredient for the ODE Case of \<open>usubst_fml_game\<close>\<close>

lemma same_ODE_same_sol:
  "(\<And>\<nu>. Uvariation \<nu> (F(0)) {RVar x,DVar x} \<Longrightarrow> term_sem I \<theta> \<nu> = term_sem J \<eta> \<nu>)
  \<Longrightarrow> solves_ODE I F x \<theta> = solves_ODE J F x \<eta>"
  using Uvariation_Vagree Vagree_def solves_ODE_def
    (*by (smt double_complement)*)
proof-
  assume va: "\<And>\<nu>. Uvariation \<nu> (F(0)) {RVar x,DVar x} \<Longrightarrow> term_sem I \<theta> \<nu> = term_sem J \<eta> \<nu>"
  then have va2: "\<And>\<nu>. Uvariation \<nu> (F(0)) {RVar x,DVar x} \<Longrightarrow> term_sem J \<eta> \<nu> = term_sem I \<theta> \<nu>" by simp
  have one: "\<And>I J \<theta> \<eta>. (\<And>\<nu>. Uvariation \<nu> (F(0)) {RVar x,DVar x} \<Longrightarrow> term_sem I \<theta> \<nu> = term_sem J \<eta> \<nu>)
   \<Longrightarrow> solves_ODE I F x \<theta> \<Longrightarrow> solves_ODE J F x \<eta>"
   proof-
     fix I J \<theta> \<eta>
     assume vaflow: "\<And>\<nu>. Uvariation \<nu> (F(0)) {RVar x,DVar x} \<Longrightarrow> term_sem I \<theta> \<nu> = term_sem J \<eta> \<nu>"
     assume sol: "solves_ODE I F x \<theta>"
     from vaflow and sol show "solves_ODE J F x \<eta>" unfolding solves_ODE_def using Uvariation_Vagree coincidence_term
     by (metis double_complement solves_Vagree sol)
  qed
  show "solves_ODE I F x \<theta> = solves_ODE J F x \<eta>" using one[where \<theta>=\<theta> and \<eta>=\<eta>, OF va] one[where \<theta>=\<eta> and \<eta>=\<theta>, OF va2] 
  by force
qed


lemma usubst_ode:
  assumes subdef: "usubstappt \<sigma> {RVar x,DVar x} \<theta> \<noteq> undeft"
  shows "solves_ODE I F x (the (usubstappt \<sigma> {RVar x,DVar x} \<theta>)) = solves_ODE (adjoint \<sigma> I (F(0))) F x \<theta>"
proof-
  have vaflow: "\<And>F \<theta> \<zeta>. solves_ODE I F x \<theta> \<Longrightarrow> Uvariation (F(\<zeta>)) (F(0)) {RVar x,DVar x}" using solves_Vagree_trans by simp
  from subdef have IH: "\<And>\<nu>. Uvariation \<nu> (F(0)) {RVar x,DVar x} \<Longrightarrow> term_sem I (the (usubstappt \<sigma> {RVar x,DVar x} \<theta>)) \<nu> = term_sem (adjoint \<sigma> I (F(0))) \<theta> \<nu>" by (simp add: usubst_term)
  then show ?thesis using IH vaflow solves_ODE_def Uvariation_Vagree same_ODE_same_sol by blast  
qed

lemma usubst_ode_ext:
  assumes     uv: "Uvariation (F(0)) \<omega> (U\<union>{RVar x,DVar x})"
  assumes subdef: "usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta> \<noteq> undeft"
  shows "solves_ODE I F x (the (usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta>)) = solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta>"
  (*using usubst_ode usubstappt_det usubstappt_antimon Uvariation_Vagree Uvariation_mon *)
proof-
  have vaflow1: "\<And>F \<theta> \<zeta>. solves_ODE I F x (the (usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta>)) \<Longrightarrow> Uvariation (F(\<zeta>)) (F(0)) {RVar x,DVar x}" using solves_Vagree_trans by simp
  have vaflow2: "\<And>F \<theta> \<zeta>. solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta> \<Longrightarrow> Uvariation (F(\<zeta>)) (F(0)) {RVar x,DVar x}" using solves_Vagree_trans by simp
  from subdef have IH: "\<And>\<nu>. Uvariation \<nu> (F(0)) (U\<union>{RVar x,DVar x}) \<Longrightarrow> term_sem I (the (usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta>)) \<nu> = term_sem (adjoint \<sigma> I (F(0))) \<theta> \<nu>" using Uvariation_refl Uvariation_trans usubst_term by blast
  have l2r: "solves_ODE I F x (the (usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta>)) \<Longrightarrow> solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta>"
    using vaflow1 subdef same_ODE_same_sol Uvariation_trans usubst_term uv
      (*by (smt sup_commute sup_left_idem)*)
  proof - (*sledgehammer*)
    assume a1: "solves_ODE I F x (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>))"
    obtain rr :: "trm \<Rightarrow> interp \<Rightarrow> trm \<Rightarrow> interp \<Rightarrow> char \<Rightarrow> (real \<Rightarrow> variable \<Rightarrow> real) \<Rightarrow> variable \<Rightarrow> real" where
      f2: "\<forall>x0 x1 x2 x3 x4 x5. (\<exists>v6. Uvariation v6 (x5 0) {RVar x4, DVar x4} \<and> term_sem x3 x2 v6 \<noteq> term_sem x1 x0 v6) = (Uvariation (rr x0 x1 x2 x3 x4 x5) (x5 0) {RVar x4, DVar x4} \<and> term_sem x3 x2 (rr x0 x1 x2 x3 x4 x5) \<noteq> term_sem x1 x0 (rr x0 x1 x2 x3 x4 x5))"
      by moura
    have f3: "Uvariation (F 0) \<omega> (insert (RVar x) (U \<union> {DVar x}))"
      using uv by auto
    have f4: "{DVar x} \<union> {} \<union> {DVar x} = insert (DVar x) ({DVar x} \<union> {} \<union> {}) \<longrightarrow> {RVar x} \<union> {DVar x} \<union> insert (RVar x) (U \<union> {DVar x}) = insert (RVar x) (U \<union> {DVar x})"
      by fastforce
    { assume "{DVar x} \<union> {} \<union> {DVar x} = insert (DVar x) ({DVar x} \<union> {} \<union> {}) \<and> Uvariation (rr (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) I \<theta> (USubst.adjoint \<sigma> I \<omega>) x F) \<omega> ({RVar x} \<union> {DVar x} \<union> insert (RVar x) (U \<union> {DVar x}))"
      then have "\<not> Uvariation (rr (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) I \<theta> (USubst.adjoint \<sigma> I \<omega>) x F) (F 0) {RVar x, DVar x} \<or> term_sem (USubst.adjoint \<sigma> I \<omega>) \<theta> (rr (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) I \<theta> (USubst.adjoint \<sigma> I \<omega>) x F) = term_sem I (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) (rr (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) I \<theta> (USubst.adjoint \<sigma> I \<omega>) x F)"
        using f4 subdef usubst_term by auto }
    then have "\<not> Uvariation (rr (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) I \<theta> (USubst.adjoint \<sigma> I \<omega>) x F) (F 0) {RVar x, DVar x} \<or> term_sem (USubst.adjoint \<sigma> I \<omega>) \<theta> (rr (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) I \<theta> (USubst.adjoint \<sigma> I \<omega>) x F) = term_sem I (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) (rr (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) I \<theta> (USubst.adjoint \<sigma> I \<omega>) x F)"
      using f3 by (metis (no_types) Uvariation_trans insert_is_Un)
    then show ?thesis
      using f2 a1 by (meson same_ODE_same_sol)
  qed 
  have r2l: "solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta> \<Longrightarrow> solves_ODE I F x (the (usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta>))"
    using vaflow2 subdef same_ODE_same_sol Uvariation_trans usubst_term uv
      (*by (smt sup_commute sup_left_idem)*)
  proof - (*sledgehammer*)
    assume a1: "solves_ODE (USubst.adjoint \<sigma> I \<omega>) F x \<theta>"
    obtain rr :: "trm \<Rightarrow> interp \<Rightarrow> trm \<Rightarrow> interp \<Rightarrow> char \<Rightarrow> (real \<Rightarrow> variable \<Rightarrow> real) \<Rightarrow> variable \<Rightarrow> real" where
      "\<forall>x0 x1 x2 x3 x4 x5. (\<exists>v6. Uvariation v6 (x5 0) {RVar x4, DVar x4} \<and> term_sem x3 x2 v6 \<noteq> term_sem x1 x0 v6) = (Uvariation (rr x0 x1 x2 x3 x4 x5) (x5 0) {RVar x4, DVar x4} \<and> term_sem x3 x2 (rr x0 x1 x2 x3 x4 x5) \<noteq> term_sem x1 x0 (rr x0 x1 x2 x3 x4 x5))"
      by moura
    then have f2: "\<forall>f c i t ia ta. Uvariation (rr ta ia t i c f) (f 0) {RVar c, DVar c} \<and> term_sem i t (rr ta ia t i c f) \<noteq> term_sem ia ta (rr ta ia t i c f) \<or> solves_ODE i f c t = solves_ODE ia f c ta"
      by (meson same_ODE_same_sol)
    have f3: "Uvariation (F 0) \<omega> ({RVar x, DVar x} \<union> U)"
      using uv by force
    have f4: "usubstappt \<sigma> ({RVar x, DVar x} \<union> U) \<theta> \<noteq> undeft"
      using subdef by auto
    { assume "Uvariation (rr \<theta> (USubst.adjoint \<sigma> I \<omega>) (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) I x F) \<omega> ({RVar x, DVar x} \<union> ({RVar x, DVar x} \<union> U))"
      then have "\<not> Uvariation (rr \<theta> (USubst.adjoint \<sigma> I \<omega>) (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) I x F) (F 0) {RVar x, DVar x} \<or> term_sem I (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) (rr \<theta> (USubst.adjoint \<sigma> I \<omega>) (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) I x F) = term_sem (USubst.adjoint \<sigma> I \<omega>) \<theta> (rr \<theta> (USubst.adjoint \<sigma> I \<omega>) (the (usubstappt \<sigma> (U \<union> {RVar x, DVar x}) \<theta>)) I x F)"
        using f4 by (simp add: Un_commute usubst_term) }
    then show ?thesis
      using f3 f2 a1 by (meson Uvariation_trans)
  qed
  from l2r and r2l show ?thesis by auto
qed

lemma usubst_ode_ext2:
  assumes subdef: "usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta> \<noteq> undeft"
  assumes     uv: "Uvariation (F(0)) \<omega> (U\<union>{RVar x,DVar x})"
  shows "solves_ODE I F x (the (usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta>)) = solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta>"
  using usubst_ode_ext subdef uv by blast 

paragraph \<open>Separately Prove the Loop Case of \<open>usubst_fml_game\<close>\<close>

lemma union_comm: "A\<union>B=B\<union>A"
  by auto


definition loopfp\<tau>:: "game \<Rightarrow> interp \<Rightarrow> (state set \<Rightarrow> state set)"
  where "loopfp\<tau> \<alpha> I X = lfp(\<lambda>Z. X \<union> game_sem I \<alpha> Z)"

lemma usubst_game_loop:
  assumes  uv: "Uvariation \<nu> \<omega> U"
    and  IH\<alpha>rec: "\<And>\<nu> \<omega> X. Uvariation \<nu> \<omega> (fst(usubstappp \<sigma> U \<alpha>)) \<Longrightarrow> snd (usubstappp \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<alpha>)\<noteq>undefg \<Longrightarrow> 
         (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<alpha>))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<alpha> X)"
  shows "snd (usubstappp \<sigma> U (Loop \<alpha>))\<noteq>undefg \<Longrightarrow> (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U (Loop \<alpha>)))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) (Loop \<alpha>) X)"
proof-
  assume def: "snd (usubstappp \<sigma> U (Loop \<alpha>))\<noteq>undefg"
  have loopfix: "\<And>\<alpha> I X. loopfp\<tau> \<alpha> I X = game_sem I (Loop \<alpha>) X" unfolding loopfp\<tau>_def using game_sem_loop by metis
  let ?\<sigma>\<alpha>loopoff = "the (snd (usubstappp \<sigma> U (Loop \<alpha>)))"
  let ?\<sigma>\<alpha> = "the (snd(usubstappp \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<alpha>))"
  let ?\<sigma>\<alpha>loop = "Loop ?\<sigma>\<alpha>"
  have loopform: "?\<sigma>\<alpha>loopoff = ?\<sigma>\<alpha>loop" using usubstappp_loop
    by (metis (mono_tags, lifting) Loopo.simps(1) def option.exhaust_sel option.inject snd_conv usubstappp_loop_conv)
  let ?\<tau> = "loopfp\<tau> ?\<sigma>\<alpha>loop I"
  let ?\<rho> = "loopfp\<tau> \<alpha> (adjoint \<sigma> I \<omega>)"
  let ?V = "fst(usubstappp \<sigma> U \<alpha>)"
  have fact1: "\<And>V. snd(usubstappp \<sigma> V \<alpha>)\<noteq>undefg \<Longrightarrow>  fst(usubstappp \<sigma> V \<alpha>) \<supseteq> BVG(the (snd(usubstappp \<sigma> V \<alpha>)))" using usubst_taboos by simp
  have fact2: "\<And>V W. snd(usubstappp \<sigma> V \<alpha>)\<noteq>undefg \<Longrightarrow> snd(usubstappp \<sigma> W \<alpha>)\<noteq>undefg \<Longrightarrow> (fst(usubstappp \<sigma> V \<alpha>) \<supseteq> BVG(the (snd(usubstappp \<sigma> W \<alpha>))))" using fact1 usubst_taboos usubstappp_det by metis
  have VgeqBV: "?V \<supseteq> BVG(?\<sigma>\<alpha>)" using usubst_taboos fact2 def usubstappp_loop_conv by simp
  have uvV: "Vagree \<nu> \<omega> (-?V)" using uv
    by (metis Uvariation_Vagree Uvariation_mon double_compl usubst_taboos_mon)  
  have \<tau>eq: "?\<tau>(X) = game_sem I ?\<sigma>\<alpha>loop X" using loopfix by auto
  have \<rho>eq: "?\<rho>(X) = game_sem (adjoint \<sigma> I \<omega>) (Loop \<alpha>) X"  using loopfix by auto
  have \<tau>is\<rho>: "selectlike (?\<tau>(X)) \<omega> (-?V)= selectlike (?\<rho>(X)) \<omega> (-?V)"
  proof-
    let ?f = "\<lambda>Z. X \<union> game_sem I ?\<sigma>\<alpha> Z"
    let ?g = "\<lambda>Y. X \<union> game_sem (adjoint \<sigma> I \<omega>) \<alpha> Y"
    let ?R = "\<lambda>Z Y. selectlike Z \<omega> (-?V) = selectlike Y \<omega> (-?V)"
    have "?R (lfp ?f) (lfp ?g)"
    proof (induction rule: lfp_lockstep_induct[where f=\<open>?f\<close> and g=\<open>?g\<close> and R=\<open>?R\<close>])
      case monof
      then show ?case using game_sem_loop_fixpoint_mono by simp
    next
      case monog
      then show ?case using game_sem_loop_fixpoint_mono by simp
    next
      case (step A B)
      then have IHfp: "selectlike A \<omega> (-?V) = selectlike B \<omega> (-?V)" by simp
      show "selectlike (X \<union> game_sem I ?\<sigma>\<alpha> A) \<omega> (-?V) = selectlike (X \<union> game_sem (adjoint \<sigma> I \<omega>) \<alpha> B) \<omega> (-?V)"
      proof (rule selectlike_equal_cocond_corule
          (*[where \<nu>=\<omega> and V=\<open>?V\<close> and X=\<open>X \<union> game_sem I ?\<sigma>\<alpha> A\<close> and Y=\<open>X \<union> game_sem (adjoint \<sigma> I \<omega>) \<alpha> B\<close>]*))
        fix \<mu>
        assume muvar: "Uvariation \<mu> \<omega> ?V"
        have forw: "(\<mu> \<in> X \<union> game_sem I ?\<sigma>\<alpha> A) = (\<mu> \<in> X \<union> game_sem I ?\<sigma>\<alpha> (selectlike A \<mu> (-BVG(?\<sigma>\<alpha>))))" using boundeffect by auto

        have "(\<mu> \<in> X \<union> game_sem (adjoint \<sigma> I \<omega>) \<alpha> B) = (\<mu> \<in> X \<union> game_sem I ?\<sigma>\<alpha> B)" using IH\<alpha>rec[OF muvar]
          using def usubstappp_loop_conv by auto
        also have "... = (\<mu> \<in> X \<union> game_sem I ?\<sigma>\<alpha> (selectlike B \<mu> (-BVG(?\<sigma>\<alpha>))))" using boundeffect by simp
        finally have backw: "(\<mu> \<in>  X \<union> game_sem (adjoint \<sigma> I \<omega>) \<alpha> B) =  (\<mu> \<in> X \<union> game_sem I ?\<sigma>\<alpha> (selectlike B \<mu> (-BVG(?\<sigma>\<alpha>))))" .

        have samewin: "selectlike A \<mu> (-BVG(?\<sigma>\<alpha>)) = selectlike B \<mu> (-BVG(?\<sigma>\<alpha>))" using IHfp selectlike_antimon VgeqBV muvar Uvariation_trans selectlike_equal_cocond
            (*by (smt le_iff_sup)*)
        proof -
          have "Vagree \<mu> \<omega> (- fst (usubstappp \<sigma> U \<alpha>))"
            by (metis Uvariation_Vagree double_complement muvar)
          then have "selectlike A \<mu> (- fst (usubstappp \<sigma> U \<alpha>)) = selectlike B \<mu> (- fst (usubstappp \<sigma> U \<alpha>))"
            using IHfp selectlike_Vagree by presburger
          then show ?thesis
            by (metis (no_types) Compl_subset_Compl_iff VgeqBV selectlike_compose sup.absorb_iff2)
        qed
        from forw and backw show "(\<mu> \<in> X \<union> game_sem I ?\<sigma>\<alpha> A) = (\<mu> \<in> X \<union> game_sem (adjoint \<sigma> I \<omega>) \<alpha> B)" using samewin by auto
      qed

    next
      case (union M)
      then show ?case using selectlike_Sup[where \<nu>=\<omega> and V=\<open>-?V\<close>] fst_proj_def snd_proj_def by (simp) (blast)
    qed
    then show ?thesis
      using \<tau>eq loopfix loopfp\<tau>_def by auto
  qed
  show ?thesis using \<tau>eq \<rho>eq \<tau>is\<rho> similar_selectlike_mem[OF uvV] by (metis loopform) 
qed



lemma usubst_fml_game: 
  assumes vaouter: "Uvariation \<nu> \<omega> U"
  shows "usubstappf \<sigma> U \<phi>\<noteq>undeff \<Longrightarrow> (\<nu> \<in> fml_sem I (the (usubstappf \<sigma> U \<phi>))) = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)"
    and "snd (usubstappp \<sigma> U \<alpha>)\<noteq>undefg \<Longrightarrow> (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U \<alpha>))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<alpha> X)"
proof-
  show "usubstappf \<sigma> U \<phi>\<noteq>undeff \<Longrightarrow> (\<nu> \<in> fml_sem I (the (usubstappf \<sigma> U \<phi>))) = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)" 
    and "snd (usubstappp \<sigma> U \<alpha>)\<noteq>undefg \<Longrightarrow> (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U \<alpha>))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<alpha> X)" for \<sigma> \<phi> \<alpha>
    using vaouter proof (induction \<phi> and \<alpha> arbitrary: \<nu> \<omega> and \<nu> \<omega> X rule: usubstappfp_induct)
    case (Pred \<sigma> U p \<theta>)
    then have va: "Uvariation \<nu> \<omega> U" by simp
    then show ?case
    proof (cases "SPreds \<sigma> p")
      case None
      then show ?thesis using usubst_term[OF va] adjoint_preds_skip
          (*by (smt Pred.prems(1) fml_sem.simps(1) mem_Collect_eq option.case_eq_if option.sel usubstappf.simps(1))*)
      proof - (*sledgehammer*)
        have "\<forall>p V c t. usubstappf p V (Pred c t) = (if usubstappt p V t = undeft then undeff else case SPreds p c of None \<Rightarrow> Afml (Pred c (the (usubstappt p V t))) | Some f \<Rightarrow> if FVF f \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt p V t))) {} f else undeff)"
          by (simp add: option.case_eq_if)
        then have f1: "\<forall>p V c t. if usubstappt p V t = undeft then usubstappf p V (Pred c t) = undeff else usubstappf p V (Pred c t) = (case SPreds p c of None \<Rightarrow> Afml (Pred c (the (usubstappt p V t))) | Some f \<Rightarrow> if FVF f \<inter> V = {} then usubstappf (dotsubstt (the (usubstappt p V t))) {} f else undeff)"
          by presburger
        then have "usubstappt \<sigma> U \<theta> \<noteq> undeft"
          by (meson Pred.prems(1))
        then have f2: "usubstappf \<sigma> U (Pred p \<theta>) = Afml (Pred p (the (usubstappt \<sigma> U \<theta>)))"
          using None by force
        have "usubstappt \<sigma> U \<theta> \<noteq> undeft"
          using f1 by (meson Pred.prems(1))
        then show ?thesis
          using f2 by (simp add: None \<open>\<And>\<theta> \<sigma> I. usubstappt \<sigma> U \<theta> \<noteq> undeft \<Longrightarrow> term_sem I (the (usubstappt \<sigma> U \<theta>)) \<nu> = term_sem (USubst.adjoint \<sigma> I \<omega>) \<theta> \<nu>\<close> adjoint_preds_skip)
      qed

    next
      case (Some r)
      then have varcond: "FVF(r)\<inter>U={}" using Pred usubstappf_pred usubstappf_pred2 usubstappf_pred_conv by meson 
      from Pred have subdef: "usubstappt \<sigma> U \<theta> \<noteq> undeft" using usubstappf_pred_conv by auto
      from Pred and Some
      have IHsubsubst: "\<And>\<nu> \<omega>. Uvariation \<nu> \<omega> {} \<Longrightarrow> (\<nu> \<in> fml_sem I (the (usubstappf (dotsubstt (the (usubstappt \<sigma> U \<theta>))) {} r))) = (\<nu> \<in> fml_sem (adjoint (dotsubstt (the (usubstappt \<sigma> U \<theta>))) I \<omega>) r)"
        using subdef varcond by fastforce

      let ?d = "term_sem I (the (usubstappt \<sigma> U \<theta>)) \<nu>"
      have deq: "?d = term_sem (adjoint \<sigma> I \<omega>) \<theta> \<nu>" by (rule usubst_term[OF va subdef])
      let ?dotIa = "adjoint (dotsubstt (the (usubstappt \<sigma> U \<theta>))) I \<nu>"

      from Some
      have "(\<nu>\<in>fml_sem I (the (usubstappf \<sigma> U (Pred p \<theta>)))) = (\<nu>\<in>fml_sem I (the (usubstappf (dotsubstt (the (usubstappt \<sigma> U \<theta>))) {} r)))"
        using subdef varcond by force 
      also have "... = (\<nu>\<in>fml_sem ?dotIa r)" using IHsubsubst[where \<nu>=\<nu> and \<omega>=\<nu>] Uvariation_empty by auto
      also have "... = (\<nu>\<in>fml_sem (repc I dotid ?d) r)" using adjoint_dotsubstt[where \<theta>=\<open>the (usubstappt \<sigma> U \<theta>)\<close> and I=I and \<omega>=\<nu>] by simp
      also have "... = (\<omega>\<in>fml_sem (repc I dotid ?d) r)" using coincidence_formula_cor[where \<omega>=\<nu> and \<omega>'=\<omega> and U=U and \<phi>=r and I=\<open>repc I dotid ?d\<close>] va varcond by simp
          (*I.^d\<omega>\<lbrakk>\<sigma>f(\<cdot>)\<rbrakk>  also have "... = term_sem ?dotIa r \<omega>" using coincidence_term_cor[of \<nu> \<omega> U r ?dotIa] uv varcond by simp*)
      also have "... = (Preds (adjoint \<sigma> I \<omega>) p)(?d)" using adjoint_preds_match Some by simp
      also have "... = (Preds (adjoint \<sigma> I \<omega>) p)(term_sem (adjoint \<sigma> I \<omega>) \<theta> \<nu>)" using deq by simp
      also have "... = (\<nu>\<in>fml_sem (adjoint \<sigma> I \<omega>) (Pred p \<theta>))" by simp
      finally show "(\<nu>\<in>fml_sem I (the (usubstappf \<sigma> U (Pred p \<theta>)))) = (\<nu>\<in>fml_sem (adjoint \<sigma> I \<omega>) (Pred p \<theta>))" .
    qed

  next
    case (Geq \<sigma> U \<theta> \<eta>)
      (* then show ?case using usubst_term usubstappf_geq usubstappf_geq_conv
          by (smt fml_sem.simps(2) mem_Collect_eq option.sel)*)
    then have def1: "usubstappt \<sigma> U \<theta> \<noteq> undeft" using usubstappf_geq_conv by simp 
    moreover have def2: "usubstappt \<sigma> U \<eta> \<noteq> undeft" using usubstappf_geq_conv Geq.prems(1) by blast 
    show ?case
      using usubst_term[OF \<open>Uvariation \<nu> \<omega> U\<close>, OF def1] usubst_term[OF \<open>Uvariation \<nu> \<omega> U\<close>,OF def2] usubstappf_geqr[OF \<open>usubstappf \<sigma> U (Geq \<theta> \<eta>) \<noteq> undeff\<close>] by force
  next
    case (Not \<sigma> U \<phi>)
    then show ?case using Noto_undef by auto
  next
    case (And \<sigma> U \<phi> \<psi>)
    then show ?case using Ando_undef by auto

  next
    case (Exists \<sigma> U x \<phi>)
    then have IH: "\<And>\<nu> \<omega>. Uvariation \<nu> \<omega> (U\<union>{x}) \<Longrightarrow> (\<nu> \<in> fml_sem I (the (usubstappf \<sigma> (U\<union>{x}) \<phi>))) = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)" by force
    from Exists have "Uvariation \<nu> \<omega> U" by simp
    (*from Exists have subdef: "usubstappt \<sigma> (U\<union>{x}) \<theta> \<noteq> undeft" by auto*)

    then have Uvar: "\<And>d. Uvariation (repv \<nu> x d) \<omega> (U\<union>{x})" using Uvariation_repv Uvariation_trans Uvariation_sym
      using Exists.prems(2) Uvariation_def by auto
    have "(\<nu>\<in>fml_sem I (the (usubstappf \<sigma> U (Exists x \<phi>)))) = (\<nu>\<in>fml_sem I (Exists x (the (usubstappf \<sigma> (U\<union>{x}) \<phi>))))"
      using usubstappf_exists Exists.prems(1) by fastforce
    also have "... = (\<exists>d. (repv \<nu> x d)\<in>fml_sem I (the (usubstappf \<sigma> (U\<union>{x}) \<phi>)))" by simp
    also have "... = (\<exists>d. (repv \<nu> x d)\<in>fml_sem (adjoint \<sigma> I \<omega>) \<phi>)" using IH Uvar by auto
    also have "... = (\<nu>\<in>fml_sem (adjoint \<sigma> I \<omega>) (Exists x \<phi>))" by auto
    finally have "(\<nu>\<in>fml_sem I (the (usubstappf \<sigma> U (Exists x \<phi>)))) =  (\<nu>\<in>fml_sem (adjoint \<sigma> I \<omega>) (Exists x \<phi>))" . 
    from this show ?case by simp

  next
    case (Diamond \<sigma> U \<alpha> \<phi>)
    let ?V = "fst(usubstappp \<sigma> U \<alpha>)"
    from Diamond have IH\<alpha>: "\<And>X. Uvariation \<nu> \<omega> U \<Longrightarrow> (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U \<alpha>))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<alpha> X)" by fastforce 
    from Diamond have IH\<phi>: "\<And>\<nu> \<omega>. Uvariation \<nu> \<omega> (fst(usubstappp \<sigma> U \<alpha>)) \<Longrightarrow> (\<nu> \<in> fml_sem I (the (usubstappf \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<phi>))) = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)"
      by (simp add: Diamondo_undef) 
    from Diamond have uv: "Uvariation \<nu> \<omega> U" by simp
    have "(\<nu> \<in> fml_sem I (the (usubstappf \<sigma> U (Diamond \<alpha> \<phi>)))) = (\<nu> \<in> fml_sem I (let V\<alpha> = usubstappp \<sigma> U \<alpha> in Diamond (the (snd V\<alpha>)) (the (usubstappf \<sigma> (fst V\<alpha>) \<phi>))))"
      by (metis Diamond.prems(1) Diamondo.elims option.sel usubstappf.simps(6)) 
    also have "... = (\<nu> \<in> fml_sem I (Diamond (the (snd(usubstappp \<sigma> U \<alpha>))) (the (usubstappf \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<phi>))))" by simp
    also have "... = (\<nu> \<in> game_sem I (the (snd(usubstappp \<sigma> U \<alpha>))) (fml_sem I (the (usubstappf \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<phi>))))" by simp
    also have "... = (\<nu> \<in> game_sem I (the (snd(usubstappp \<sigma> U \<alpha>))) (selectlike (fml_sem I (the (usubstappf \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<phi>))) \<nu> (-BVG(the (snd(usubstappp \<sigma> U \<alpha>))))))" using boundeffect by auto
    finally have forw: "(\<nu> \<in> fml_sem I (the (usubstappf \<sigma> U (Diamond \<alpha> \<phi>)))) = (\<nu> \<in> game_sem I (the (snd(usubstappp \<sigma> U \<alpha>))) (selectlike (fml_sem I (the (usubstappf \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<phi>))) \<nu> (-BVG(the (snd(usubstappp \<sigma> U \<alpha>))))))" .

    have "(\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) (Diamond \<alpha> \<phi>)) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<alpha> (fml_sem (adjoint \<sigma> I \<omega>) \<phi>))" by simp
    also have "... = (\<nu> \<in> game_sem I (the (snd(usubstappp \<sigma> U \<alpha>))) (fml_sem (adjoint \<sigma> I \<omega>) \<phi>))" using IH\<alpha> uv by simp
    also have "... = (\<nu> \<in> game_sem I (the (snd(usubstappp \<sigma> U \<alpha>))) (selectlike (fml_sem (adjoint \<sigma> I \<omega>) \<phi>) \<nu> (-BVG(the (snd(usubstappp \<sigma> U \<alpha>))))))" using boundeffect by auto
    finally have backw: "(\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) (Diamond \<alpha> \<phi>)) = (\<nu> \<in> game_sem I (the (snd(usubstappp \<sigma> U \<alpha>))) (selectlike (fml_sem (adjoint \<sigma> I \<omega>) \<phi>) \<nu> (-BVG(the (snd(usubstappp \<sigma> U \<alpha>))))))" .

    have samewin: "selectlike (fml_sem I (the (usubstappf \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<phi>))) \<nu> (-BVG(the (snd(usubstappp \<sigma> U \<alpha>)))) = selectlike (fml_sem (adjoint \<sigma> I \<omega>) \<phi>) \<nu> (-BVG(the (snd(usubstappp \<sigma> U \<alpha>))))"
    proof (rule selectlike_equal_cocond_corule)
      fix \<mu>
      assume muvar: "Uvariation \<mu> \<nu> (BVG(the (snd(usubstappp \<sigma> U \<alpha>))))" 
      have U\<mu>\<omega>: "Uvariation \<mu> \<omega> ?V" using muvar uv Uvariation_trans union_comm usubst_taboos Uvariation_mon
          (*by (smt Diamond.prems(1) Diamondo.simps(2) usubstappf.simps(6))*)
      proof- 
        have U\<mu>\<nu>: "Uvariation \<mu> \<nu> (BVG(the (snd(usubstappp \<sigma> U \<alpha>))))" by (rule muvar)
        have U\<nu>\<omega>: "Uvariation \<nu> \<omega> U" by (rule uv)
        have "Uvariation \<mu> \<omega> (U \<union> BVG(the (snd(usubstappp \<sigma> U \<alpha>))))" using Uvariation_trans[OF U\<mu>\<nu> U\<nu>\<omega>] union_comm by (rule HOL.back_subst)
        thus ?thesis using usubst_taboos Uvariation_mon by (metis (mono_tags, lifting) Diamond.prems(1) Diamondo_undef Uvariation_mon usubst_taboos usubstappf.simps(6))
      qed
      have "(\<mu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>) = (\<mu> \<in> fml_sem I (the (usubstappf \<sigma> (fst(usubstappp \<sigma> U \<alpha>)) \<phi>)))"
        using muvar Uvariation_trans uv IH\<phi> boundeffect Uvariation_mon usubst_taboos U\<mu>\<omega> by auto
      then show "(\<mu> \<in> fml_sem I (the (usubstappf \<sigma> (fst (usubstappp \<sigma> U \<alpha>)) \<phi>))) = (\<mu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)" by simp
    qed
    from forw and backw show "(\<nu> \<in> fml_sem I (the (usubstappf \<sigma> U (Diamond \<alpha> \<phi>)))) = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) (Diamond \<alpha> \<phi>))" using samewin by auto

  next (* games *)

    case (Game \<sigma> U a)
    then show ?case using adjoint_games usubstappp_game by (cases "SGames \<sigma> a") auto

  next
    case (Assign \<sigma> U x \<theta>)
    then show ?case using usubst_term Assigno_undef
        (*by (smt Assigno.elims game_sem.simps(2) mem_Collect_eq option.sel snd_pair usubstappp.simps(2))*)
    proof - (*sledgehammer*)
      have f1: "usubstappt \<sigma> U \<theta> \<noteq> undeft"
        using Assign.prems(1) Assigno_undef by auto
      { assume "repv \<nu> x (term_sem (USubst.adjoint \<sigma> I \<omega>) \<theta> \<nu>) \<in> X"
        then have "repv \<nu> x (term_sem I (the (usubstappt \<sigma> U \<theta>)) \<nu>) \<in> X"
          using f1 Assign.prems(2) usubst_term by auto
        then have "repv \<nu> x (term_sem (USubst.adjoint \<sigma> I \<omega>) \<theta> \<nu>) \<in> X \<longrightarrow> (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U (x := \<theta>)))) X) = (\<nu> \<in> game_sem (USubst.adjoint \<sigma> I \<omega>) (x := \<theta>) X)"
          using f1 by force }
      moreover
      { assume "repv \<nu> x (term_sem (USubst.adjoint \<sigma> I \<omega>) \<theta> \<nu>) \<notin> X"
        then have "repv \<nu> x (term_sem I (the (usubstappt \<sigma> U \<theta>)) \<nu>) \<notin> X \<and> repv \<nu> x (term_sem (USubst.adjoint \<sigma> I \<omega>) \<theta> \<nu>) \<notin> X"
          using f1 Assign.prems(2) usubst_term by presburger
        then have ?thesis
          using f1 by force }
      ultimately show ?thesis
        by fastforce
    qed

  next
    case (Test \<sigma> U \<phi>)
    then show ?case using Testo_undef by auto

  next
    case (Choice \<sigma> U \<alpha> \<beta>)
    from Choice have IH\<alpha>: "\<And>X. Uvariation \<nu> \<omega> U \<Longrightarrow> (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U \<alpha>))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<alpha> X)" by (simp add: Choiceo_undef) 
    from Choice have IH\<beta>: "\<And>X. Uvariation \<nu> \<omega> U \<Longrightarrow> (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U \<beta>))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<beta> X)" by (simp add: Choiceo_undef) 
    from Choice have uv: "Uvariation \<nu> \<omega> U" by simp
    show ?case using IH\<alpha> IH\<beta> uv
        (*by (smt Choice.prems(1) Choiceo.elims game_sem.simps(4) option.sel snd_pair union_or usubstappp_choice) *)
    proof -
      have f1: "Agame (the (snd (usubstappp \<sigma> U \<alpha>))) = snd (usubstappp \<sigma> U \<alpha>)"
        by (meson Choice(3) option.collapse usubstappp_choice_conv)
      have "Agame (the (snd (usubstappp \<sigma> U \<beta>))) = snd (usubstappp \<sigma> U \<beta>)"
        by (meson Choice(3) option.collapse usubstappp_choice_conv)
      then have "snd (usubstappp \<sigma> U (\<alpha> \<union>\<union> \<beta>)) = Agame (the (snd (usubstappp \<sigma> U \<alpha>)) \<union>\<union> the (snd (usubstappp \<sigma> U \<beta>)))"
        using f1 by (metis Choiceo.simps(1) snd_conv usubstappp.simps(4))
      then have f2: "game_sem I (the (snd (usubstappp \<sigma> U \<alpha>))) X \<union> game_sem I (the (snd (usubstappp \<sigma> U \<beta>))) X = game_sem I (the (snd (usubstappp \<sigma> U (\<alpha> \<union>\<union> \<beta>)))) X"
        by simp
      moreover
      { assume "\<nu> \<notin> game_sem I (the (snd (usubstappp \<sigma> U \<beta>))) X"
        have "(\<nu> \<notin> game_sem I (the (snd (usubstappp \<sigma> U (\<alpha> \<union>\<union> \<beta>)))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) (\<alpha> \<union>\<union> \<beta>) X) \<longrightarrow> \<nu> \<notin> game_sem I (the (snd (usubstappp \<sigma> U \<beta>))) X \<and> \<nu> \<notin> game_sem (adjoint \<sigma> I \<omega>) (\<alpha> \<union>\<union> \<beta>) X"
          using f2 Choice(4) IH\<alpha> IH\<beta> by auto
        then have "(\<nu> \<notin> game_sem I (the (snd (usubstappp \<sigma> U (\<alpha> \<union>\<union> \<beta>)))) X) \<noteq> (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) (\<alpha> \<union>\<union> \<beta>) X)"
          using f2 Choice(4) IH\<alpha> by auto }
      ultimately show ?thesis
        using Choice(4) IH\<beta> by auto
    qed 

  next
    case (Compose \<sigma> U \<alpha> \<beta>)
    let ?V = "fst(usubstappp \<sigma> U \<alpha>)"
    from Compose have IH\<alpha>: "\<And>X. Uvariation \<nu> \<omega> U \<Longrightarrow> (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U \<alpha>))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<alpha> X)" by (simp add: Composeo_undef) 
    from Compose have IH\<beta>: "\<And>\<nu> \<omega> X. Uvariation \<nu> \<omega> ?V \<Longrightarrow> (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> ?V \<beta>))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<beta> X)" by (simp add: Composeo_undef) 
    from Compose have uv: "Uvariation \<nu> \<omega> U" by simp
    have "(\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U (Compose \<alpha> \<beta>)))) X) = (\<nu> \<in> game_sem I (Compose (the (snd(usubstappp \<sigma> U \<alpha>))) (the (snd(usubstappp \<sigma> ?V \<beta>)))) X)"
      by (metis (no_types, lifting) Compose.prems(1) Composeo.elims option.sel snd_pair usubstappp.simps(5))
    also have "... = (\<nu> \<in> game_sem I (the (snd(usubstappp \<sigma> U \<alpha>))) (game_sem I (the (snd(usubstappp \<sigma> ?V \<beta>))) X))" by simp
    also have "... = (\<nu> \<in> game_sem I (the (snd(usubstappp \<sigma> U \<alpha>))) (selectlike (game_sem I (the (snd(usubstappp \<sigma> ?V \<beta>))) X) \<nu> (-BVG(the(snd(usubstappp \<sigma> U \<alpha>))))))" using boundeffect by auto
    finally have forw: "(\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U (Compose \<alpha> \<beta>)))) X) = (\<nu> \<in> game_sem I (the (snd(usubstappp \<sigma> U \<alpha>))) (selectlike (game_sem I (the (snd(usubstappp \<sigma> ?V \<beta>))) X) \<nu> (-BVG(the(snd(usubstappp \<sigma> U \<alpha>))))))" .

    have "(\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) (Compose \<alpha> \<beta>) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<alpha> ((game_sem (adjoint \<sigma> I \<omega>) \<beta>) X))" by simp
    also have "... = (\<nu> \<in> game_sem I (the (snd(usubstappp \<sigma> U \<alpha>))) ((game_sem (adjoint \<sigma> I \<omega>) \<beta>) X))" using IH\<alpha>[OF uv] by auto
    also have "... = (\<nu> \<in> game_sem I (the (snd(usubstappp \<sigma> U \<alpha>))) (selectlike ((game_sem (adjoint \<sigma> I \<omega>) \<beta>) X) \<nu> (-BVG(the(snd(usubstappp \<sigma> U \<alpha>))))))" using boundeffect by auto
    finally have backw: "(\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) (Compose \<alpha> \<beta>) X) = (\<nu> \<in> game_sem I (the (snd(usubstappp \<sigma> U \<alpha>))) (selectlike ((game_sem (adjoint \<sigma> I \<omega>) \<beta>) X) \<nu> (-BVG(the(snd(usubstappp \<sigma> U \<alpha>))))))" .

    have samewin: "selectlike (game_sem I (the (snd(usubstappp \<sigma> ?V \<beta>))) X) \<nu> (-BVG(the(snd(usubstappp \<sigma> U \<alpha>)))) = selectlike ((game_sem (adjoint \<sigma> I \<omega>) \<beta>) X) \<nu> (-BVG(the(snd(usubstappp \<sigma> U \<alpha>))))"
    proof (rule selectlike_equal_cocond_corule)
      fix \<mu>
      assume muvar: "Uvariation \<mu> \<nu> (BVG(the(snd(usubstappp \<sigma> U \<alpha>))))" 
      have U\<mu>\<omega>: "Uvariation \<mu> \<omega> ?V" using muvar uv Uvariation_trans union_comm usubst_taboos Uvariation_mon
          (*by (smt Compose.prems(1) Composeo_undef snd_pair usubstappp.simps(5))*)
      proof -
        have "Uvariation \<mu> \<omega> (BVG (the (snd (usubstappp \<sigma> U \<alpha>))) \<union> U)" by (meson Uvariation_trans muvar uv)
        then show ?thesis using Uvariation_mon union_comm usubst_taboos
          by (metis (no_types, lifting) Compose.prems(1) Composeo_undef Pair_inject prod.collapse usubstappp_compose) 
            (*by (metis (no_types) Uvariation_mon union_comm usubst_taboos)*)
      qed
      have "(\<mu> \<in> game_sem I (the(snd(usubstappp \<sigma> ?V \<beta>))) X) = (\<mu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<beta> X)"
        using muvar Uvariation_trans uv IH\<beta> boundeffect Uvariation_mon usubst_taboos U\<mu>\<omega> by auto
      then show "(\<mu> \<in> game_sem I (the(snd(usubstappp \<sigma> ?V \<beta>))) X) = (\<mu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<beta> X)" by simp
    qed
    from forw and backw show "(\<nu> \<in> game_sem I (the(snd (usubstappp \<sigma> U (Compose \<alpha> \<beta>)))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) (Compose \<alpha> \<beta>) X)" using samewin by auto

  next
    case (Loop \<sigma> U \<alpha>)
    let ?V = "fst(usubstappp \<sigma> U \<alpha>)"
    from Loop have selfdef: "snd (usubstappp \<sigma> U (Loop \<alpha>)) \<noteq> undefg" by auto
    from Loop have IH\<alpha>rec: "\<And>\<nu> \<omega> X. Uvariation \<nu> \<omega> ?V \<Longrightarrow> (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> ?V \<alpha>))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<alpha> X)" by fastforce 
    from Loop have uv: "Uvariation \<nu> \<omega> U" by simp
    show "(\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U (Loop \<alpha>)))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) (Loop \<alpha>) X)" 
      using usubst_game_loop IH\<alpha>rec Loop.prems(2) selfdef by blast 
      (*by (rule usubst_game_loop[OF uv (*IH\<alpha>*) IH\<alpha>rec])*)

  next
    case (Dual \<sigma> U \<alpha>)
    from Dual have IH\<alpha>: "\<And>X. Uvariation \<nu> \<omega> U \<Longrightarrow> (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U \<alpha>))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<alpha> X)" by force 
    from Dual have uv: "Uvariation \<nu> \<omega> U" by simp
    from Dual have def: "snd (usubstappp \<sigma> U (\<alpha>^d)) \<noteq> undefg" by simp
        (*show ?case using IH\<alpha>[OF uv]
    by (smt Compl_iff Dual.prems(1) Dualo.elims game_sem.simps(7) option.sel snd_pair usubstappp.simps(7))*)
    have "(\<nu> \<in> -game_sem I (the (snd (usubstappp \<sigma> U \<alpha>))) (-X)) = (\<nu> \<in> -game_sem (adjoint \<sigma> I \<omega>) \<alpha> (-X))" using IH\<alpha>[OF uv] by simp
    then have "(\<nu> \<in> game_sem I ((the (snd (usubstappp \<sigma> U \<alpha>)))^d) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) (\<alpha>^d) X)" using game_sem.simps(7) by auto
    then show ?case using usubstappp_dual Dualo_undef
    proof -
      have "\<And>\<sigma> V \<alpha>. snd (usubstappp \<sigma> U (\<alpha>^d)) = Dualo (snd (usubstappp \<sigma> U \<alpha>))"  by simp
      then have "snd (usubstappp \<sigma> U \<alpha>) \<noteq> undefg" using Dualo_undef def by presburger
      then show ?thesis
        using \<open>(\<nu> \<in> game_sem I ((the (snd (usubstappp \<sigma> U \<alpha>)))^d) X) = (\<nu> \<in> game_sem (USubst.adjoint \<sigma> I \<omega>) (\<alpha>^d) X)\<close> by force
    qed 

  next
    case (ODE \<sigma> U x \<theta>)
    then have va: "Uvariation \<nu> \<omega> U" by simp
    from ODE have subdef: "usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta> \<noteq> undeft" by (simp add: ODEo_undef) 
    from ODE have IH: "term_sem I (the (usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta>)) \<nu> = term_sem (adjoint \<sigma> I \<omega>) \<theta> \<nu>" using va
      by (metis ODEo_undef fst_pair snd_conv usubst_taboos_mon usubst_term usubstappp.simps(8) usubstappt_antimon) 
    have "(\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U (ODE x \<theta>)))) X) = (\<nu> \<in> game_sem I (the (ODEo x (usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta>))) X)" by simp
    also have "... = (\<nu> \<in> game_sem I (ODE x (the (usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta>))) X)" using subdef by force
    also have "... = (\<exists>F T. Vagree \<nu> (F(0)) (-{DVar x}) \<and> F(T) \<in> X \<and> solves_ODE I F x (the (usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta>)))" by simp
    also have "... = (\<exists>F T. Uvariation \<nu> (F(0)) {DVar x} \<and> F(T) \<in> X \<and> solves_ODE I F x (the (usubstappt \<sigma> (U\<union>{RVar x,DVar x}) \<theta>)))" using Uvariation_Vagree by (metis double_compl) 
    also have "... = (\<exists>F T. Uvariation \<nu> (F(0)) {DVar x} \<and> F(T) \<in> X \<and> solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta>)" 
      using usubst_ode_ext2[OF subdef] va solves_Vagree_trans Uvariation_trans Uvariation_sym_rel Uvariation_mon by (meson subset_insertI)
    also have "... = (\<exists>F T. Vagree \<nu> (F(0)) (-{DVar x}) \<and> F(T) \<in> X \<and> solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta>)" using Uvariation_Vagree by (metis double_compl) 
    also have "... = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) (ODE x \<theta>) X)" using solves_ODE_def by simp
    finally show "(\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U (ODE x \<theta>)))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) (ODE x \<theta>) X)" .
  qed
qed

text \<open>Lemma 16 of \<^url>\<open>http://arxiv.org/abs/1902.07230\<close>\<close>
theorem usubst_fml: "Uvariation \<nu> \<omega> U \<Longrightarrow> usubstappf \<sigma> U \<phi> \<noteq> undeff \<Longrightarrow>
    (\<nu> \<in> fml_sem I (the (usubstappf \<sigma> U \<phi>))) = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)"
  using usubst_fml_game by simp

text \<open>Lemma 17 of \<^url>\<open>http://arxiv.org/abs/1902.07230\<close>\<close>
theorem usubst_game: "Uvariation \<nu> \<omega> U \<Longrightarrow> snd (usubstappp \<sigma> U \<alpha>) \<noteq> undefg \<Longrightarrow>
    (\<nu> \<in> game_sem I (the (snd (usubstappp \<sigma> U \<alpha>))) X) = (\<nu> \<in> game_sem (adjoint \<sigma> I \<omega>) \<alpha> X)"
  using usubst_fml_game by simp


subsection \<open>Soundness of Uniform Substitution of Formulas\<close>

abbreviation usubsta:: "usubst \<Rightarrow> fml \<Rightarrow> fmlo"
  where "usubsta \<sigma> \<phi> \<equiv> usubstappf \<sigma> {} \<phi>"


text \<open>Theorem 18 of \<^url>\<open>http://arxiv.org/abs/1902.07230\<close>\<close>
theorem usubst_sound: "usubsta \<sigma> \<phi> \<noteq> undeff \<Longrightarrow> valid \<phi> \<Longrightarrow> valid (the (usubsta \<sigma> \<phi>))"
proof-
  assume def: "usubsta \<sigma> \<phi> \<noteq> undeff"
  assume prem: "valid \<phi>"
  from prem have premc: "\<And>I \<omega>. \<omega> \<in> fml_sem I \<phi>" using valid_def by auto
  show "valid (the (usubsta \<sigma> \<phi>))" unfolding valid_def
  proof (clarify)
    fix I \<omega>
    have "(\<omega> \<in> fml_sem I (the (usubsta \<sigma> \<phi>))) = (\<omega> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)" using usubst_fml by (simp add: usubst_fml def)
    also have "... = True" using premc by simp
    finally have "(\<omega> \<in> fml_sem I (the (usubsta \<sigma> \<phi>))) = True" .
    from this show "\<omega> \<in> fml_sem I (the (usubstappf \<sigma> {} \<phi>))" by simp
  qed
qed

subsection \<open>Soundness of Uniform Substitution of Rules\<close>

text \<open>Uniform Substitution applied to a rule or inference\<close>
definition usubstr:: "usubst \<Rightarrow> inference \<Rightarrow> inference option"
  where "usubstr \<sigma> R \<equiv> if (usubstappf \<sigma> allvars (snd R) \<noteq> undeff \<and> (\<forall>\<phi>\<in>set (fst R). usubstappf \<sigma> allvars \<phi> \<noteq> undeff)) then
    Some(map(the o (usubstappf \<sigma> allvars))(fst R), the (usubstappf \<sigma> allvars (snd R)))
  else
    None"

text \<open>Simple observations about applying uniform substitutions to a rule\<close>

lemma usubstr_conv: "usubstr \<sigma> R \<noteq> None \<Longrightarrow>
  usubstappf \<sigma> allvars (snd R) \<noteq> undeff \<and>
  (\<forall>\<phi>\<in>set (fst R). usubstappf \<sigma> allvars \<phi> \<noteq> undeff)"
  by (metis usubstr_def)

lemma usubstr_union_undef: "(usubstr \<sigma> ((append A B), C) \<noteq> None) = (usubstr \<sigma> (A, C) \<noteq> None \<and> usubstr \<sigma> (B, C) \<noteq> None)"
  using usubstr_def by auto
lemma usubstr_union_undef2: "(usubstr \<sigma> ((append A B), C) \<noteq> None) \<Longrightarrow> (usubstr \<sigma> (A, C) \<noteq> None \<and> usubstr \<sigma> (B, C) \<noteq> None)"
  using usubstr_union_undef by blast

lemma usubstr_cons_undef: "(usubstr \<sigma> ((Cons A B), C) \<noteq> None) = (usubstr \<sigma> ([A], C) \<noteq> None \<and> usubstr \<sigma> (B, C) \<noteq> None)"
  using usubstr_def by auto
lemma usubstr_cons_undef2: "(usubstr \<sigma> ((Cons A B), C) \<noteq> None) \<Longrightarrow> (usubstr \<sigma> ([A], C) \<noteq> None \<and> usubstr \<sigma> (B, C) \<noteq> None)"
  using usubstr_cons_undef by blast

lemma usubstr_cons: "(usubstr \<sigma> ((Cons A B), C) \<noteq> None) \<Longrightarrow>
  the (usubstr \<sigma> ((Cons A B), C)) = (Cons (the (usubstappf \<sigma> allvars A)) (fst (the (usubstr \<sigma> (B, C)))), snd (the (usubstr \<sigma> ([A], C))))"
  using usubstr_union_undef map_cons usubstr_def
proof-
  assume def: "(usubstr \<sigma> ((Cons A B), C) \<noteq> None)"
  let ?R = "((Cons A B), C)"
  have "the (usubstr \<sigma> ?R) = (map(the o (usubstappf \<sigma> allvars))(fst ?R) , the (usubstappf \<sigma> allvars (snd ?R)))" using def usubstr_def by (metis option.sel)
  also have "... = (Cons (the (usubstappf \<sigma> allvars A)) (map(the o (usubstappf \<sigma> allvars))(B)) , the (usubstappf \<sigma> allvars (snd ?R)))" using map_cons by auto 
  also have "... = (Cons (the (usubstappf \<sigma> allvars A)) (fst (the (usubstr \<sigma> (B, C)))) , the (usubstappf \<sigma> allvars (snd ?R)))" using usubstr_cons_undef2[OF def] usubstr_def by (metis (no_types, lifting) fst_conv option.sel) 
  also have "... = (Cons (the (usubstappf \<sigma> allvars A)) (fst (the (usubstr \<sigma> (B, C)))) , snd (the (usubstr \<sigma> ([A], C))))" using def usubstr_def by auto
  ultimately show "the (usubstr \<sigma> ((Cons A B), C)) = (Cons (the (usubstappf \<sigma> allvars A)) (fst (the (usubstr \<sigma> (B, C)))) , snd (the (usubstr \<sigma> ([A], C))))" by simp
qed

lemma usubstr_union: "(usubstr \<sigma> ((append A B), C) \<noteq> None) \<Longrightarrow>
  the (usubstr \<sigma> ((append A B), C)) = (append (fst (the (usubstr \<sigma> (A, C)))) (fst (the (usubstr \<sigma> (B, C)))), snd (the (usubstr \<sigma> (A, C))))"
  using usubstr_union_undef2
    (*by (smt fst_pair map_append option.sel snd_pair usubstr_def)*)
proof-
  assume def: "(usubstr \<sigma> ((append A B), C) \<noteq> None)"  
  let ?R = "((append A B), C)"
  have "the (usubstr \<sigma> ?R) = (map(the o (usubstappf \<sigma> allvars))(fst ?R) , the (usubstappf \<sigma> allvars (snd ?R)))" using def usubstr_def by (metis option.sel)
  also have "... = (map(the o (usubstappf \<sigma> allvars))(fst ?R) , snd (the (usubstr \<sigma> (A, C))))" using usubstr_union_undef2[OF def] usubstr_def by (metis option.sel sndI) 
  also have "... = (append (map(the o (usubstappf \<sigma> allvars))(A)) (map(the o (usubstappf \<sigma> allvars))(B)) , snd (the (usubstr \<sigma> (A, C))))" using usubstr_union_undef2[OF def] map_append by simp
  also have "... = (append (fst (the (usubstr \<sigma> (A, C)))) (fst (the (usubstr \<sigma> (B, C)))), snd (the (usubstr \<sigma> (A, C))))" using usubstr_union_undef2[OF def] usubstr_def by (metis (no_types, lifting) fst_conv option.sel) 
  ultimately show "the (usubstr \<sigma> ((append A B), C)) = (append (fst (the (usubstr \<sigma> (A, C)))) (fst (the (usubstr \<sigma> (B, C)))), snd (the (usubstr \<sigma> (A, C))))" by simp
qed

lemma usubstr_length: "usubstr \<sigma> R \<noteq> None \<Longrightarrow> length (fst (the (usubstr \<sigma> R))) = length (fst R)"
  by (metis fst_pair length_map option.sel usubstr_def)

lemma usubstr_nth: "usubstr \<sigma> R \<noteq> None \<Longrightarrow> 0\<le>k \<Longrightarrow> k<length (fst R) \<Longrightarrow>
   nth (fst (the (usubstr \<sigma> R))) k = the (usubstappf \<sigma> allvars (nth (fst R) k))"
  (*unfolding usubstr_def using usubstr_length
  by (smt comp_apply fst_pair nth_map option.sel)*)
proof-
  assume a1: "usubstr \<sigma> R \<noteq> None"
  assume a2: "0\<le>k"
  assume a3: "k<length (fst R)"  
  show "nth (fst (the (usubstr \<sigma> R))) k = the (usubstappf \<sigma> allvars (nth (fst R) k))"
    using a1 a2 a3 proof (induction R arbitrary: k)
    case (Pair A C)
    then show ?case
    proof (induction A arbitrary: k)
      case Nil
      then show ?case by simp 
    next
      case (Cons D E)
      then have IH: "\<And>k. usubstr \<sigma> (E, C) \<noteq> None \<Longrightarrow> 0 \<le> k \<Longrightarrow> k < length E \<Longrightarrow> nth (fst (the (usubstr \<sigma> (E, C)))) k = the (usubstappf \<sigma> allvars (nth E k))" by simp
      then show ?case
      proof (cases k)
        case 0
        then show ?thesis using Cons usubstr_cons by simp
      next
        case (Suc n)
        then have smaller: "n<length E" using Cons.prems(3) by auto 
        have nati: "0\<le>n" by simp
        have def: "usubstr \<sigma> (E, C) \<noteq> None" using usubstr_cons_undef2[OF Cons.prems(1)] by blast
        have "nth (fst (the (usubstr \<sigma> (E, C)))) n = the (usubstappf \<sigma> allvars (nth (fst (E,C)) n))" using IH[OF def, OF nati, OF smaller] by simp
        then show ?thesis using Cons usubstr_cons by (simp add: Suc) 
      qed
    qed
  qed
qed

text \<open>Theorem 19 of \<^url>\<open>http://arxiv.org/abs/1902.07230\<close>\<close>

theorem usubst_rule_sound: "usubstr \<sigma> R \<noteq> None \<Longrightarrow> locally_sound R \<Longrightarrow> locally_sound (the (usubstr \<sigma> R))"
proof-
  assume def: "usubstr \<sigma> R \<noteq> None"
  assume prem: "locally_sound R"
  let ?\<sigma>D = "usubstr \<sigma> R"
  fix \<omega>
  from usubst_fml have substeq: "\<And>I \<nu> \<phi>. usubstappf \<sigma> allvars \<phi> \<noteq> undeff \<Longrightarrow> (\<nu> \<in> fml_sem I (the (usubstappf \<sigma> allvars \<phi>))) = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)" using Uvariation_univ by blast
  then have substval: "\<And>I. usubstappf \<sigma> allvars \<phi> \<noteq> undeff \<Longrightarrow> valid_in I (the (usubstappf \<sigma> allvars \<phi>)) = valid_in (adjoint \<sigma> I \<omega>) \<phi>" unfolding valid_in_def by auto
  show "locally_sound (the (usubstr \<sigma> R))" unfolding locally_sound_def
  proof (clarify)
    fix I
    assume "\<forall>k\<ge>0. k < length (fst (the (usubstr \<sigma> R))) \<longrightarrow> valid_in I (nth (fst (the (usubstr \<sigma> R))) k)"
    then have "\<forall>k\<ge>0. k < length (fst R) \<longrightarrow> valid_in (adjoint \<sigma> I \<omega>) (nth (fst R) k)" using substval usubstr_nth usubstr_length substeq valid_in_def by (metis def nth_mem usubstr_def)
    then have "valid_in (adjoint \<sigma> I \<omega>) (snd R)" using prem unfolding locally_sound_def by simp
    from this show "valid_in I (snd (the (usubstr \<sigma> R)))" using usubst_fml substeq usubstr_def valid_in_def by (metis def option.sel snd_conv)
  qed
qed

end
