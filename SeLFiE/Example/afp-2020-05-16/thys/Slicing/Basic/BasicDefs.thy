chapter \<open>The Framework\<close>

theory BasicDefs imports AuxLemmas begin

text \<open>
  As slicing is a program analysis that can be completely based on the
  information given in the CFG, we want to provide a framework which
  allows us to formalize and prove properties of slicing regardless of
  the actual programming language. So the starting point for the formalization 
  is the definition of an abstract CFG, i.e.\ without considering features 
  specific for certain languages. By doing so we ensure that our framework 
  is as generic as possible since all proofs hold for every language whose 
  CFG conforms to this abstract CFG.  This abstract CFG can be used as a 
  basis for static intraprocedural slicing as well as for dynamic slicing, 
  if in the dynamic case all method calls are inlined (i.e., abstract CFG 
  paths conform to traces).
\<close>

section \<open>Basic Definitions\<close>

subsection\<open>Edge kinds\<close>

datatype 'state edge_kind = Update "'state \<Rightarrow> 'state"           ("\<Up>_")
                          | Predicate "'state \<Rightarrow> bool"      ("'(_')\<^sub>\<surd>")


subsection \<open>Transfer and predicate functions\<close>

fun transfer :: "'state edge_kind \<Rightarrow> 'state \<Rightarrow> 'state"
where "transfer (\<Up>f) s = f s"
  | "transfer (P)\<^sub>\<surd> s   = s"

fun transfers :: "'state edge_kind list \<Rightarrow> 'state \<Rightarrow> 'state"
where "transfers [] s   = s"
  | "transfers (e#es) s = transfers es (transfer e s)"

fun pred :: "'state edge_kind \<Rightarrow> 'state \<Rightarrow> bool"
where "pred (\<Up>f) s = True"
  | "pred (P)\<^sub>\<surd> s   = (P s)"

fun preds :: "'state edge_kind list \<Rightarrow> 'state \<Rightarrow> bool"
where "preds [] s   = True"
  | "preds (e#es) s = (pred e s \<and> preds es (transfer e s))"



lemma transfers_split:
  "(transfers (ets@ets') s) = (transfers ets' (transfers ets s))"
by(induct ets arbitrary:s) auto

lemma preds_split:
  "(preds (ets@ets') s) = (preds ets s \<and> preds ets' (transfers ets s))"
by(induct ets arbitrary:s) auto


lemma transfers_id_no_influence:
  "transfers [et \<leftarrow> ets. et \<noteq> \<Up>id] s = transfers ets s"
by(induct ets arbitrary:s,auto)

lemma preds_True_no_influence:
  "preds [et \<leftarrow> ets. et \<noteq> (\<lambda>s. True)\<^sub>\<surd>] s = preds ets s"
by(induct ets arbitrary:s,auto)

end
