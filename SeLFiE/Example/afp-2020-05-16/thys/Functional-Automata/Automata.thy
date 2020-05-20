(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "Conversions between automata"

theory Automata
imports DA NAe
begin

definition
 na2da :: "('a,'s)na \<Rightarrow> ('a,'s set)da" where
"na2da A = ({start A}, \<lambda>a Q. Union(next A a ` Q), \<lambda>Q. \<exists>q\<in>Q. fin A q)"

definition
 nae2da :: "('a,'s)nae \<Rightarrow> ('a,'s set)da" where
"nae2da A = ({start A},
              \<lambda>a Q. Union(next A (Some a) ` ((eps A)\<^sup>* `` Q)),
              \<lambda>Q. \<exists>p \<in> (eps A)\<^sup>* `` Q. fin A p)"

(*** Equivalence of NA and DA ***)

lemma DA_delta_is_lift_NA_delta:
 "\<And>Q. DA.delta (na2da A) w Q = Union(NA.delta A w ` Q)"
by (induct w)(auto simp:na2da_def)

lemma NA_DA_equiv:
  "NA.accepts A w = DA.accepts (na2da A) w"
apply (simp add: DA.accepts_def NA.accepts_def DA_delta_is_lift_NA_delta)
apply (simp add: na2da_def)
done

(*** Direct equivalence of NAe and DA ***)

lemma espclosure_DA_delta_is_steps:
 "\<And>Q. (eps A)\<^sup>* `` (DA.delta (nae2da A) w Q) = steps A w `` Q"
apply (induct w)
 apply(simp)
apply (simp add: step_def nae2da_def)
apply (blast)
done

lemma NAe_DA_equiv:
  "DA.accepts (nae2da A) w = NAe.accepts A w"
proof -
  have "\<And>Q. fin (nae2da A) Q = (\<exists>q \<in> (eps A)\<^sup>* `` Q. fin A q)"
    by(simp add:nae2da_def)
  thus ?thesis
    apply(simp add:espclosure_DA_delta_is_steps NAe.accepts_def DA.accepts_def)
    apply(simp add:nae2da_def)
    apply blast
    done
qed

end
