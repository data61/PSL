(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Struct_Cong
  imports Agent
begin

inductive structCong :: "ccs \<Rightarrow> ccs \<Rightarrow> bool" ("_ \<equiv>\<^sub>s _")
  where
  Refl: "P \<equiv>\<^sub>s P"
| Sym: "P \<equiv>\<^sub>s Q \<Longrightarrow> Q \<equiv>\<^sub>s P"
| Trans: "\<lbrakk>P \<equiv>\<^sub>s Q; Q \<equiv>\<^sub>s R\<rbrakk> \<Longrightarrow> P \<equiv>\<^sub>s R"

| ParComm: "P \<parallel> Q \<equiv>\<^sub>s Q \<parallel> P"
| ParAssoc: "(P \<parallel> Q) \<parallel> R \<equiv>\<^sub>s P \<parallel> (Q \<parallel> R)"
| ParId: "P \<parallel> \<zero> \<equiv>\<^sub>s P"

| SumComm: "P \<oplus> Q \<equiv>\<^sub>s Q \<oplus> P"
| SumAssoc: "(P \<oplus> Q) \<oplus> R \<equiv>\<^sub>s P \<oplus> (Q \<oplus> R)"
| SumId: "P \<oplus> \<zero> \<equiv>\<^sub>s P"

| ResNil: "\<lparr>\<nu>x\<rparr>\<zero> \<equiv>\<^sub>s \<zero>"
| ScopeExtPar: "x \<sharp> P \<Longrightarrow> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<equiv>\<^sub>s P \<parallel> \<lparr>\<nu>x\<rparr>Q"
| ScopeExtSum: "x \<sharp> P \<Longrightarrow> \<lparr>\<nu>x\<rparr>(P \<oplus> Q) \<equiv>\<^sub>s P \<oplus> \<lparr>\<nu>x\<rparr>Q"
| ScopeAct: "x \<sharp> \<alpha> \<Longrightarrow> \<lparr>\<nu>x\<rparr>(\<alpha>.(P)) \<equiv>\<^sub>s \<alpha>.(\<lparr>\<nu>x\<rparr>P)"
| ScopeCommAux: "x \<noteq> y \<Longrightarrow> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<equiv>\<^sub>s \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"

| BangUnfold: "!P \<equiv>\<^sub>s P \<parallel> !P"
equivariance structCong
nominal_inductive structCong
by(auto simp add: abs_fresh)

lemma ScopeComm:
  fixes x :: name
  and   y :: name
  and   P :: ccs

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<equiv>\<^sub>s \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
by(cases "x=y") (auto intro: Refl ScopeCommAux)

end

