(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Structural_Congruence
  imports Agent
begin


inductive structCong :: "(('a::fs_name), ('b::fs_name), ('c::fs_name)) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<equiv>\<^sub>s _" [70, 70] 70)
where
  Refl: "P \<equiv>\<^sub>s P"
| Sym:  "P \<equiv>\<^sub>s Q \<Longrightarrow> Q \<equiv>\<^sub>s P"
| Trans: "\<lbrakk>P \<equiv>\<^sub>s Q; Q \<equiv>\<^sub>s R\<rbrakk> \<Longrightarrow> P \<equiv>\<^sub>s R"

| ParComm: "P \<parallel> Q \<equiv>\<^sub>s Q \<parallel> P"
| ParAssoc: "(P \<parallel> Q) \<parallel> R \<equiv>\<^sub>s P \<parallel> (Q \<parallel> R)"
| ParId: "P \<parallel> \<zero> \<equiv>\<^sub>s P"

| ResNil: "\<lparr>\<nu>x\<rparr>\<zero> \<equiv>\<^sub>s \<zero>"
| ResComm: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<equiv>\<^sub>s \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
| ScopeExtPar: "x \<sharp> P \<Longrightarrow> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<equiv>\<^sub>s P \<parallel> \<lparr>\<nu>x\<rparr>Q"
| InputRes: "\<lbrakk>x \<sharp> M; x \<sharp> xvec; x \<sharp> N\<rbrakk> \<Longrightarrow> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<equiv>\<^sub>s M\<lparr>\<lambda>*xvec N\<rparr>.(\<lparr>\<nu>x\<rparr>P)"
| OutputRes: "\<lbrakk>x \<sharp> M; x \<sharp> N\<rbrakk> \<Longrightarrow> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<equiv>\<^sub>s M\<langle>N\<rangle>.(\<lparr>\<nu>x\<rparr>P)"
| CaseRes: "x \<sharp> (map fst Cs) \<Longrightarrow> \<lparr>\<nu>x\<rparr>(Cases Cs) \<equiv>\<^sub>s Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"

| BangUnfold: "guarded P \<Longrightarrow> !P \<equiv>\<^sub>s P \<parallel> !P"

end
