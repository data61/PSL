(*
Title: Strong-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory MWLf
imports Types
begin

\<comment> \<open>SYNTAX\<close>

\<comment> \<open>Commands for the multi-threaded while language with fork (to instantiate 'com)\<close>
datatype ('exp, 'id) MWLfCom 
  = Skip ("skip")
  | Assign "'id" "'exp" 
       ("_:=_" [70,70] 70)

  | Seq "('exp, 'id) MWLfCom" "('exp, 'id) MWLfCom" 
       ("_;_" [61,60] 60)
 
  | If_Else "'exp" "('exp, 'id) MWLfCom" "('exp, 'id) MWLfCom"
       ("if _ then _ else _ fi" [80,79,79] 70)

  | While_Do "'exp" "('exp, 'id) MWLfCom" 
       ("while _ do _ od" [80,79] 70)

  | Fork "('exp, 'id) MWLfCom" "(('exp, 'id) MWLfCom) list"
       ("fork _ _" [70,70] 70)

\<comment> \<open>SEMANTICS\<close>

locale MWLf_semantics =
fixes E :: "('exp, 'id, 'val) Evalfunction"
and BMap :: "'val \<Rightarrow> bool"
begin

\<comment> \<open>steps semantics, set of deterministic steps from single threads to either single threads or thread pools\<close>
inductive_set 
MWLfSteps_det :: "('exp, 'id, 'val, ('exp, 'id) MWLfCom) TSteps"
and MWLfSteps_det' :: "('exp, 'id, 'val, ('exp, 'id) MWLfCom) TSteps_curry"
  ("(1\<langle>_,/_\<rangle>) \<rightarrow>/ (1\<langle>_,/_\<rangle>)" [0,0,0,0] 81)
where
"\<langle>c1,m1\<rangle> \<rightarrow> \<langle>c2,m2\<rangle> \<equiv> ((c1,m1),(c2,m2)) \<in> MWLfSteps_det" |
skip: "\<langle>skip,m\<rangle> \<rightarrow> \<langle>[],m\<rangle>" |
assign: "(E e m) = v \<Longrightarrow> \<langle>x := e,m\<rangle> \<rightarrow> \<langle>[],m(x := v)\<rangle>" |
seq1: "\<langle>c1,m\<rangle> \<rightarrow> \<langle>[],m'\<rangle> \<Longrightarrow> \<langle>c1;c2,m\<rangle> \<rightarrow> \<langle>[c2],m'\<rangle>" |
seq2: "\<langle>c1,m\<rangle> \<rightarrow> \<langle>c1'#V,m'\<rangle> \<Longrightarrow> \<langle>c1;c2,m\<rangle> \<rightarrow> \<langle>(c1';c2)#V,m'\<rangle>" |
iftrue: "BMap (E b m) = True \<Longrightarrow> 
    \<langle>if b then c1 else c2 fi,m\<rangle> \<rightarrow> \<langle>[c1],m\<rangle>" |
iffalse: "BMap (E b m) = False \<Longrightarrow> 
    \<langle>if b then c1 else c2 fi,m\<rangle> \<rightarrow> \<langle>[c2],m\<rangle>" |
whiletrue: "BMap (E b m) = True \<Longrightarrow> 
    \<langle>while b do c od,m\<rangle> \<rightarrow> \<langle>[c;(while b do c od)],m\<rangle>" |
whilefalse: "BMap (E b m) = False \<Longrightarrow> 
    \<langle>while b do c od,m\<rangle> \<rightarrow> \<langle>[],m\<rangle>" |
fork: "\<langle>fork c V,m\<rangle> \<rightarrow> \<langle>c#V,m\<rangle>"

inductive_cases MWLfSteps_det_cases:
"\<langle>skip,m\<rangle> \<rightarrow> \<langle>W,m'\<rangle>"
"\<langle>x := e,m\<rangle> \<rightarrow> \<langle>W,m'\<rangle>"
"\<langle>c1;c2,m\<rangle> \<rightarrow> \<langle>W,m'\<rangle>"
"\<langle>if b then c1 else c2 fi,m\<rangle> \<rightarrow> \<langle>W,m'\<rangle>"
"\<langle>while b do c od,m\<rangle> \<rightarrow> \<langle>W,m'\<rangle>"
"\<langle>fork c V,m\<rangle> \<rightarrow> \<langle>W,m'\<rangle>"

\<comment> \<open>non-deterministic, possibilistic system step (added for intuition, not used in the proofs)\<close>
inductive_set
MWLfSteps_ndet :: "('exp, 'id, 'val, ('exp,'id) MWLfCom) TPSteps"
and MWLfSteps_ndet' :: "('exp, 'id, 'val, ('exp,'id) MWLfCom) TPSteps_curry"
("(1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>)" [0,0,0,0] 81)
where
"\<langle>V1,m1\<rangle> \<Rightarrow> \<langle>V2,m2\<rangle> \<equiv> ((V1,m1),(V2,m2)) \<in> MWLfSteps_ndet" |
"\<langle>ci,m\<rangle> \<rightarrow> \<langle>c,m'\<rangle> \<Longrightarrow> \<langle>Vf @ [ci] @ Va,m\<rangle> \<Rightarrow> \<langle>Vf @ c @ Va,m'\<rangle>"

end


end
