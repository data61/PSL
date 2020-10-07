(*  Title:      Jinja/J/execute_Bigstep.thy
    Author:     Tobias Nipkow
    Copyright   2004 Technische Universitaet Muenchen
*)

section \<open>Code Generation For BigStep\<close>

theory execute_Bigstep
imports
  BigStep Examples
  "HOL-Library.Code_Target_Numeral"
begin

inductive map_val :: "expr list \<Rightarrow> val list \<Rightarrow> bool"
where
  Nil: "map_val [] []"
| Cons: "map_val xs ys \<Longrightarrow> map_val (Val y # xs) (y # ys)"

inductive map_val2 :: "expr list \<Rightarrow> val list \<Rightarrow> expr list \<Rightarrow> bool"
where
  Nil: "map_val2 [] [] []"
| Cons: "map_val2 xs ys zs \<Longrightarrow> map_val2 (Val y # xs) (y # ys) zs"
| Throw: "map_val2 (throw e # xs) [] (throw e # xs)"

theorem map_val_conv: "(xs = map Val ys) = map_val xs ys"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys \<Longrightarrow> map_val xs ys"
    apply (induct xs type:list)
    apply (case_tac ys)
    apply simp
    apply (rule map_val.Nil)
    apply simp
    apply (case_tac ys)
    apply simp
    apply simp
    apply (erule conjE)
    apply (rule map_val.Cons)
    apply simp
    done
  moreover have "map_val xs ys \<Longrightarrow> xs = map Val ys"
    by (erule map_val.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

theorem map_val2_conv:
 "(xs = map Val ys @ throw e # zs) = map_val2 xs ys (throw e # zs)"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys @ throw e # zs \<Longrightarrow> map_val2 xs ys (throw e # zs)"
    apply (induct xs type:list)
    apply (case_tac ys)
    apply simp
    apply simp
    apply simp
    apply (case_tac ys)
    apply simp
    apply (rule map_val2.Throw)
    apply simp
    apply (rule map_val2.Cons)
    apply simp
    done
  moreover have "map_val2 xs ys (throw e # zs) \<Longrightarrow> xs = map Val ys @ throw e # zs"
    by (erule map_val2.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

lemma CallNull2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>evs,s\<^sub>2\<rangle>; map_val evs vs \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>2\<rangle>"
apply(rule CallNull, assumption+)
apply(simp add: map_val_conv[symmetric])
done


lemma CallParamsThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>evs,s\<^sub>2\<rangle>;
     map_val2 evs vs (throw ex # es'') \<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"
apply(rule eval_evals.CallParamsThrow, assumption+)
apply(simp add: map_val2_conv[symmetric])
done

lemma Call2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^sub>2,l\<^sub>2)\<rangle>;
     map_val evs vs;
     h\<^sub>2 a = Some(C,fs);  P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D;
     length vs = length pns;  l\<^sub>2' = [this\<mapsto>Addr a, pns[\<mapsto>]vs];
     P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2)\<rangle>"
apply(rule Call, assumption+)
apply(simp add: map_val_conv[symmetric])
apply assumption+
done

code_pred 
  (modes: i \<Rightarrow> o \<Rightarrow> bool)
  map_val 
.

code_pred
  (modes: i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  map_val2
.

lemmas [code_pred_intro] =
 eval_evals.New eval_evals.NewFail
 eval_evals.Cast eval_evals.CastNull eval_evals.CastFail eval_evals.CastThrow
 eval_evals.Val eval_evals.Var
 eval_evals.BinOp eval_evals.BinOpThrow1 eval_evals.BinOpThrow2
 eval_evals.LAss eval_evals.LAssThrow
 eval_evals.FAcc eval_evals.FAccNull eval_evals.FAccThrow
 eval_evals.FAss eval_evals.FAssNull
 eval_evals.FAssThrow1 eval_evals.FAssThrow2
 eval_evals.CallObjThrow

declare CallNull2 [code_pred_intro CallNull2]
declare CallParamsThrow2 [code_pred_intro CallParamsThrow2]
declare Call2 [code_pred_intro Call2]

lemmas [code_pred_intro] =
 eval_evals.Block
 eval_evals.Seq eval_evals.SeqThrow
 eval_evals.CondT eval_evals.CondF eval_evals.CondThrow
 eval_evals.WhileF eval_evals.WhileT
 eval_evals.WhileCondThrow

declare eval_evals.WhileBodyThrow [code_pred_intro WhileBodyThrow2]

lemmas [code_pred_intro] =
 eval_evals.Throw eval_evals.ThrowNull
 eval_evals.ThrowThrow
 eval_evals.Try eval_evals.TryCatch eval_evals.TryThrow
 eval_evals.Nil eval_evals.Cons eval_evals.ConsThrow

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool as execute)
  eval
proof -
  case eval
  from eval.prems show thesis
  proof(cases (no_simp))
    case CallNull thus ?thesis
      by(rule eval.CallNull2[OF refl])(simp add: map_val_conv[symmetric])
  next
    case CallParamsThrow thus ?thesis
      by(rule eval.CallParamsThrow2[OF refl])(simp add: map_val2_conv[symmetric])
  next
    case Call thus ?thesis
      by -(rule eval.Call2[OF refl], simp_all add: map_val_conv[symmetric])
  next
    case WhileBodyThrow thus ?thesis by(rule eval.WhileBodyThrow2[OF refl])
  qed(assumption|erule (4) eval.that[OF refl]|erule (3) eval.that[OF refl])+
next
  case evals
  from evals.prems show thesis
    by(cases (no_simp))(assumption|erule (3) evals.that[OF refl])+
qed

notation execute ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<Rightarrow>/ \<langle>'_, '_\<rangle>)" [51,0,0] 81)

definition "test1 = [] \<turnstile> \<langle>testExpr1,(Map.empty,Map.empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test2 = [] \<turnstile> \<langle>testExpr2,(Map.empty,Map.empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test3 = [] \<turnstile> \<langle>testExpr3,(Map.empty,Map.empty(''V''\<mapsto>Intg 77))\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test4 = [] \<turnstile> \<langle>testExpr4,(Map.empty,Map.empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test5 = [(''Object'',('''',[],[])),(''C'',(''Object'',[(''F'',Integer)],[]))] \<turnstile> \<langle>testExpr5,(Map.empty,Map.empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test6 = [(''Object'',('''',[],[])), classI] \<turnstile> \<langle>testExpr6,(Map.empty,Map.empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

definition "V = ''V''"
definition "C = ''C''"
definition "F = ''F''"

ML_val \<open>
  val SOME ((@{code Val} (@{code Intg} (@{code int_of_integer} 5)), _), _) = Predicate.yield @{code test1};
  val SOME ((@{code Val} (@{code Intg} (@{code int_of_integer} 11)), _), _) = Predicate.yield @{code test2};
  val SOME ((@{code Val} (@{code Intg} (@{code int_of_integer} 83)), _), _) = Predicate.yield @{code test3};

  val SOME ((_, (_, l)), _) = Predicate.yield @{code test4};
  val SOME (@{code Intg} (@{code int_of_integer} 6)) = l @{code V};

  val SOME ((_, (h, _)), _) = Predicate.yield @{code test5};
  val SOME (c, fs) = h (@{code nat_of_integer} 1);
  val SOME (obj, _) = h (@{code nat_of_integer} 0);
  val SOME (@{code Intg} i) = fs (@{code F}, @{code C});
  @{assert} (c = @{code C} andalso obj = @{code Object} andalso i = @{code int_of_integer} 42);

  val SOME ((@{code Val} (@{code Intg} (@{code int_of_integer} 160)), _), _) = Predicate.yield @{code test6};
\<close>

definition "test7 = [classObject, classL] \<turnstile> \<langle>testExpr_BuildList, (Map.empty,Map.empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

definition "L = ''L''"
definition "N = ''N''"

ML_val \<open>
  val SOME ((_, (h, _)), _) = Predicate.yield @{code test7};
  val SOME (_, fs1) = h (@{code nat_of_integer} 0);
  val SOME (_, fs2) = h (@{code nat_of_integer} 1);
  val SOME (_, fs3) = h (@{code nat_of_integer} 2);
  val SOME (_, fs4) = h (@{code nat_of_integer} 3);

  val F = @{code "F"};
  val L = @{code "L"};
  val N = @{code "N"};

  @{assert} (fs1 (F, L) = SOME (@{code Intg} (@{code int_of_integer} 1)) andalso
     fs1 (N, L) = SOME (@{code Addr} (@{code nat_of_integer} 1)) andalso
     fs2 (F, L) = SOME (@{code Intg} (@{code int_of_integer} 2)) andalso
     fs2 (N, L) = SOME (@{code Addr} (@{code nat_of_integer} 2)) andalso
     fs3 (F, L) = SOME (@{code Intg} (@{code int_of_integer} 3)) andalso
     fs3 (N, L) = SOME (@{code Addr} (@{code nat_of_integer} 3)) andalso
     fs4 (F, L) = SOME (@{code Intg} (@{code int_of_integer} 4)) andalso
     fs4 (N, L) = SOME @{code Null});
\<close>

definition "test8 = [classObject, classA] \<turnstile> \<langle>testExpr_ClassA, (Map.empty,Map.empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "i = ''int''"
definition "t = ''test''"
definition "A = ''A''"

ML_val \<open>
  val SOME ((_, (h, l)), _) = Predicate.yield @{code test8};
  val SOME (_, fs1) = h (@{code nat_of_integer} 0);
  val SOME (_, fs2) = h (@{code nat_of_integer} 1);

  val i = @{code "i"};
  val t = @{code "t"};
  val A = @{code "A"};

  @{assert} (fs1 (i, A) = SOME (@{code Intg} (@{code int_of_integer} 10)) andalso 
     fs1 (t, A) = SOME @{code Null} andalso
     fs2 (i, A) = SOME (@{code Intg} (@{code int_of_integer} 50)) andalso 
     fs2 (t, A) = SOME @{code Null});
\<close>

end

