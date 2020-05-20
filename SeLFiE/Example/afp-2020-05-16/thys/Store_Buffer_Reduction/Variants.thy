(*<*)
theory Variants
imports Abbrevs 
begin


lemma restrict_map_inverse: "m |` (dom m - X) = m |`(-X)"
  apply (rule ext)
  apply (auto simp add: restrict_map_def)
  done

lemma conj_assoc: "((P \<and> Q) \<and> X) = (P \<and> Q \<and> X)"
  by simp

(* Constructor markup for some datatypes *)
(* instr *)
notation (latex output)
Read ("\<^latex>\<open>\\constructor{Read}\<close>")
notation (latex output)
Write ("\<^latex>\<open>\\constructor{Write}\<close>")
notation (latex output)
RMW ("\<^latex>\<open>\\constructor{RMW}\<close>")
notation (latex output)
Fence ("\<^latex>\<open>\\constructor{Fence}\<close>")
notation (latex output)
Ghost ("\<^latex>\<open>\\constructor{Ghost}\<close>")

(* memref *)
notation (latex output)
Write\<^sub>s\<^sub>b ("\<^latex>\<open>\\constructor{Write}\<close>\<^sub>s\<^sub>b")
notation (latex output)
Read\<^sub>s\<^sub>b ("\<^latex>\<open>\\constructor{Read}\<close>\<^sub>s\<^sub>b")
notation (latex output)
Prog\<^sub>s\<^sub>b ("\<^latex>\<open>\\constructor{Prog}\<close>\<^sub>s\<^sub>b")
notation (latex output)
Ghost\<^sub>s\<^sub>b ("\<^latex>\<open>\\constructor{Ghost}\<close>\<^sub>s\<^sub>b")



(* expr *)
notation (latex output)
Const ("\<^latex>\<open>\\constructor{Const}\<close>")
notation (latex output)
Mem ("\<^latex>\<open>\\constructor{Mem}\<close>")
notation (latex output)
Tmp ("\<^latex>\<open>\\constructor{Tmp}\<close>")
notation (latex output)
Unop ("\<^latex>\<open>\\constructor{Unop}\<close>")
notation (latex output)
Binop ("\<^latex>\<open>\\constructor{Binop}\<close>")

(* stmt *)
notation (latex output)
Skip ("\<^latex>\<open>\\constructor{Skip}\<close>")
notation (latex output)
Assign ("\<^latex>\<open>\\constructor{Assign}\<close>")
notation (latex output)
CAS ("\<^latex>\<open>\\constructor{CAS}\<close>")
notation (latex output)
Seq ("\<^latex>\<open>\\constructor{Seq}\<close>")
notation (latex output)
Cond ("\<^latex>\<open>\\constructor{Cond}\<close>")
notation (latex output)
While ("\<^latex>\<open>\\constructor{While}\<close>")
notation (latex output)
SGhost ("\<^latex>\<open>\\constructor{SGhost}\<close>")
notation (latex output)
SFence ("\<^latex>\<open>\\constructor{SFence}\<close>")

lemma sim_direct_config_def': "ts\<^sub>s\<^sub>b \<sim>\<^sub>d ts \<equiv>
(ts\<^sub>s\<^sub>b = (map (\<lambda>(p,is, \<theta>,sb::unit,\<D>, \<O>,\<R>). (p,is,\<theta>,[],(),(),())) ts))"
apply (rule HOL.eq_reflection)
apply rule
apply  (erule sim_direct_config.cases)
apply  (clarsimp)
apply  (rule nth_equalityI)
apply   simp
apply  clarsimp
apply  (case_tac "ts!i")
apply  fastforce
apply (rule sim_direct_config.intros)
apply auto
done

ML \<open>@{term "(\<lambda>(p,is, \<theta>,sb::unit,\<D>, \<O>,\<R>). (p,is,\<theta>,[],(),(),()))"}\<close>

lemma DRead: "(Read volatile a t # is,\<theta>, x, m,ghst) \<rightarrow>
               (is, \<theta> (t\<mapsto>m a), x, m, ghst)"
apply (cases ghst) 
apply (simp add: direct_memop_step.Read)
done

lemma DWriteNonVolatile:"
  (Write False a (D,f) A L R W#is, \<theta>, x, m, ghst) \<rightarrow> (is, \<theta>, x, m(a := f \<theta>), ghst)"
apply (cases ghst) 
apply (simp add: direct_memop_step.WriteNonVolatile)
done

lemma DWriteVolatile:
  "ghst = (\<D>, \<O>, \<R>, \<S>) \<Longrightarrow> ghst' = (True, \<O> \<union> A - R, Map.empty, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) 
   \<Longrightarrow> (Write True a (D,f) A L R W# is, \<theta>, x, m, ghst) \<rightarrow> (is, \<theta>,  x, m(a:=f \<theta>), ghst')"
by (simp add: direct_memop_step.WriteVolatile)

lemma DGhost:
  "ghst = (\<D>, \<O>, \<R>, \<S>) \<Longrightarrow> ghst' = (\<D>, \<O> \<union> A - R, augment_rels (dom \<S>) R \<R>, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) 
   \<Longrightarrow> (Ghost A L R W# is, \<theta>, x, m, ghst) \<rightarrow> (is, \<theta>,  x, m, ghst')"
by (simp add: direct_memop_step.Ghost)

lemma DRMWReadOnly:
  "\<lbrakk>\<not> cond (\<theta>(t\<mapsto>m a)); ghst = (\<D>, \<O>, \<R>, \<S>); ghst'=(False, \<O>, Map.empty,\<S>)\<rbrakk> \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W # is, \<theta>, x, m, ghst) \<rightarrow> (is, \<theta>(t\<mapsto>m a),x,m, ghst')"
apply (simp add: direct_memop_step.RMWReadOnly)
done

lemma DRMWWrite:
  "\<lbrakk>cond (\<theta>(t\<mapsto>m a)); 
    \<theta>' = \<theta>(t\<mapsto>ret (m a) (f(\<theta>(t\<mapsto>m a))));
    m' = m(a:= f(\<theta>(t\<mapsto>m a)));
    ghst = (\<D>, \<O>, \<R>, \<S>); 
   ghst' = (False,\<O> \<union> A - R, Map.empty, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)\<rbrakk> 
   \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W# is, \<theta>, x, m, ghst) \<rightarrow> (is, \<theta>',x, m' , ghst')"
apply (simp add: direct_memop_step.RMWWrite)
done

lemma VRead: "(Read volatile a t # is,\<theta>, x, m,ghst) \<rightarrow>\<^sub>v
               (is, \<theta> (t\<mapsto>m a), x, m, ghst)"
apply (cases ghst) 
apply (simp add: virtual_memop_step.Read)
done

lemma VWriteNonVolatile:"
  (Write False a (D,f) A L R W#is, \<theta>, x, m, ghst) \<rightarrow>\<^sub>v (is, \<theta>, x, m(a := f \<theta>), ghst)"
apply (cases ghst) 
apply (simp add: virtual_memop_step.WriteNonVolatile)
done

lemma VWriteVolatile:
  "ghst = (\<D>, \<O>, \<R>, \<S>) \<Longrightarrow> ghst' = (True, \<O> \<union> A - R, \<R>, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) 
   \<Longrightarrow> (Write True a (D,f) A L R W# is, \<theta>, x, m, ghst) \<rightarrow>\<^sub>v (is, \<theta>,  x, m(a:=f \<theta>), ghst')"
by (simp add: virtual_memop_step.WriteVolatile)

lemma VRMWReadOnly:
  "\<lbrakk>\<not> cond (\<theta>(t\<mapsto>m a)); ghst = (\<D>, \<O>, \<R>, \<S>); ghst'=(False, \<O>,\<R>,\<S>)\<rbrakk> \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W # is, \<theta>, x, m, ghst) \<rightarrow>\<^sub>v (is, \<theta>(t\<mapsto>m a),x,m, ghst')"
apply (simp add: virtual_memop_step.RMWReadOnly)
done

lemma VFence:
  "ghst = (\<D>, \<O>, \<R>, \<S>) \<Longrightarrow> ghst' = (False, \<O>, \<R>, \<S>) 
   \<Longrightarrow> (Fence# is, \<theta>, x, m, ghst) \<rightarrow>\<^sub>v (is, \<theta>,  x, m, ghst')"
by (simp add: virtual_memop_step.Fence)

lemma VGhost:
  "ghst = (\<D>, \<O>, \<R>, \<S>) \<Longrightarrow> ghst' = (\<D>, \<O> \<union> A - R, \<R>, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)  
   \<Longrightarrow> (Ghost A L R W# is, \<theta>, x, m, ghst) \<rightarrow>\<^sub>v (is, \<theta>,  x, m, ghst')"
by (simp add: virtual_memop_step.Ghost)

lemma VRMWWrite:
  "\<lbrakk>cond (\<theta>(t\<mapsto>m a)); 
    \<theta>' = \<theta>(t\<mapsto>ret (m a) (f(\<theta>(t\<mapsto>m a))));
    m' = m(a:= f(\<theta>(t\<mapsto>m a)));
    ghst = (\<D>, \<O>, \<R>, \<S>); 
   ghst' = (False,\<O> \<union> A - R, \<R>, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)\<rbrakk> 
   \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W# is, \<theta>, x, m, ghst) \<rightarrow>\<^sub>v (is, \<theta>',x, m' , ghst')"
apply (simp add: virtual_memop_step.RMWWrite)
done


lemma SafeWriteVolatile:
  "\<lbrakk>\<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> a \<notin> \<O>s!j; a \<notin> read_only \<S>;    
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow>  A \<inter>  \<O>s!j = {};
    A \<subseteq> \<O> \<union> dom \<S>; L \<subseteq> A; R \<subseteq> \<O>; A \<inter> R = {}
   \<rbrakk>
   \<Longrightarrow> 
   \<O>s,i\<turnstile>(Write True a (D,f) A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"
apply (rule safe_direct_memop_state.WriteVolatile)
apply auto
done

lemma SafeDelayedWriteVolatile:
  "\<lbrakk>\<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> a \<notin> (\<O>s!j \<union> dom (\<R>s!j)); a \<notin> read_only \<S>;
  \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow>  A \<inter>  (\<O>s!j \<union> dom (\<R>s!j)) = {};
    A \<subseteq> dom \<S> \<union> \<O>; L \<subseteq> A; R \<subseteq> \<O>; A \<inter> R = {}
   \<rbrakk>
   \<Longrightarrow> 
   \<O>s,\<R>s,i\<turnstile>(Write True a (D,f) A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"
apply (rule safe_delayed_direct_memop_state.WriteVolatile)
apply auto
done


lemma SafeRMWReadOnly:
  "\<lbrakk>\<not> cond (\<theta>(t\<mapsto>m a)); a \<in> dom \<S> \<union> \<O>\<rbrakk> \<Longrightarrow> 
   \<O>s,i\<turnstile> (RMW a t (D,f) cond ret A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"
apply (rule safe_direct_memop_state.RMWReadOnly)
apply auto
done

lemma SafeDelayedRMWReadOnly:
  "\<lbrakk>\<not> cond (\<theta>(t\<mapsto>m a)); a \<in> dom \<S> \<union> \<O>; 
   \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> (\<R>s!j) a \<noteq> Some False \<comment> \<open>no release of unshared address\<close>\<rbrakk>
   \<Longrightarrow> 
   \<O>s,\<R>s,i\<turnstile>(RMW a t (D,f) cond ret A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"
apply (rule safe_delayed_direct_memop_state.RMWReadOnly)
apply auto
done

lemma SafeRMWWrite:
  "\<lbrakk>cond (\<theta>(t\<mapsto>m a));  
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> a \<notin> \<O>s!j; a \<notin> read_only \<S>;
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> A \<inter> \<O>s!j  = {};    
    A \<subseteq>  \<O> \<union> dom \<S>; L \<subseteq> A; R \<subseteq> \<O>; A \<inter> R = {}
    \<rbrakk> 
   \<Longrightarrow> 
   \<O>s,i\<turnstile> (RMW a t (D,f) cond ret A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"
apply (rule safe_direct_memop_state.RMWWrite)
apply auto
done

lemma SafeDelayedRMWWrite:
  "\<lbrakk>cond (\<theta>(t\<mapsto>m a)); a \<in> dom \<S> \<union> \<O>;  
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> a \<notin> (\<O>s!j \<union> dom (\<R>s!j));a \<notin> read_only \<S>;
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> A \<inter> (\<O>s!j \<union> dom (\<R>s!j))  = {};
    A \<subseteq> dom \<S> \<union> \<O>; L \<subseteq> A; R \<subseteq> \<O>; A \<inter> R = {}
    \<rbrakk> 
   \<Longrightarrow> 
   \<O>s,\<R>s,i\<turnstile>(RMW a t (D,f) cond ret A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"
apply (rule safe_delayed_direct_memop_state.RMWWrite)
apply auto
done

lemma  Write\<^sub>s\<^sub>bNonVolatile: 
  "(m, Write\<^sub>s\<^sub>b False a sop v A L R W# rs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m(a := v), rs,\<O>,\<R>,\<S>)"
  apply (rule flush_step.Write\<^sub>s\<^sub>b)
  apply auto
  done

lemma Write\<^sub>s\<^sub>bVolatile: 
"\<lbrakk>\<O>'= \<O> \<union> A - R;  \<S>'=(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)\<rbrakk> \<Longrightarrow>
  (m, Write\<^sub>s\<^sub>b True a sop v A L R W# rs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m(a := v), rs,\<O>',Map.empty,\<S>')"
  apply (rule flush_step.Write\<^sub>s\<^sub>b)
  apply auto
  done

lemma Ghost\<^sub>s\<^sub>b: "\<lbrakk>\<O>'= \<O> \<union> A - R; \<R>'= augment_rels (dom \<S>) R \<R>; \<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L\<rbrakk> \<Longrightarrow> 
             (m, Ghost\<^sub>s\<^sub>b A L R W# rs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m, rs,\<O>',\<R>',\<S>')"
by (simp add: flush_step.Ghost)

lemma  SBHRead: 
  "\<lbrakk>v = (case (buffered_val sb a) of Some v' \<Rightarrow> v' | None \<Rightarrow> m a);
   sb' = sb@[Read\<^sub>s\<^sub>b volatile a t v] \<rbrakk>
   \<Longrightarrow>
   (Read volatile a t # is, \<theta>, sb, m,ghst) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
          (is, \<theta> (t\<mapsto>v), sb', m,ghst)"
  apply (cases ghst)
  apply (cases "buffered_val sb a")
  apply (auto simp add: SBHReadBuffered SBHReadUnbuffered)
  done

lemma  SBRead: 
  "\<lbrakk>v = (case (buffered_val sb a) of Some v' \<Rightarrow> v' | None \<Rightarrow> m a)\<rbrakk>
   \<Longrightarrow>
   (Read volatile a t # is, \<theta>, sb, m,ghst) \<rightarrow>\<^sub>s\<^sub>b
          (is, \<theta> (t\<mapsto>v), sb, m,ghst)"
  apply (cases ghst)
  apply (cases "buffered_val sb a")
  apply (auto simp add: SBReadBuffered SBReadUnbuffered)
  done

lemma  SBHReadBuffered': 
  "\<lbrakk>buffered_val sb a = Some v;
   sb' = sb@[Read\<^sub>s\<^sub>b volatile a t v] \<rbrakk>
   \<Longrightarrow>
   (Read volatile a t # is, \<theta>, sb, m, \<D>, \<O>,\<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
          (is, \<theta> (t\<mapsto>v), sb', m, \<D>, \<O>,\<R>, \<S>)"
  by (simp add: SBHReadBuffered)

lemma SBHReadUnbuffered': 
  "\<lbrakk>buffered_val sb a = None;
    sb' = sb@[Read\<^sub>s\<^sub>b volatile a t (m a)]\<rbrakk> 
   \<Longrightarrow>
   (Read volatile a t # is,\<theta>, sb, m, \<D>, \<O>,\<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
          (is,\<theta> (t\<mapsto>m a), sb', m, \<D>, \<O>,\<R>, \<S>)"
by (simp add: SBHReadUnbuffered)

lemma SBHWriteNonVolatile':
  "\<lbrakk> sb'= sb@ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>) A L R W]\<rbrakk> 
   \<Longrightarrow>
   (Write False a (D,f) A L R W#is,\<theta>, sb, m, ghst) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
          (is, \<theta>, sb', m, ghst)"
by (cases ghst) (simp add: SBHWriteNonVolatile)

lemma SBWriteNonVolatile':
  "\<lbrakk> sb'= sb@ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>) A L R W]\<rbrakk> 
   \<Longrightarrow>
   (Write False a (D,f) A L R W#is,\<theta>, sb, m, ghst) \<rightarrow>\<^sub>s\<^sub>b
          (is, \<theta>, sb', m, ghst)"
by (cases ghst) (simp add: SBWriteNonVolatile)

lemma SBHWriteVolatile':
  "\<lbrakk>sb'= sb@[Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>) A L R W]; ghst = (\<D>, \<O>, \<R>, \<S>); ghst' = (True, \<O>,\<R>, \<S>)\<rbrakk>
   \<Longrightarrow> 
   (Write True a (D,f) A L R W# is,\<theta>, sb, m,ghst) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
         (is,\<theta>, sb', m,ghst')"
by (simp add: SBHWriteVolatile)

lemma SBHGhost':
  "(Ghost A L R W# is, \<theta>, sb, m, G) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
         (is, \<theta>, sb@[Ghost\<^sub>s\<^sub>b A L R W], m, G)"
  by (cases G) (simp add: SBHGhost)


lemma SBWriteVolatile':
  "\<lbrakk>sb'= sb@[Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>) A L R W]\<rbrakk>
   \<Longrightarrow> 
   (Write True a (D,f) A L R W# is,\<theta>, sb, m,ghst) \<rightarrow>\<^sub>s\<^sub>b
         (is,\<theta>, sb', m,ghst)"
by (cases ghst) (simp add: SBWriteVolatile)

lemma SBWrite':
  "\<lbrakk>sb'= sb@[Write\<^sub>s\<^sub>b volatile a (D,f) (f \<theta>) A L R W]\<rbrakk>
   \<Longrightarrow> 
   (Write volatile a (D,f) A L R W# is,\<theta>, sb, m,ghst) \<rightarrow>\<^sub>s\<^sub>b
         (is,\<theta>, sb', m,ghst)"
apply (cases volatile)
apply (auto intro: SBWriteVolatile' SBWriteNonVolatile')
done


lemma SBHRMWReadOnly':
  "\<lbrakk>\<not> cond (\<theta>(t\<mapsto>m a)); ghst = (\<D>, \<O>, \<R>, \<S>); ghst' = (False, \<O>, Map.empty,\<S>)\<rbrakk> \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W# is, \<theta>, [], m, ghst) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h (is, \<theta>(t\<mapsto>m a),[], m, ghst')"
by (simp add: SBHRMWReadOnly)

lemma SBHRMWWrite':
  "\<lbrakk>cond (\<theta>(t\<mapsto>m a)); \<theta>'=\<theta>(t\<mapsto>ret (m a) (f(\<theta>(t\<mapsto>m a))));m'=m(a:= f(\<theta>(t\<mapsto>m a)));
   ghst = (\<D>, \<O>,\<R>, \<S>); ghst'=(False, \<O> \<union> A - R, Map.empty,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)\<rbrakk> \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W# is, \<theta>, [], m, ghst) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
         (is, \<theta>',[], m', ghst')"
  by (simp add: SBHRMWWrite)

lemma SBRMWReadOnly':
  "\<lbrakk>\<not> cond (\<theta>(t\<mapsto>m a)); \<theta>'=\<theta>(t\<mapsto>m a)\<rbrakk> \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W# is, \<theta>, [], m, ghst) \<rightarrow>\<^sub>s\<^sub>b (is, \<theta>',[], m, ghst)"
by (cases ghst) (simp add: SBRMWReadOnly)

lemma SBRMWWrite':
  "\<lbrakk>cond (\<theta>(t\<mapsto>m a)); \<theta>'=\<theta>(t\<mapsto>ret (m a) (f(\<theta>(t\<mapsto>m a))));m'=m(a:= f(\<theta>(t\<mapsto>m a)))\<rbrakk> 
   \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W# is, \<theta>, [], m, ghst) \<rightarrow>\<^sub>s\<^sub>b
         (is, \<theta>',[], m', ghst)"
  by (cases ghst) (simp add: SBRMWWrite)

lemma sim_config':
  "\<lbrakk>m = flush_all_until_volatile_write ts\<^sub>s\<^sub>b\<^sub>h m\<^sub>s\<^sub>b\<^sub>h;
    \<S> = share_all_until_volatile_write ts\<^sub>s\<^sub>b\<^sub>h \<S>\<^sub>s\<^sub>b\<^sub>h;
    length ts\<^sub>s\<^sub>b\<^sub>h = length ts; 
    \<forall>i < length ts\<^sub>s\<^sub>b\<^sub>h. 
           let (p\<^sub>s\<^sub>b\<^sub>h, is\<^sub>s\<^sub>b\<^sub>h, \<theta>\<^sub>s\<^sub>b\<^sub>h, sb, \<D>\<^sub>s\<^sub>b\<^sub>h, \<O>\<^sub>s\<^sub>b\<^sub>h,\<R>\<^sub>s\<^sub>b\<^sub>h) = ts\<^sub>s\<^sub>b\<^sub>h!i;
               execs = takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb;
               suspends = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb
            in  \<exists>is \<D>. instrs suspends @ is\<^sub>s\<^sub>b\<^sub>h = is @ prog_instrs suspends \<and>
                    \<D>\<^sub>s\<^sub>b\<^sub>h = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {}) \<and>
                ts!i = (hd_prog p\<^sub>s\<^sub>b\<^sub>h suspends, 
                        is,
                        \<theta>\<^sub>s\<^sub>b\<^sub>h |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>h - read_tmps suspends),(),
                        \<D>,  
                        acquired True execs \<O>\<^sub>s\<^sub>b\<^sub>h,
                        release execs (dom \<S>\<^sub>s\<^sub>b\<^sub>h) \<R>\<^sub>s\<^sub>b\<^sub>h)
   \<rbrakk> 
    \<Longrightarrow> 
     (ts\<^sub>s\<^sub>b\<^sub>h,m\<^sub>s\<^sub>b\<^sub>h,\<S>\<^sub>s\<^sub>b\<^sub>h) \<sim> (ts,m,\<S>)"
apply (rule sim_config.intros)
apply (simp_all add: Let_def)
done

lemma  AssignAddr':
  "\<lbrakk>\<forall>sop. a \<noteq> Tmp sop; a'=Tmp (eval_expr t a); t'= t + used_tmps a; is=issue_expr t a \<rbrakk> \<Longrightarrow>
   \<theta>\<turnstile> (Assign volatile a e A L R W, t) \<rightarrow>\<^sub>s 
         ((Assign volatile a' e A L R W, t'),is)"
  by (simp add: AssignAddr)


lemma  Assign':
  "\<lbrakk>D \<subseteq> dom \<theta>; is= issue_expr t e@[Write volatile (a \<theta>) (eval_expr t e) (A \<theta>) (L \<theta>) (R \<theta>) (W \<theta>)]\<rbrakk> \<Longrightarrow> 
   \<theta>\<turnstile> (Assign volatile (Tmp (D,a)) e A L R W, t) \<rightarrow>\<^sub>s 
         ((Skip, t + used_tmps e), is)"
  by (simp add: Assign)


lemma CASAddr':
  "\<lbrakk>\<forall>sop. a \<noteq> Tmp sop; a'=(Tmp (eval_expr t a));t'=t + used_tmps a; is=issue_expr t a \<rbrakk> \<Longrightarrow>
   \<theta>\<turnstile> (CAS a c\<^sub>e s\<^sub>e A L R W, t) \<rightarrow>\<^sub>s 
         ((CAS a' c\<^sub>e s\<^sub>e A L R W, t'), is)"
  by (simp add: CASAddr)

lemma CASComp':
  "\<lbrakk>\<forall>sop. c\<^sub>e \<noteq> Tmp sop;c\<^sub>e'=(Tmp (eval_expr t c\<^sub>e));t'=t + used_tmps c\<^sub>e; is= issue_expr t c\<^sub>e \<rbrakk> \<Longrightarrow>
   \<theta>\<turnstile> (CAS (Tmp a) c\<^sub>e s\<^sub>e A L R W, t) \<rightarrow>\<^sub>s 
         ((CAS (Tmp a) c\<^sub>e' s\<^sub>e A L R W, t'), is)"
  by (cases a) (simp add: CASComp)
  
lemma CAS':
  "\<lbrakk>D\<^sub>a \<subseteq> dom \<theta>; D\<^sub>c \<subseteq> dom \<theta>; eval_expr t s\<^sub>e  = (D,f);t'=(t + used_tmps s\<^sub>e); 
   cond = (\<lambda>\<theta>. the (\<theta> t') = c \<theta>);
   ret = (\<lambda>v\<^sub>1 v\<^sub>2. v\<^sub>1);
   is = issue_expr t s\<^sub>e@
           [RMW (a \<theta>) t' (D,f) cond ret 
            (A \<theta>) (L \<theta>) (R \<theta>) (W \<theta>) ]\<rbrakk>  
   \<Longrightarrow>
   \<theta>\<turnstile> (CAS (Tmp (D\<^sub>a,a)) (Tmp (D\<^sub>c,c)) s\<^sub>e A L R W, t) \<rightarrow>\<^sub>s 
         ((Skip, Suc t'),is )"
  by (simp add: CAS)


lemma SCond':
  "\<forall>sop. e \<noteq> Tmp sop \<Longrightarrow> e'= (Tmp (eval_expr t e)) \<Longrightarrow> t'=t + used_tmps e \<Longrightarrow> is=issue_expr t e
   \<Longrightarrow>
   \<theta>\<turnstile> (Cond e s\<^sub>1 s\<^sub>2, t) \<rightarrow>\<^sub>s 
    ((Cond e' s\<^sub>1 s\<^sub>2, t'), is)"
  by (simp add: Cond)

lemma SWhile':
  "s'= (Cond e (Seq s (While e s)) Skip) \<Longrightarrow>
   \<theta>\<turnstile> (While e s, t) \<rightarrow>\<^sub>s ((s', t),[])"
  by (simp add: stmt_step.While)


theorem (in xvalid_program) simulation_hol:
  "(ts\<^sub>s\<^sub>b\<^sub>h,m\<^sub>s\<^sub>b\<^sub>h,\<S>\<^sub>s\<^sub>b\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h (ts\<^sub>s\<^sub>b\<^sub>h',m\<^sub>s\<^sub>b\<^sub>h',\<S>\<^sub>s\<^sub>b\<^sub>h') \<and>
   (ts\<^sub>s\<^sub>b\<^sub>h,m\<^sub>s\<^sub>b\<^sub>h,\<S>\<^sub>s\<^sub>b\<^sub>h) \<sim> (ts,m,\<S>) \<and> safe_reach_direct safe_delayed (ts, m, \<S>) \<and>
   invariant ts\<^sub>s\<^sub>b\<^sub>h \<S>\<^sub>s\<^sub>b\<^sub>h m\<^sub>s\<^sub>b\<^sub>h \<longrightarrow>
  invariant ts\<^sub>s\<^sub>b\<^sub>h' \<S>\<^sub>s\<^sub>b\<^sub>h' m\<^sub>s\<^sub>b\<^sub>h' \<and>
           (\<exists>ts' \<S>' m'. (ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>') \<and> (ts\<^sub>s\<^sub>b\<^sub>h',m\<^sub>s\<^sub>b\<^sub>h',\<S>\<^sub>s\<^sub>b\<^sub>h') \<sim> (ts',m',\<S>'))"
  apply clarify
  apply (drule simulation')
  by auto

theorem (in xvalid_program_progress) store_buffer_execution_result_sequential_consistent'_hol:
"(ts\<^sub>s\<^sub>b,m,x) \<Rightarrow>\<^sub>s\<^sub>b\<^sup>* (ts\<^sub>s\<^sub>b',m',x') \<and>
empty_store_buffers ts\<^sub>s\<^sub>b' \<and>
ts\<^sub>s\<^sub>b \<sim>\<^sub>d ts \<and>
initial\<^sub>v ts \<S> valid \<and>
safe_reach_virtual safe_free_flowing (ts,m,\<S>) 
\<longrightarrow>
(\<exists>ts' \<S>'. 
          (ts,m,\<S>) \<Rightarrow>\<^sub>v\<^sup>* (ts',m',\<S>') \<and> ts\<^sub>s\<^sub>b' \<sim>\<^sub>d ts')"
  apply clarify
  apply (drule store_buffer_execution_result_sequential_consistent')
  apply auto
  done

end
(*>*)

