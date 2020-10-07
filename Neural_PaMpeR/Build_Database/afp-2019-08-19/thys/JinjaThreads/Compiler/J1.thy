(*  Title:      JinjaThreads/Compiler/J1.thy
    Author:     Andreas Lochbihler
*)

section \<open>Semantics of the intermediate language\<close>

theory J1 imports
  J1State
  J1Heap
  "../Framework/FWBisimulation"
begin

abbreviation final_expr1 :: "('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list \<Rightarrow> bool" where
  "final_expr1 \<equiv> \<lambda>(ex, exs). final (fst ex) \<and> exs = []"

definition extNTA2J1 :: 
  "'addr J1_prog \<Rightarrow> (cname \<times> mname \<times> 'addr) \<Rightarrow> (('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list)"
where
  "extNTA2J1 P = (\<lambda>(C, M, a). let (D, _, _, meth) = method P C M; body = the meth
                              in (({0:Class D=None; body}, Addr a # replicate (max_vars body) undefined_value), []))"

lemma extNTA2J1_iff [simp]:
  "extNTA2J1 P (C, M, a) = (({0:Class (fst (method P C M))=None; the (snd (snd (snd (method P C M))))}, Addr a # replicate (max_vars (the (snd (snd (snd (method P C M)))))) undefined_value), [])"
by(simp add: extNTA2J1_def split_beta)

abbreviation extTA2J1 :: 
  "'addr J1_prog \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> ('addr, 'thread_id, 'heap) J1_thread_action"
where "extTA2J1 P \<equiv> convert_extTA (extNTA2J1 P)"

abbreviation (input) extRet2J1 :: "'addr expr1 \<Rightarrow> 'addr extCallRet \<Rightarrow> 'addr expr1"
where "extRet2J1 \<equiv> extRet2J"

lemma max_vars_extRet2J1 [simp]: 
  "max_vars e = 0 \<Longrightarrow> max_vars (extRet2J1 e va) = 0"
by(cases va) simp_all

context J1_heap_base begin

abbreviation J1_start_state :: "'addr J1_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> ('addr, 'thread_id, 'heap) J1_state"
where
  "J1_start_state \<equiv> 
   start_state (\<lambda>C M Ts T body vs. ((blocks1 0 (Class C # Ts) body, Null # vs @ replicate (max_vars body) undefined_value), []))"

inductive red1 :: 
  "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr expr1 \<Rightarrow> 'heap \<times> 'addr locals1 
  \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> 'addr expr1 \<Rightarrow> 'heap \<times> 'addr locals1 \<Rightarrow> bool"
  ("_,_,_ \<turnstile>1 ((1\<langle>_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,51,0,0,0,0,0,0] 81)
  and reds1 ::
  "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr expr1 list \<Rightarrow> 'heap \<times> 'addr locals1
  \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> 'addr expr1 list \<Rightarrow> 'heap \<times> 'addr locals1 \<Rightarrow> bool"
  ("_,_,_ \<turnstile>1 ((1\<langle>_,/_\<rangle>) [-_\<rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,51,0,0,0,0,0,0] 81)
for uf :: bool and P :: "'addr J1_prog" and t :: 'thread_id
where
  Red1New:
  "(h', a) \<in> allocate h (Class_type C)
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>new C, (h, l)\<rangle> -\<lbrace>NewHeapElem a (Class_type C)\<rbrace>\<rightarrow> \<langle>addr a, (h', l)\<rangle>"

| Red1NewFail:
  "allocate h (Class_type C) = {}
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>new C, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW OutOfMemory, (h, l)\<rangle>"

| New1ArrayRed:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>newA T\<lfloor>e\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>newA T\<lfloor>e'\<rceil>, s'\<rangle>"

| Red1NewArray:
  "\<lbrakk> 0 <=s i; (h', a) \<in> allocate h (Array_type T (nat (sint i))) \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, (h, l)\<rangle> -\<lbrace>NewHeapElem a (Array_type T (nat (sint i)))\<rbrace>\<rightarrow> \<langle>addr a, (h', l)\<rangle>"

| Red1NewArrayNegative:
  "i <s 0 \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NegativeArraySize, s\<rangle>"

| Red1NewArrayFail:
  "\<lbrakk> 0 <=s i; allocate h (Array_type T (nat (sint i))) = {} \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>newA T\<lfloor>Val (Intg i)\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW OutOfMemory, (h, l)\<rangle>"

| Cast1Red:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>Cast C e, s\<rangle> -ta\<rightarrow> \<langle>Cast C e', s'\<rangle>"

| Red1Cast:
 "\<lbrakk> typeof\<^bsub>hp s\<^esub> v = \<lfloor>U\<rfloor>; P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>Cast T (Val v), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| Red1CastFail:
  "\<lbrakk> typeof\<^bsub>hp s\<^esub> v = \<lfloor>U\<rfloor>; \<not> P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>Cast T (Val v), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ClassCast, s\<rangle>"

| InstanceOf1Red:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>e instanceof T, s\<rangle> -ta\<rightarrow> \<langle>e' instanceof T, s'\<rangle>"

| Red1InstanceOf:
  "\<lbrakk> typeof\<^bsub>hp s\<^esub> v = \<lfloor>U\<rfloor>; b \<longleftrightarrow> v \<noteq> Null \<and> P \<turnstile> U \<le> T \<rbrakk>
   \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>(Val v) instanceof T, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val (Bool b), s\<rangle>"

| Bin1OpRed1:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>e \<guillemotleft>bop\<guillemotright> e2, s\<rangle> -ta\<rightarrow> \<langle>e' \<guillemotleft>bop\<guillemotright> e2, s'\<rangle>"

| Bin1OpRed2:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e, s\<rangle> -ta\<rightarrow> \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e', s'\<rangle>"

| Red1BinOp:
  "binop bop v1 v2 = Some (Inl v) \<Longrightarrow>
  uf,P,t \<turnstile>1 \<langle>(Val v1) \<guillemotleft>bop\<guillemotright> (Val v2), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| Red1BinOpFail:
  "binop bop v1 v2 = Some (Inr a) \<Longrightarrow>
  uf,P,t \<turnstile>1 \<langle>(Val v1) \<guillemotleft>bop\<guillemotright> (Val v2), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"

| Red1Var:
  "\<lbrakk> (lcl s)!V = v; V < size (lcl s) \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>Var V, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| LAss1Red:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>V:=e, s\<rangle> -ta\<rightarrow> \<langle>V:=e', s'\<rangle>"

| Red1LAss:
  "V < size l
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>V:=(Val v), (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>unit, (h, l[V := v])\<rangle>"

| AAcc1Red1:
  "uf,P,t \<turnstile>1 \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>a\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>a'\<lfloor>i\<rceil>, s'\<rangle>"

| AAcc1Red2:
  "uf,P,t \<turnstile>1 \<langle>i, s\<rangle> -ta\<rightarrow> \<langle>i', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>(Val a)\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>i'\<rceil>, s'\<rangle>"

| Red1AAccNull:
  "uf,P,t \<turnstile>1 \<langle>null\<lfloor>Val i\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| Red1AAccBounds:
  "\<lbrakk> typeof_addr (hp s) a = \<lfloor>Array_type T n\<rfloor>; i <s 0 \<or> sint i \<ge> int n \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayIndexOutOfBounds, s\<rangle>"

| Red1AAcc:
  "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; 0 <=s i; sint i < int n;
     heap_read h a (ACell (nat (sint i))) v \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>(addr a)\<lfloor>Val (Intg i)\<rceil>, (h, xs)\<rangle> -\<lbrace>ReadMem a (ACell (nat (sint i))) v\<rbrace>\<rightarrow> \<langle>Val v, (h, xs)\<rangle>"

| AAss1Red1:
  "uf,P,t \<turnstile>1 \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>a\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>a'\<lfloor>i\<rceil> := e, s'\<rangle>"

| AAss1Red2:
  "uf,P,t \<turnstile>1 \<langle>i, s\<rangle> -ta\<rightarrow> \<langle>i', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>(Val a)\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>i'\<rceil> := e, s'\<rangle>"

| AAss1Red3:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>AAss (Val a) (Val i) e, s\<rangle> -ta\<rightarrow> \<langle>(Val a)\<lfloor>Val i\<rceil> := e', s'\<rangle>"

| Red1AAssNull:
  "uf,P,t \<turnstile>1 \<langle>AAss null (Val i) (Val e), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| Red1AAssBounds:
  "\<lbrakk> typeof_addr (hp s) a = \<lfloor>Array_type T n\<rfloor>; i <s 0 \<or> sint i \<ge> int n \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>AAss (addr a) (Val (Intg i)) (Val e), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayIndexOutOfBounds, s\<rangle>"

| Red1AAssStore:
  "\<lbrakk> typeof_addr (hp s) a = \<lfloor>Array_type T n\<rfloor>; 0 <=s i; sint i < int n;
     typeof\<^bsub>hp s\<^esub> w = \<lfloor>U\<rfloor>; \<not> (P \<turnstile> U \<le> T) \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>AAss (addr a) (Val (Intg i)) (Val w), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ArrayStore, s\<rangle>"

| Red1AAss:
  "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; 0 <=s i; sint i < int n; typeof\<^bsub>h\<^esub> w = Some U; P \<turnstile> U \<le> T;
     heap_write h a (ACell (nat (sint i))) w h' \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>AAss (addr a) (Val (Intg i)) (Val w), (h, l)\<rangle> -\<lbrace>WriteMem a (ACell (nat (sint i))) w\<rbrace>\<rightarrow> \<langle>unit, (h', l)\<rangle>"

| ALength1Red:
  "uf,P,t \<turnstile>1 \<langle>a, s\<rangle> -ta\<rightarrow> \<langle>a', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>a\<bullet>length, s\<rangle> -ta\<rightarrow> \<langle>a'\<bullet>length, s'\<rangle>"

| Red1ALength:
  "typeof_addr h a = \<lfloor>Array_type T n\<rfloor> 
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>addr a\<bullet>length, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>Val (Intg (word_of_int (int n))), (h, xs)\<rangle>"

| Red1ALengthNull:
  "uf,P,t \<turnstile>1 \<langle>null\<bullet>length, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| FAcc1Red:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>e\<bullet>F{D}, s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>F{D}, s'\<rangle>"

| Red1FAcc:
  "heap_read h a (CField D F) v
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>(addr a)\<bullet>F{D}, (h, xs)\<rangle> -\<lbrace>ReadMem a (CField D F) v\<rbrace>\<rightarrow> \<langle>Val v, (h, xs)\<rangle>"

| Red1FAccNull:
  "uf,P,t \<turnstile>1 \<langle>null\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| FAss1Red1:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>e\<bullet>F{D}:=e2, s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>F{D}:=e2, s'\<rangle>"

| FAss1Red2:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>FAss (Val v) F D e, s\<rangle> -ta\<rightarrow> \<langle>Val v\<bullet>F{D}:=e', s'\<rangle>"

| Red1FAss:
  "heap_write h a (CField D F) v h' \<Longrightarrow>
  uf,P,t \<turnstile>1 \<langle>FAss (addr a) F D (Val v), (h, l)\<rangle> -\<lbrace>WriteMem a (CField D F) v\<rbrace>\<rightarrow> \<langle>unit, (h', l)\<rangle>"

| Red1FAssNull:
  "uf,P,t \<turnstile>1 \<langle>FAss null F D (Val v), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| CAS1Red1:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow>
  uf,P,t \<turnstile>1 \<langle>e\<bullet>compareAndSwap(D\<bullet>F, e2, e3), s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>compareAndSwap(D\<bullet>F, e2, e3), s'\<rangle>"

| CAS1Red2:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow>
  uf,P,t \<turnstile>1 \<langle>Val v\<bullet>compareAndSwap(D\<bullet>F, e, e3), s\<rangle> -ta\<rightarrow> \<langle>Val v\<bullet>compareAndSwap(D\<bullet>F, e', e3), s'\<rangle>"

| CAS1Red3:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow>
  uf,P,t \<turnstile>1 \<langle>Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e), s\<rangle> -ta\<rightarrow> \<langle>Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e'), s'\<rangle>"

| CAS1Null:
  "uf,P,t \<turnstile>1 \<langle>null\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v'), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| Red1CASSucceed:
  "\<lbrakk> heap_read h a (CField D F) v; heap_write h a (CField D F) v' h' \<rbrakk> \<Longrightarrow>
  uf,P,t \<turnstile>1 \<langle>addr a\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v'), (h, l)\<rangle> 
  -\<lbrace>ReadMem a (CField D F) v, WriteMem a (CField D F) v'\<rbrace>\<rightarrow> 
  \<langle>true, (h', l)\<rangle>"

| Red1CASFail:
  "\<lbrakk> heap_read h a (CField D F) v''; v \<noteq> v'' \<rbrakk> \<Longrightarrow>
  uf,P,t \<turnstile>1 \<langle>addr a\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v'), (h, l)\<rangle> 
  -\<lbrace>ReadMem a (CField D F) v''\<rbrace>\<rightarrow> 
  \<langle>false, (h, l)\<rangle>"

| Call1Obj:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>e\<bullet>M(es), s\<rangle> -ta\<rightarrow> \<langle>e'\<bullet>M(es), s'\<rangle>"

| Call1Params:
  "uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
  uf,P,t \<turnstile>1 \<langle>(Val v)\<bullet>M(es),s\<rangle> -ta\<rightarrow> \<langle>(Val v)\<bullet>M(es'),s'\<rangle>"

| Red1CallExternal:
  "\<lbrakk> typeof_addr (hp s) a = \<lfloor>T\<rfloor>; P \<turnstile> class_type_of T sees M:Ts\<rightarrow>Tr = Native in D; P,t \<turnstile> \<langle>a\<bullet>M(vs), hp s\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>;
     e' = extRet2J1 ((addr a)\<bullet>M(map Val vs)) va; s' = (h', lcl s) \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>(addr a)\<bullet>M(map Val vs), s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"

| Red1CallNull:
  "uf,P,t \<turnstile>1 \<langle>null\<bullet>M(map Val vs), s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| Block1Some:
  "V < length x \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>{V:T=\<lfloor>v\<rfloor>; e}, (h, x)\<rangle> -\<epsilon>\<rightarrow> \<langle>{V:T=None; e}, (h, x[V := v])\<rangle>"

| Block1Red:
  "uf,P,t \<turnstile>1 \<langle>e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>{V:T=None; e}, (h, x)\<rangle> -ta\<rightarrow> \<langle>{V:T=None; e'}, (h', x')\<rangle>"

| Red1Block:
  "uf,P,t \<turnstile>1 \<langle>{V:T=None; Val u}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val u, s\<rangle>"

| Synchronized1Red1:
  "uf,P,t \<turnstile>1 \<langle>o', s\<rangle> -ta\<rightarrow> \<langle>o'', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (o') e, s\<rangle> -ta\<rightarrow> \<langle>sync\<^bsub>V\<^esub> (o'') e, s'\<rangle>"

| Synchronized1Null:
  "V < length xs \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (null) e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h, xs[V := Null])\<rangle>"

| Lock1Synchronized:
  "V < length xs \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (addr a) e, (h, xs)\<rangle> -\<lbrace>Lock\<rightarrow>a, SyncLock a\<rbrace>\<rightarrow> \<langle>insync\<^bsub>V\<^esub> (a) e, (h, xs[V := Addr a])\<rangle>"

| Synchronized1Red2:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) e, s\<rangle> -ta\<rightarrow> \<langle>insync\<^bsub>V\<^esub> (a) e', s'\<rangle>"

| Unlock1Synchronized:
  "\<lbrakk> xs ! V = Addr a'; V < length xs \<rbrakk> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) (Val v), (h, xs)\<rangle> -\<lbrace>Unlock\<rightarrow>a', SyncUnlock a'\<rbrace>\<rightarrow> \<langle>Val v, (h, xs)\<rangle>"

| Unlock1SynchronizedNull:
  "\<lbrakk> xs ! V = Null; V < length xs \<rbrakk> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) (Val v), (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h, xs)\<rangle>"

| Unlock1SynchronizedFail:
  "\<lbrakk> uf; xs ! V = Addr a'; V < length xs \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) (Val v), (h, xs)\<rangle> -\<lbrace>UnlockFail\<rightarrow>a'\<rbrace>\<rightarrow> \<langle>THROW IllegalMonitorState, (h, xs)\<rangle>"

| Seq1Red:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>e;;e2, s\<rangle> -ta\<rightarrow> \<langle>e';;e2, s'\<rangle>"

| Red1Seq:
  "uf,P,t \<turnstile>1 \<langle>Seq (Val v) e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e, s\<rangle>"

| Cond1Red:
  "uf,P,t \<turnstile>1 \<langle>b, s\<rangle> -ta\<rightarrow> \<langle>b', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>if (b) e1 else e2, s\<rangle> -ta\<rightarrow> \<langle>if (b') e1 else e2, s'\<rangle>"

| Red1CondT:
  "uf,P,t \<turnstile>1 \<langle>if (true) e1 else e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e1, s\<rangle>"

| Red1CondF:
  "uf,P,t \<turnstile>1 \<langle>if (false) e1 else e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e2, s\<rangle>"

| Red1While:
  "uf,P,t \<turnstile>1 \<langle>while(b) c, s\<rangle> -\<epsilon>\<rightarrow> \<langle>if (b) (c;;while(b) c) else unit, s\<rangle>"

| Throw1Red:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>throw e, s\<rangle> -ta\<rightarrow> \<langle>throw e', s'\<rangle>"

| Red1ThrowNull:
  "uf,P,t \<turnstile>1 \<langle>throw null, s\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| Try1Red:
  "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>try e catch(C V) e2, s\<rangle> -ta\<rightarrow> \<langle>try e' catch(C V) e2, s'\<rangle>"

| Red1Try:
  "uf,P,t \<turnstile>1 \<langle>try (Val v) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v, s\<rangle>"

| Red1TryCatch:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type D\<rfloor>; P \<turnstile> D \<preceq>\<^sup>* C; V < length x \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>try (Throw a) catch(C V) e2, (h, x)\<rangle> -\<epsilon>\<rightarrow> \<langle>{V:Class C=None; e2}, (h, x[V := Addr a])\<rangle>"

| Red1TryFail:
  "\<lbrakk> typeof_addr (hp s) a = \<lfloor>Class_type D\<rfloor>; \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>try (Throw a) catch(C V) e2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"

| List1Red1:
  "uf,P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  uf,P,t \<turnstile>1 \<langle>e#es,s\<rangle> [-ta\<rightarrow>] \<langle>e'#es,s'\<rangle>"

| List1Red2:
  "uf,P,t \<turnstile>1 \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
  uf,P,t \<turnstile>1 \<langle>Val v # es,s\<rangle> [-ta\<rightarrow>] \<langle>Val v # es',s'\<rangle>"

| New1ArrayThrow: "uf,P,t \<turnstile>1 \<langle>newA T\<lfloor>Throw a\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Cast1Throw: "uf,P,t \<turnstile>1 \<langle>Cast C (Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| InstanceOf1Throw: "uf,P,t \<turnstile>1 \<langle>(Throw a) instanceof T, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Bin1OpThrow1: "uf,P,t \<turnstile>1 \<langle>(Throw a) \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Bin1OpThrow2: "uf,P,t \<turnstile>1 \<langle>(Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> (Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| LAss1Throw: "uf,P,t \<turnstile>1 \<langle>V:=(Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAcc1Throw1: "uf,P,t \<turnstile>1 \<langle>(Throw a)\<lfloor>i\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAcc1Throw2: "uf,P,t \<turnstile>1 \<langle>(Val v)\<lfloor>Throw a\<rceil>, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAss1Throw1: "uf,P,t \<turnstile>1 \<langle>(Throw a)\<lfloor>i\<rceil> := e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAss1Throw2: "uf,P,t \<turnstile>1 \<langle>(Val v)\<lfloor>Throw a\<rceil> := e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| AAss1Throw3: "uf,P,t \<turnstile>1 \<langle>AAss (Val v) (Val i) (Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| ALength1Throw: "uf,P,t \<turnstile>1 \<langle>(Throw a)\<bullet>length, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| FAcc1Throw: "uf,P,t \<turnstile>1 \<langle>(Throw a)\<bullet>F{D}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| FAss1Throw1: "uf,P,t \<turnstile>1 \<langle>(Throw a)\<bullet>F{D}:=e\<^sub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| FAss1Throw2: "uf,P,t \<turnstile>1 \<langle>FAss (Val v) F D (Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| CAS1Throw: "uf,P,t \<turnstile>1 \<langle>Throw a\<bullet>compareAndSwap(D\<bullet>F, e2, e3), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| CAS1Throw2: "uf,P,t \<turnstile>1 \<langle>Val v\<bullet>compareAndSwap(D\<bullet>F, Throw a, e3), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| CAS1Throw3: "uf,P,t \<turnstile>1 \<langle>Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Call1ThrowObj: "uf,P,t \<turnstile>1 \<langle>(Throw a)\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Call1ThrowParams: "\<lbrakk> es = map Val vs @ Throw a # es' \<rbrakk> \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>(Val v)\<bullet>M(es), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Block1Throw: "uf,P,t \<turnstile>1 \<langle>{V:T=None; Throw a}, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Synchronized1Throw1: "uf,P,t \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (Throw a) e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Synchronized1Throw2:
  "\<lbrakk> xs ! V = Addr a'; V < length xs \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw ad, (h, xs)\<rangle> -\<lbrace>Unlock\<rightarrow>a', SyncUnlock a'\<rbrace>\<rightarrow> \<langle>Throw ad, (h, xs)\<rangle>"
| Synchronized1Throw2Fail:
  "\<lbrakk> uf; xs ! V = Addr a'; V < length xs \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw ad, (h, xs)\<rangle> -\<lbrace>UnlockFail\<rightarrow>a'\<rbrace>\<rightarrow> \<langle>THROW IllegalMonitorState, (h, xs)\<rangle>"
| Synchronized1Throw2Null:
  "\<lbrakk> xs ! V = Null; V < length xs \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw ad, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h, xs)\<rangle>"
| Seq1Throw: "uf,P,t \<turnstile>1 \<langle>(Throw a);;e\<^sub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Cond1Throw: "uf,P,t \<turnstile>1 \<langle>if (Throw a) e\<^sub>1 else e\<^sub>2, s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"
| Throw1Throw: "uf,P,t \<turnstile>1 \<langle>throw(Throw a), s\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, s\<rangle>"

inductive_cases red1_cases:
  "uf,P,t \<turnstile>1 \<langle>new C, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>new T\<lfloor>e\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>e \<guillemotleft>bop\<guillemotright> e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>Var V, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>V:=e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>a\<lfloor>i\<rceil>, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>a\<lfloor>i\<rceil> := e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>a\<bullet>length, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>e\<bullet>F{D}, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>e\<bullet>F{D} := e2, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>e\<bullet>compareAndSwap(D\<bullet>F, e', e''), s\<rangle> -ta\<rightarrow> \<langle>e''', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>e\<bullet>M(es), s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>{V:T=vo; e}, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (o') e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>e;;e', s\<rangle> -ta\<rightarrow> \<langle>e'', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>throw e, s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  "uf,P,t \<turnstile>1 \<langle>try e catch(C V) e'', s \<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"

inductive Red1 ::
  "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> ('addr expr1 \<times> 'addr locals1) list \<Rightarrow> 'heap
  \<Rightarrow> ('addr, 'thread_id, 'heap) J1_thread_action
  \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> ('addr expr1 \<times> 'addr locals1) list \<Rightarrow> 'heap \<Rightarrow> bool"
  ("_,_,_ \<turnstile>1 ((1\<langle>_'/_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_'/_,/_\<rangle>))" [51,51,0,0,0,0,0,0,0,0] 81)
for uf :: bool and P :: "'addr J1_prog" and t :: 'thread_id
where

  red1Red:
  "uf,P,t \<turnstile>1 \<langle>e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>(e, x)/exs, h\<rangle> -extTA2J1 P ta\<rightarrow> \<langle>(e', x')/exs, h'\<rangle>"

| red1Call:
  "\<lbrakk> call1 e = \<lfloor>(a, M, vs)\<rfloor>; typeof_addr h a = \<lfloor>U\<rfloor>; 
     P \<turnstile> class_type_of U sees M:Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D; 
     size vs = size Ts \<rbrakk>
  \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>(e, x)/exs, h\<rangle> -\<epsilon>\<rightarrow> \<langle>(blocks1 0 (Class D#Ts) body, Addr a # vs @ replicate (max_vars body) undefined_value)/(e, x)#exs, h\<rangle>"

| red1Return:
  "final e' \<Longrightarrow> uf,P,t \<turnstile>1 \<langle>(e', x')/(e, x)#exs, h\<rangle> -\<epsilon>\<rightarrow> \<langle>(inline_call e' e, x)/exs, h\<rangle>"

abbreviation mred1g :: "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> ('addr,'thread_id,('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list,'heap,'addr,('addr, 'thread_id) obs_event) semantics"
where "mred1g uf P \<equiv> \<lambda>t ((ex, exs), h) ta ((ex', exs'), h'). uf,P,t \<turnstile>1 \<langle>ex/exs, h\<rangle> -ta\<rightarrow> \<langle>ex'/exs', h'\<rangle>"

abbreviation mred1' :: 
  "'addr J1_prog \<Rightarrow> ('addr,'thread_id,('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list,'heap,'addr,('addr, 'thread_id) obs_event) semantics"
where "mred1' \<equiv> mred1g False"

abbreviation mred1 :: 
  "'addr J1_prog \<Rightarrow> ('addr,'thread_id,('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list,'heap,'addr,('addr, 'thread_id) obs_event) semantics"
where "mred1 \<equiv> mred1g True"

lemma red1_preserves_len: "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> length (lcl s') = length (lcl s)"
  and reds1_preserves_len: "uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> length (lcl s') = length (lcl s)"
by(induct rule: red1_reds1.inducts)(auto)

lemma reds1_preserves_elen: "uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> length es' = length es"
by(induct es arbitrary: es')(auto elim: reds1.cases)

lemma red1_Val_iff [iff]:
  "\<not> uf,P,t \<turnstile>1 \<langle>Val v, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
by(auto elim: red1.cases)

lemma red1_Throw_iff [iff]:
  "\<not> uf,P,t \<turnstile>1 \<langle>Throw a, xs\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
by(auto elim: red1.cases)

lemma reds1_Nil_iff [iff]:
  "\<not> uf,P,t \<turnstile>1 \<langle>[], s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>"
by(auto elim: reds1.cases)

lemma reds1_Val_iff [iff]:
  "\<not> uf,P,t \<turnstile>1 \<langle>map Val vs, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>"
by(induct vs arbitrary: es')(auto elim: reds1.cases)

lemma reds1_map_Val_Throw_iff [iff]:
  "\<not> uf,P,t \<turnstile>1 \<langle>map Val vs @ Throw a # es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>"
by(induct vs arbitrary: es')(auto elim: reds1.cases elim!: red1_cases)

lemma red1_max_vars_decr: "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> max_vars e' \<le> max_vars e" 
  and reds1_max_varss_decr: "uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> max_varss es' \<le> max_varss es"
by(induct rule: red1_reds1.inducts)(auto)

lemma red1_new_thread_heap: "\<lbrakk>uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t' ex h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h = hp s'"
  and reds1_new_thread_heap: "\<lbrakk>uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t' ex h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h = hp s'"
apply(induct rule: red1_reds1.inducts)
apply(fastforce dest: red_ext_new_thread_heap simp add: ta_upd_simps)+
done

lemma red1_new_threadD:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t' x H \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>a M vs va T Ts Tr D. P,t \<turnstile> \<langle>a\<bullet>M(vs), hp s\<rangle> -ta\<rightarrow>ext \<langle>va, hp s'\<rangle> \<and> typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<and> P \<turnstile> class_type_of T sees M:Ts\<rightarrow>Tr = Native in D"
  and reds1_new_threadD:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t' x H \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>a M vs va T Ts Tr D. P,t \<turnstile> \<langle>a\<bullet>M(vs), hp s\<rangle> -ta\<rightarrow>ext \<langle>va, hp s'\<rangle> \<and> typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<and> P \<turnstile> class_type_of T sees M:Ts\<rightarrow>Tr = Native in D"
by(induct rule: red1_reds1.inducts)(fastforce simp add: ta_upd_simps)+

lemma red1_call_synthesized: "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; call1 e = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> synthesized_call P (hp s) aMvs"
  and reds1_calls_synthesized: "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; calls1 es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> synthesized_call P (hp s) aMvs"
apply(induct rule: red1_reds1.inducts)
apply(auto split: if_split_asm simp add: is_vals_conv append_eq_map_conv synthesized_call_conv)
apply blast
done

lemma red1_preserves_B: "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<B> e n\<rbrakk> \<Longrightarrow> \<B> e' n"
  and reds1_preserves_Bs: "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<B>s es n\<rbrakk> \<Longrightarrow> \<B>s es' n"
by(induct arbitrary: n and n rule: red1_reds1.inducts)(auto)

end

context J1_heap begin

lemma red1_hext_incr: "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> hext (hp s) (hp s')"
  and reds1_hext_incr: "uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> hext (hp s) (hp s')"
by(induct rule: red1_reds1.inducts)(auto intro: hext_heap_ops red_external_hext)

lemma Red1_hext_incr: "uf,P,t \<turnstile>1 \<langle>ex/exs,h\<rangle> -ta\<rightarrow> \<langle>ex'/exs',h'\<rangle> \<Longrightarrow> h \<unlhd> h'"
by(auto elim!: Red1.cases dest: red1_hext_incr)

end

subsection \<open>Silent moves\<close>

context J1_heap_base begin 

primrec \<tau>move1 :: "'m prog \<Rightarrow> 'heap \<Rightarrow> ('a, 'b, 'addr) exp \<Rightarrow> bool"
  and \<tau>moves1 :: "'m prog \<Rightarrow> 'heap \<Rightarrow> ('a, 'b, 'addr) exp list \<Rightarrow> bool"
where
  "\<tau>move1 P h (new C) \<longleftrightarrow> False"
| "\<tau>move1 P h (newA T\<lfloor>e\<rceil>) \<longleftrightarrow> \<tau>move1 P h e \<or> (\<exists>a. e = Throw a)"
| "\<tau>move1 P h (Cast U e) \<longleftrightarrow> \<tau>move1 P h e \<or> final e"
| "\<tau>move1 P h (e instanceof T) \<longleftrightarrow> \<tau>move1 P h e \<or> final e"
| "\<tau>move1 P h (e \<guillemotleft>bop\<guillemotright> e') \<longleftrightarrow> \<tau>move1 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v \<and> (\<tau>move1 P h e' \<or> final e'))"
| "\<tau>move1 P h (Val v) \<longleftrightarrow> False"
| "\<tau>move1 P h (Var V) \<longleftrightarrow> True"
| "\<tau>move1 P h (V := e) \<longleftrightarrow> \<tau>move1 P h e \<or> final e"
| "\<tau>move1 P h (a\<lfloor>i\<rceil>) \<longleftrightarrow> \<tau>move1 P h a \<or> (\<exists>ad. a = Throw ad) \<or> (\<exists>v. a = Val v \<and> (\<tau>move1 P h i \<or> (\<exists>a. i = Throw a)))"
| "\<tau>move1 P h (AAss a i e) \<longleftrightarrow> \<tau>move1 P h a \<or> (\<exists>ad. a = Throw ad) \<or> (\<exists>v. a = Val v \<and> (\<tau>move1 P h i \<or> (\<exists>a. i = Throw a) \<or> (\<exists>v. i = Val v \<and> (\<tau>move1 P h e \<or> (\<exists>a. e = Throw a)))))"
| "\<tau>move1 P h (a\<bullet>length) \<longleftrightarrow> \<tau>move1 P h a \<or> (\<exists>ad. a = Throw ad)"
| "\<tau>move1 P h (e\<bullet>F{D}) \<longleftrightarrow> \<tau>move1 P h e \<or> (\<exists>a. e = Throw a)"
| "\<tau>move1 P h (FAss e F D e') \<longleftrightarrow> \<tau>move1 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v \<and> (\<tau>move1 P h e' \<or> (\<exists>a. e' = Throw a)))"
| "\<tau>move1 P h (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) \<longleftrightarrow> \<tau>move1 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v \<and> 
  (\<tau>move1 P h e' \<or> (\<exists>a. e' = Throw a) \<or> (\<exists>v. e' = Val v \<and> (\<tau>move1 P h e'' \<or> (\<exists>a. e'' = Throw a)))))"
| "\<tau>move1 P h (e\<bullet>M(es)) \<longleftrightarrow> \<tau>move1 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v \<and> 
   (\<tau>moves1 P h es \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es') \<or> 
    (\<exists>vs. es = map Val vs \<and> (v = Null \<or> (\<forall>T C Ts Tr D. typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor> \<longrightarrow> class_type_of' T = \<lfloor>C\<rfloor> \<longrightarrow> P \<turnstile> C sees M:Ts\<rightarrow>Tr = Native in D \<longrightarrow> \<tau>external_defs D M)))))"
| "\<tau>move1 P h ({V:T=vo; e}) \<longleftrightarrow> vo \<noteq> None \<or> \<tau>move1 P h e \<or> final e"
| "\<tau>move1 P h (sync\<^bsub>V'\<^esub>(e) e') \<longleftrightarrow> \<tau>move1 P h e \<or> (\<exists>a. e = Throw a)"
| "\<tau>move1 P h (insync\<^bsub>V'\<^esub>(ad) e) \<longleftrightarrow> \<tau>move1 P h e"
| "\<tau>move1 P h (e;;e') \<longleftrightarrow> \<tau>move1 P h e \<or> final e"
| "\<tau>move1 P h (if (e) e' else e'') \<longleftrightarrow> \<tau>move1 P h e \<or> final e"
| "\<tau>move1 P h (while (e) e') = True"
| "\<tau>move1 P h (throw e) \<longleftrightarrow> \<tau>move1 P h e \<or> (\<exists>a. e = Throw a) \<or> e = null"
| "\<tau>move1 P h (try e catch(C V) e') \<longleftrightarrow> \<tau>move1 P h e \<or> final e"

| "\<tau>moves1 P h [] \<longleftrightarrow> False"
| "\<tau>moves1 P h (e # es) \<longleftrightarrow> \<tau>move1 P h e \<or> (\<exists>v. e = Val v \<and> \<tau>moves1 P h es)"

fun \<tau>Move1 :: "'m prog \<Rightarrow> 'heap \<Rightarrow> (('a, 'b, 'addr) exp \<times> 'c) \<times> (('a, 'b, 'addr) exp \<times> 'd) list \<Rightarrow> bool"
where
  "\<tau>Move1 P h ((e, x), exs) = (\<tau>move1 P h e \<or> final e)"

definition \<tau>red1g :: "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>red1g uf P t h exs e'xs' = (uf,P,t \<turnstile>1 \<langle>fst exs, (h, snd exs)\<rangle> -\<epsilon>\<rightarrow> \<langle>fst e'xs', (h, snd e'xs')\<rangle> \<and> \<tau>move1 P h (fst exs))"

definition \<tau>reds1g :: 
  "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> bool"
where
  "\<tau>reds1g uf P t h esxs es'xs' =
   (uf,P,t \<turnstile>1 \<langle>fst esxs, (h, snd esxs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>fst es'xs', (h, snd es'xs')\<rangle> \<and> \<tau>moves1 P h (fst esxs))"

abbreviation \<tau>red1gt :: 
  "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>red1gt uf P t h \<equiv> (\<tau>red1g uf P t h)^++"

abbreviation \<tau>reds1gt ::
  "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>reds1gt uf P t h \<equiv> (\<tau>reds1g uf P t h)^++"

abbreviation \<tau>red1gr ::
  "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>red1gr uf P t h \<equiv> (\<tau>red1g uf P t h)^**"

abbreviation \<tau>reds1gr ::
  "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>reds1gr uf P t h \<equiv> (\<tau>reds1g uf P t h)^**"

definition \<tau>Red1g ::
  "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list)
  \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) \<Rightarrow> bool"
where "\<tau>Red1g uf P t h exexs ex'exs' = (uf,P,t \<turnstile>1 \<langle>fst exexs/snd exexs, h\<rangle> -\<epsilon>\<rightarrow> \<langle>fst ex'exs'/snd ex'exs', h\<rangle> \<and> \<tau>Move1 P h exexs)"

abbreviation \<tau>Red1gt ::
  "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) 
  \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) \<Rightarrow> bool"
where "\<tau>Red1gt uf P t h \<equiv> (\<tau>Red1g uf P t h)^++"

abbreviation \<tau>Red1gr :: 
  "bool \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) 
  \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) \<Rightarrow> bool"
where "\<tau>Red1gr uf P t h \<equiv> (\<tau>Red1g uf P t h)^**"

abbreviation \<tau>red1 :: 
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>red1 \<equiv> \<tau>red1g True"

abbreviation \<tau>reds1 :: 
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>reds1 \<equiv> \<tau>reds1g True"

abbreviation \<tau>red1t :: 
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>red1t \<equiv> \<tau>red1gt True"

abbreviation \<tau>reds1t ::
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>reds1t \<equiv> \<tau>reds1gt True"

abbreviation \<tau>red1r ::
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>red1r \<equiv> \<tau>red1gr True"

abbreviation \<tau>reds1r ::
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>reds1r \<equiv> \<tau>reds1gr True"

abbreviation \<tau>Red1 ::
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list)
  \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) \<Rightarrow> bool"
where "\<tau>Red1 \<equiv> \<tau>Red1g True"

abbreviation \<tau>Red1t ::
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) 
  \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) \<Rightarrow> bool"
where "\<tau>Red1t \<equiv> \<tau>Red1gt True"

abbreviation \<tau>Red1r :: 
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) 
  \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) \<Rightarrow> bool"
where "\<tau>Red1r \<equiv> \<tau>Red1gr True"

abbreviation \<tau>red1' :: 
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>red1' \<equiv> \<tau>red1g False"

abbreviation \<tau>reds1' :: 
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>reds1' \<equiv> \<tau>reds1g False"

abbreviation \<tau>red1't ::
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>red1't \<equiv> \<tau>red1gt False"

abbreviation \<tau>reds1't :: 
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>reds1't \<equiv> \<tau>reds1gt False"

abbreviation \<tau>red1'r ::
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>red1'r \<equiv> \<tau>red1gr False"

abbreviation \<tau>reds1'r :: 
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> ('addr expr1 list \<times> 'addr locals1) \<Rightarrow> bool"
where "\<tau>reds1'r \<equiv> \<tau>reds1gr False"

abbreviation \<tau>Red1' ::
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) 
  \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) \<Rightarrow> bool"
where "\<tau>Red1' \<equiv> \<tau>Red1g False"

abbreviation \<tau>Red1't ::
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) 
  \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) \<Rightarrow> bool"
where "\<tau>Red1't \<equiv> \<tau>Red1gt False"

abbreviation \<tau>Red1'r :: 
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) 
  \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> (('addr expr1 \<times> 'addr locals1) list) \<Rightarrow> bool"
where "\<tau>Red1'r \<equiv> \<tau>Red1gr False"

abbreviation \<tau>MOVE1 :: 
  "'m prog \<Rightarrow> ((('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list) \<times> 'heap, ('addr, 'thread_id, 'heap) J1_thread_action) trsys"
where "\<tau>MOVE1 P \<equiv> \<lambda>(exexs, h) ta s. \<tau>Move1 P h exexs \<and> ta = \<epsilon>"

lemma \<tau>move1_\<tau>moves1_intros:
  fixes e :: "('a, 'b, 'addr) exp" and es :: "('a, 'b, 'addr) exp list"
  shows \<tau>move1NewArray: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (newA T\<lfloor>e\<rceil>)"
  and \<tau>move1Cast: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (Cast U e)"
  and \<tau>move1CastRed: "\<tau>move1 P h (Cast U (Val v))"
  and \<tau>move1InstanceOf: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (e instanceof U)"
  and \<tau>move1InstanceOfRed: "\<tau>move1 P h ((Val v) instanceof U)"
  and \<tau>move1BinOp1: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (e\<guillemotleft>bop\<guillemotright>e')"
  and \<tau>move1BinOp2: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (Val v\<guillemotleft>bop\<guillemotright>e)"
  and \<tau>move1BinOp: "\<tau>move1 P h (Val v\<guillemotleft>bop\<guillemotright>Val v')"
  and \<tau>move1Var: "\<tau>move1 P h (Var V)"
  and \<tau>move1LAss: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (V := e)"
  and \<tau>move1LAssRed: "\<tau>move1 P h (V := Val v)"
  and \<tau>move1AAcc1: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (e\<lfloor>e'\<rceil>)"
  and \<tau>move1AAcc2: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (Val v\<lfloor>e\<rceil>)"
  and \<tau>move1AAss1: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (AAss e e' e'')"
  and \<tau>move1AAss2: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (AAss (Val v) e e')"
  and \<tau>move1AAss3: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (AAss (Val v) (Val v') e)"
  and \<tau>move1ALength: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (e\<bullet>length)"
  and \<tau>move1FAcc: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (e\<bullet>F{D})"
  and \<tau>move1FAss1: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (FAss e F D e')"
  and \<tau>move1FAss2: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (FAss (Val v) F D e)"
  and \<tau>move1CAS1: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (e\<bullet>compareAndSwap(D\<bullet>F, e', e''))"
  and \<tau>move1CAS2: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (Val v\<bullet>compareAndSwap(D\<bullet>F, e, e''))"
  and \<tau>move1CAS3: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e))"
  and \<tau>move1CallObj: "\<tau>move1 P h obj \<Longrightarrow> \<tau>move1 P h (obj\<bullet>M(ps))"
  and \<tau>move1CallParams: "\<tau>moves1 P h ps \<Longrightarrow> \<tau>move1 P h (Val v\<bullet>M(ps))"
  and \<tau>move1Call: "(\<And>T C Ts Tr D. \<lbrakk> typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>; class_type_of' T = \<lfloor>C\<rfloor>; P \<turnstile> C sees M:Ts\<rightarrow>Tr = Native in D \<rbrakk> \<Longrightarrow> \<tau>external_defs D M) \<Longrightarrow> \<tau>move1 P h (Val v\<bullet>M(map Val vs))"
  and \<tau>move1BlockSome: "\<tau>move1 P h {V:T=\<lfloor>v\<rfloor>; e}"
  and \<tau>move1Block: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h {V:T=None; e}"
  and \<tau>move1BlockRed: "\<tau>move1 P h {V:T=None; Val v}"
  and \<tau>move1Sync: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (sync\<^bsub>V'\<^esub> (e) e')"
  and \<tau>move1InSync: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (insync\<^bsub>V'\<^esub> (a) e)"
  and \<tau>move1Seq: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (e;;e')"
  and \<tau>move1SeqRed: "\<tau>move1 P h (Val v;; e)"
  and \<tau>move1Cond: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (if (e) e1 else e2)"
  and \<tau>move1CondRed: "\<tau>move1 P h (if (Val v) e1 else e2)"
  and \<tau>move1WhileRed: "\<tau>move1 P h (while (c) e)"
  and \<tau>move1Throw: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (throw e)"
  and \<tau>move1ThrowNull: "\<tau>move1 P h (throw null)"
  and \<tau>move1Try: "\<tau>move1 P h e \<Longrightarrow> \<tau>move1 P h (try e catch(C V) e'')"
  and \<tau>move1TryRed: "\<tau>move1 P h (try Val v catch(C V) e)"
  and \<tau>move1TryThrow: "\<tau>move1 P h (try Throw a catch(C V) e)"
  and \<tau>move1NewArrayThrow: "\<tau>move1 P h (newA T\<lfloor>Throw a\<rceil>)"
  and \<tau>move1CastThrow: "\<tau>move1 P h (Cast T (Throw a))"
  and \<tau>move1InstanceOfThrow: "\<tau>move1 P h ((Throw a) instanceof T)"
  and \<tau>move1BinOpThrow1: "\<tau>move1 P h (Throw a \<guillemotleft>bop\<guillemotright> e2)"
  and \<tau>move1BinOpThrow2: "\<tau>move1 P h (Val v \<guillemotleft>bop\<guillemotright> Throw a)"
  and \<tau>move1LAssThrow: "\<tau>move1 P h (V:=(Throw a))"
  and \<tau>move1AAccThrow1: "\<tau>move1 P h (Throw a\<lfloor>e\<rceil>)"
  and \<tau>move1AAccThrow2: "\<tau>move1 P h (Val v\<lfloor>Throw a\<rceil>)"
  and \<tau>move1AAssThrow1: "\<tau>move1 P h (AAss (Throw a) e e')"
  and \<tau>move1AAssThrow2: "\<tau>move1 P h (AAss (Val v) (Throw a) e')"
  and \<tau>move1AAssThrow3: "\<tau>move1 P h (AAss (Val v) (Val v') (Throw a))"
  and \<tau>move1ALengthThrow: "\<tau>move1 P h (Throw a\<bullet>length)"
  and \<tau>move1FAccThrow: "\<tau>move1 P h (Throw a\<bullet>F{D})"
  and \<tau>move1FAssThrow1: "\<tau>move1 P h (Throw a\<bullet>F{D} := e)"
  and \<tau>move1FAssThrow2: "\<tau>move1 P h (FAss (Val v) F D (Throw a))"
  and \<tau>move1CASThrow1: "\<tau>move1 P h (CompareAndSwap (Throw a) D F e e')"
  and \<tau>move1CASThrow2: "\<tau>move1 P h (CompareAndSwap (Val v) D F (Throw a) e')"
  and \<tau>move1CASThrow3: "\<tau>move1 P h (CompareAndSwap (Val v) D F (Val v') (Throw a))"
  and \<tau>move1CallThrowObj: "\<tau>move1 P h (Throw a\<bullet>M(es))"
  and \<tau>move1CallThrowParams: "\<tau>move1 P h (Val v\<bullet>M(map Val vs @ Throw a # es))"
  and \<tau>move1BlockThrow: "\<tau>move1 P h {V:T=None; Throw a}"
  and \<tau>move1SyncThrow: "\<tau>move1 P h (sync\<^bsub>V'\<^esub> (Throw a) e)"
  and \<tau>move1SeqThrow: "\<tau>move1 P h (Throw a;;e)"
  and \<tau>move1CondThrow: "\<tau>move1 P h (if (Throw a) e1 else e2)"
  and \<tau>move1ThrowThrow: "\<tau>move1 P h (throw (Throw a))"

  and \<tau>moves1Hd: "\<tau>move1 P h e \<Longrightarrow> \<tau>moves1 P h (e # es)"
  and \<tau>moves1Tl: "\<tau>moves1 P h es \<Longrightarrow> \<tau>moves1 P h (Val v # es)"
by fastforce+

lemma \<tau>moves1_map_Val [dest!]:
  "\<tau>moves1 P h (map Val es) \<Longrightarrow> False"
by(induct es)(auto)

lemma \<tau>moves1_map_Val_ThrowD [simp]: "\<tau>moves1 P h (map Val vs @ Throw a # es) = False"
by(induct vs)(fastforce)+

lemma fixes e :: "('a, 'b, 'addr) exp" and es :: "('a, 'b, 'addr) exp list"
  shows \<tau>move1_not_call1:
  "call1 e = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<tau>move1 P h e \<longleftrightarrow> (synthesized_call P h (a, M, vs) \<longrightarrow> \<tau>external' P h a M)"
  and \<tau>moves1_not_calls1:
  "calls1 es = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<tau>moves1 P h es \<longleftrightarrow> (synthesized_call P h (a, M, vs) \<longrightarrow> \<tau>external' P h a M)"
apply(induct e and es rule: call1.induct calls1.induct)
apply(auto split: if_split_asm simp add: is_vals_conv)
apply(fastforce simp add: synthesized_call_def map_eq_append_conv \<tau>external'_def \<tau>external_def dest: sees_method_fun)+
done

lemma red1_\<tau>_taD: "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<tau>move1 P (hp s) e \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
  and reds1_\<tau>_taD: "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<tau>moves1 P (hp s) es \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
apply(induct rule: red1_reds1.inducts)
apply(fastforce simp add: map_eq_append_conv \<tau>external'_def \<tau>external_def dest: \<tau>external'_red_external_TA_empty)+
done

lemma \<tau>move1_heap_unchanged: "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<tau>move1 P (hp s) e \<rbrakk> \<Longrightarrow> hp s' = hp s"
  and \<tau>moves1_heap_unchanged: "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<tau>moves1 P (hp s) es \<rbrakk> \<Longrightarrow> hp s' = hp s"
apply(induct rule: red1_reds1.inducts)
apply(auto)
apply(fastforce simp add: map_eq_append_conv \<tau>external'_def \<tau>external_def dest: \<tau>external'_red_external_heap_unchanged)+
done

lemma \<tau>Move1_iff:
  "\<tau>Move1 P h exexs \<longleftrightarrow> (let ((e, _), _) = exexs in \<tau>move1 P h e \<or> final e)"
by(cases exexs)(auto)


lemma \<tau>red1_iff [iff]:
  "\<tau>red1g uf P t h (e, xs) (e', xs') = (uf,P,t \<turnstile>1 \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle> \<and> \<tau>move1 P h e)"
by(simp add: \<tau>red1g_def)

lemma \<tau>reds1_iff [iff]:
  "\<tau>reds1g uf P t h (es, xs) (es', xs') = (uf,P,t \<turnstile>1 \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle> \<and> \<tau>moves1 P h es)"
by(simp add: \<tau>reds1g_def)

lemma \<tau>red1t_1step:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move1 P h e \<rbrakk>
  \<Longrightarrow> \<tau>red1gt uf P t h (e, xs) (e', xs')"
by(blast intro: tranclp.r_into_trancl)

lemma \<tau>red1t_2step:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move1 P h e; 
     uf,P,t \<turnstile>1 \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move1 P h e' \<rbrakk>
  \<Longrightarrow> \<tau>red1gt uf P t h (e, xs) (e'', xs'')"
by(blast intro: tranclp.trancl_into_trancl[OF \<tau>red1t_1step])

lemma \<tau>red1t_3step:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move1 P h e; 
     uf,P,t \<turnstile>1 \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move1 P h e';
     uf,P,t \<turnstile>1 \<langle>e'', (h, xs'')\<rangle> -\<epsilon>\<rightarrow> \<langle>e''', (h, xs''')\<rangle>; \<tau>move1 P h e'' \<rbrakk>
  \<Longrightarrow> \<tau>red1gt uf P t h (e, xs) (e''', xs''')"
by(blast intro: tranclp.trancl_into_trancl[OF \<tau>red1t_2step])

lemma \<tau>reds1t_1step:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves1 P h es \<rbrakk>
  \<Longrightarrow> \<tau>reds1gt uf P t h (es, xs) (es', xs')"
by(blast intro: tranclp.r_into_trancl)

lemma \<tau>reds1t_2step:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves1 P h es; 
     uf,P,t \<turnstile>1 \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves1 P h es' \<rbrakk>
  \<Longrightarrow> \<tau>reds1gt uf P t h (es, xs) (es'', xs'')"
by(blast intro: tranclp.trancl_into_trancl[OF \<tau>reds1t_1step])

lemma \<tau>reds1t_3step:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves1 P h es; 
     uf,P,t \<turnstile>1 \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves1 P h es';
     uf,P,t \<turnstile>1 \<langle>es'', (h, xs'')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es''', (h, xs''')\<rangle>; \<tau>moves1 P h es'' \<rbrakk>
  \<Longrightarrow> \<tau>reds1gt uf P t h (es, xs) (es''', xs''')"
by(blast intro: tranclp.trancl_into_trancl[OF \<tau>reds1t_2step])

lemma \<tau>red1r_1step:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move1 P h e \<rbrakk>
  \<Longrightarrow> \<tau>red1gr uf P t h (e, xs) (e', xs')"
by(blast intro: r_into_rtranclp)

lemma \<tau>red1r_2step:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move1 P h e; 
     uf,P,t \<turnstile>1 \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move1 P h e' \<rbrakk>
  \<Longrightarrow> \<tau>red1gr uf P t h (e, xs) (e'', xs'')"
by(blast intro: rtranclp.rtrancl_into_rtrancl[OF \<tau>red1r_1step])

lemma \<tau>red1r_3step:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move1 P h e; 
     uf,P,t \<turnstile>1 \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move1 P h e';
     uf,P,t \<turnstile>1 \<langle>e'', (h, xs'')\<rangle> -\<epsilon>\<rightarrow> \<langle>e''', (h, xs''')\<rangle>; \<tau>move1 P h e'' \<rbrakk>
  \<Longrightarrow> \<tau>red1gr uf P t h (e, xs) (e''', xs''')"
by(blast intro: rtranclp.rtrancl_into_rtrancl[OF \<tau>red1r_2step])

lemma \<tau>reds1r_1step:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves1 P h es \<rbrakk>
  \<Longrightarrow> \<tau>reds1gr uf P t h (es, xs) (es', xs')"
by(blast intro: r_into_rtranclp)

lemma \<tau>reds1r_2step:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves1 P h es; 
     uf,P,t \<turnstile>1 \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves1 P h es' \<rbrakk>
  \<Longrightarrow> \<tau>reds1gr uf P t h (es, xs) (es'', xs'')"
by(blast intro: rtranclp.rtrancl_into_rtrancl[OF \<tau>reds1r_1step])

lemma \<tau>reds1r_3step:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves1 P h es; 
     uf,P,t \<turnstile>1 \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves1 P h es';
     uf,P,t \<turnstile>1 \<langle>es'', (h, xs'')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es''', (h, xs''')\<rangle>; \<tau>moves1 P h es'' \<rbrakk>
  \<Longrightarrow> \<tau>reds1gr uf P t h (es, xs) (es''', xs''')"
by(blast intro: rtranclp.rtrancl_into_rtrancl[OF \<tau>reds1r_2step])

lemma \<tau>red1t_preserves_len: "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> length xs' = length xs"
by(induct rule: tranclp_induct2)(auto dest: red1_preserves_len)

lemma \<tau>red1r_preserves_len: "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> length xs' = length xs"
by(induct rule: rtranclp_induct2)(auto dest: red1_preserves_len)

lemma \<tau>red1t_inj_\<tau>reds1t: "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>reds1gt uf P t h (e # es, xs) (e' # es, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl List1Red1 \<tau>moves1Hd)

lemma \<tau>reds1t_cons_\<tau>reds1t: "\<tau>reds1gt uf P t h (es, xs) (es', xs') \<Longrightarrow> \<tau>reds1gt uf P t h (Val v # es, xs) (Val v # es', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl List1Red2 \<tau>moves1Tl)

lemma \<tau>red1r_inj_\<tau>reds1r: "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>reds1gr uf P t h (e # es, xs) (e' # es, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl List1Red1 \<tau>moves1Hd)

lemma \<tau>reds1r_cons_\<tau>reds1r: "\<tau>reds1gr uf P t h (es, xs) (es', xs') \<Longrightarrow> \<tau>reds1gr uf P t h (Val v # es, xs) (Val v # es', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl List1Red2 \<tau>moves1Tl)

lemma NewArray_\<tau>red1t_xt:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (newA T\<lfloor>e\<rceil>, xs) (newA T\<lfloor>e'\<rceil>, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl New1ArrayRed \<tau>move1NewArray)

lemma Cast_\<tau>red1t_xt:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (Cast T e, xs) (Cast T e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl Cast1Red \<tau>move1Cast)

lemma InstanceOf_\<tau>red1t_xt:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (e instanceof T, xs) (e' instanceof T, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl InstanceOf1Red \<tau>move1InstanceOf)

lemma BinOp_\<tau>red1t_xt1:
  "\<tau>red1gt uf P t h (e1, xs) (e1', xs') \<Longrightarrow> \<tau>red1gt uf P t h (e1 \<guillemotleft>bop\<guillemotright> e2, xs) (e1' \<guillemotleft>bop\<guillemotright> e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl Bin1OpRed1 \<tau>move1BinOp1)

lemma BinOp_\<tau>red1t_xt2:
  "\<tau>red1gt uf P t h (e2, xs) (e2', xs') \<Longrightarrow> \<tau>red1gt uf P t h (Val v \<guillemotleft>bop\<guillemotright> e2, xs) (Val v \<guillemotleft>bop\<guillemotright> e2', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl Bin1OpRed2 \<tau>move1BinOp2)

lemma LAss_\<tau>red1t:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (V := e, xs) (V := e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl LAss1Red \<tau>move1LAss)

lemma AAcc_\<tau>red1t_xt1:
  "\<tau>red1gt uf P t h (a, xs) (a', xs') \<Longrightarrow> \<tau>red1gt uf P t h (a\<lfloor>i\<rceil>, xs) (a'\<lfloor>i\<rceil>, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAcc1Red1 \<tau>move1AAcc1)

lemma AAcc_\<tau>red1t_xt2:
  "\<tau>red1gt uf P t h (i, xs) (i', xs') \<Longrightarrow> \<tau>red1gt uf P t h (Val a\<lfloor>i\<rceil>, xs) (Val a\<lfloor>i'\<rceil>, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAcc1Red2 \<tau>move1AAcc2)

lemma AAss_\<tau>red1t_xt1:
  "\<tau>red1gt uf P t h (a, xs) (a', xs') \<Longrightarrow> \<tau>red1gt uf P t h (a\<lfloor>i\<rceil> := e, xs) (a'\<lfloor>i\<rceil> := e, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAss1Red1 \<tau>move1AAss1)

lemma AAss_\<tau>red1t_xt2:
  "\<tau>red1gt uf P t h (i, xs) (i', xs') \<Longrightarrow> \<tau>red1gt uf P t h (Val a\<lfloor>i\<rceil> := e, xs) (Val a\<lfloor>i'\<rceil> := e, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAss1Red2 \<tau>move1AAss2)

lemma AAss_\<tau>red1t_xt3:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (Val a\<lfloor>Val i\<rceil> := e, xs) (Val a\<lfloor>Val i\<rceil> := e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAss1Red3 \<tau>move1AAss3)

lemma ALength_\<tau>red1t_xt:
  "\<tau>red1gt uf P t h (a, xs) (a', xs') \<Longrightarrow> \<tau>red1gt uf P t h (a\<bullet>length, xs) (a'\<bullet>length, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl ALength1Red \<tau>move1ALength)

lemma FAcc_\<tau>red1t_xt:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (e\<bullet>F{D}, xs) (e'\<bullet>F{D}, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl FAcc1Red \<tau>move1FAcc)

lemma FAss_\<tau>red1t_xt1:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (e\<bullet>F{D} := e2, xs) (e'\<bullet>F{D} := e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl FAss1Red1 \<tau>move1FAss1)

lemma FAss_\<tau>red1t_xt2:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (Val v\<bullet>F{D} := e, xs) (Val v\<bullet>F{D} := e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl FAss1Red2 \<tau>move1FAss2)

lemma CAS_\<tau>red1t_xt1:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (e\<bullet>compareAndSwap(D\<bullet>F, e2, e3), xs) (e'\<bullet>compareAndSwap(D\<bullet>F, e2, e3), xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl CAS1Red1)

lemma CAS_\<tau>red1t_xt2:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (Val v\<bullet>compareAndSwap(D\<bullet>F, e, e3), xs) (Val v\<bullet>compareAndSwap(D\<bullet>F, e', e3), xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl CAS1Red2)

lemma CAS_\<tau>red1t_xt3:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e), xs) (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e'), xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl CAS1Red3)

lemma Call_\<tau>red1t_obj:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (e\<bullet>M(ps), xs) (e'\<bullet>M(ps), xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl Call1Obj \<tau>move1CallObj)

lemma Call_\<tau>red1t_param:
  "\<tau>reds1gt uf P t h (es, xs) (es', xs') \<Longrightarrow> \<tau>red1gt uf P t h (Val v\<bullet>M(es), xs) (Val v\<bullet>M(es'), xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl Call1Params \<tau>move1CallParams)

lemma Block_None_\<tau>red1t_xt:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h ({V:T=None; e}, xs) ({V:T=None; e'}, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl \<tau>move1Block elim!: Block1Red)

lemma Block_\<tau>red1t_Some:
  "\<lbrakk> \<tau>red1gt uf P t h (e, xs[V := v]) (e', xs'); V < length xs \<rbrakk> 
  \<Longrightarrow> \<tau>red1gt uf P t h ({V:Ty=\<lfloor>v\<rfloor>; e}, xs) ({V:Ty=None; e'}, xs')"
by(blast intro: tranclp_into_tranclp2 Block1Some \<tau>move1BlockSome Block_None_\<tau>red1t_xt)

lemma Sync_\<tau>red1t_xt:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (sync\<^bsub>V\<^esub> (e) e2, xs) (sync\<^bsub>V\<^esub> (e') e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl Synchronized1Red1 \<tau>move1Sync)

lemma InSync_\<tau>red1t_xt:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (insync\<^bsub>V\<^esub> (a) e, xs) (insync\<^bsub>V\<^esub> (a) e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl Synchronized1Red2 \<tau>move1InSync)

lemma Seq_\<tau>red1t_xt:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (e;;e2, xs) (e';;e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl Seq1Red \<tau>move1Seq)

lemma Cond_\<tau>red1t_xt:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (if (e) e1 else e2, xs) (if (e') e1 else e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl Cond1Red \<tau>move1Cond)

lemma Throw_\<tau>red1t_xt:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (throw e, xs) (throw e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl Throw1Red \<tau>move1Throw)

lemma Try_\<tau>red1t_xt:
  "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gt uf P t h (try e catch(C V) e2, xs) (try e' catch(C V) e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl Try1Red \<tau>move1Try)


lemma NewArray_\<tau>red1r_xt:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (newA T\<lfloor>e\<rceil>, xs) (newA T\<lfloor>e'\<rceil>, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl New1ArrayRed \<tau>move1NewArray)

lemma Cast_\<tau>red1r_xt:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (Cast T e, xs) (Cast T e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl Cast1Red \<tau>move1Cast)

lemma InstanceOf_\<tau>red1r_xt:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (e instanceof T, xs) (e' instanceof T, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl InstanceOf1Red \<tau>move1InstanceOf)

lemma BinOp_\<tau>red1r_xt1:
  "\<tau>red1gr uf P t h (e1, xs) (e1', xs') \<Longrightarrow> \<tau>red1gr uf P t h (e1 \<guillemotleft>bop\<guillemotright> e2, xs) (e1' \<guillemotleft>bop\<guillemotright> e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl Bin1OpRed1 \<tau>move1BinOp1)

lemma BinOp_\<tau>red1r_xt2:
  "\<tau>red1gr uf P t h (e2, xs) (e2', xs') \<Longrightarrow> \<tau>red1gr uf P t h (Val v \<guillemotleft>bop\<guillemotright> e2, xs) (Val v \<guillemotleft>bop\<guillemotright> e2', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl Bin1OpRed2 \<tau>move1BinOp2)

lemma LAss_\<tau>red1r:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (V := e, xs) (V := e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl LAss1Red \<tau>move1LAss)

lemma AAcc_\<tau>red1r_xt1:
  "\<tau>red1gr uf P t h (a, xs) (a', xs') \<Longrightarrow> \<tau>red1gr uf P t h (a\<lfloor>i\<rceil>, xs) (a'\<lfloor>i\<rceil>, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAcc1Red1 \<tau>move1AAcc1)

lemma AAcc_\<tau>red1r_xt2:
  "\<tau>red1gr uf P t h (i, xs) (i', xs') \<Longrightarrow> \<tau>red1gr uf P t h (Val a\<lfloor>i\<rceil>, xs) (Val a\<lfloor>i'\<rceil>, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAcc1Red2 \<tau>move1AAcc2)

lemma AAss_\<tau>red1r_xt1:
  "\<tau>red1gr uf P t h (a, xs) (a', xs') \<Longrightarrow> \<tau>red1gr uf P t h (a\<lfloor>i\<rceil> := e, xs) (a'\<lfloor>i\<rceil> := e, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAss1Red1 \<tau>move1AAss1)

lemma AAss_\<tau>red1r_xt2:
  "\<tau>red1gr uf P t h (i, xs) (i', xs') \<Longrightarrow> \<tau>red1gr uf P t h (Val a\<lfloor>i\<rceil> := e, xs) (Val a\<lfloor>i'\<rceil> := e, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAss1Red2 \<tau>move1AAss2)

lemma AAss_\<tau>red1r_xt3:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (Val a\<lfloor>Val i\<rceil> := e, xs) (Val a\<lfloor>Val i\<rceil> := e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAss1Red3 \<tau>move1AAss3)

lemma ALength_\<tau>red1r_xt:
  "\<tau>red1gr uf P t h (a, xs) (a', xs') \<Longrightarrow> \<tau>red1gr uf P t h (a\<bullet>length, xs) (a'\<bullet>length, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl ALength1Red \<tau>move1ALength)

lemma FAcc_\<tau>red1r_xt:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (e\<bullet>F{D}, xs) (e'\<bullet>F{D}, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl FAcc1Red \<tau>move1FAcc)

lemma FAss_\<tau>red1r_xt1:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (e\<bullet>F{D} := e2, xs) (e'\<bullet>F{D} := e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl FAss1Red1 \<tau>move1FAss1)

lemma FAss_\<tau>red1r_xt2:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (Val v\<bullet>F{D} := e, xs) (Val v\<bullet>F{D} := e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl FAss1Red2 \<tau>move1FAss2)

lemma CAS_\<tau>red1r_xt1:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (e\<bullet>compareAndSwap(D\<bullet>F, e2, e3), xs) (e'\<bullet>compareAndSwap(D\<bullet>F, e2, e3), xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl CAS1Red1)

lemma CAS_\<tau>red1r_xt2:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (Val v\<bullet>compareAndSwap(D\<bullet>F, e, e3), xs) (Val v\<bullet>compareAndSwap(D\<bullet>F, e', e3), xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl CAS1Red2)

lemma CAS_\<tau>red1r_xt3:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e), xs) (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e'), xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl CAS1Red3)

lemma Call_\<tau>red1r_obj:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (e\<bullet>M(ps), xs) (e'\<bullet>M(ps), xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl Call1Obj \<tau>move1CallObj)

lemma Call_\<tau>red1r_param:
  "\<tau>reds1gr uf P t h (es, xs) (es', xs') \<Longrightarrow> \<tau>red1gr uf P t h (Val v\<bullet>M(es), xs) (Val v\<bullet>M(es'), xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl Call1Params \<tau>move1CallParams)

lemma Block_None_\<tau>red1r_xt:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h ({V:T=None; e}, xs) ({V:T=None; e'}, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl \<tau>move1Block elim!: Block1Red)

lemma Block_\<tau>red1r_Some:
  "\<lbrakk> \<tau>red1gr uf P t h (e, xs[V := v]) (e', xs'); V < length xs \<rbrakk> 
  \<Longrightarrow> \<tau>red1gr uf P t h ({V:Ty=\<lfloor>v\<rfloor>; e}, xs) ({V:Ty=None; e'}, xs')"
by(blast intro: converse_rtranclp_into_rtranclp Block1Some \<tau>move1BlockSome Block_None_\<tau>red1r_xt)

lemma Sync_\<tau>red1r_xt:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (sync\<^bsub>V\<^esub> (e) e2, xs) (sync\<^bsub>V\<^esub> (e') e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl Synchronized1Red1 \<tau>move1Sync)

lemma InSync_\<tau>red1r_xt:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (insync\<^bsub>V\<^esub> (a) e, xs) (insync\<^bsub>V\<^esub> (a) e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl Synchronized1Red2 \<tau>move1InSync)

lemma Seq_\<tau>red1r_xt:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (e;;e2, xs) (e';;e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl Seq1Red \<tau>move1Seq)

lemma Cond_\<tau>red1r_xt:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (if (e) e1 else e2, xs) (if (e') e1 else e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl Cond1Red \<tau>move1Cond)

lemma Throw_\<tau>red1r_xt:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (throw e, xs) (throw e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl Throw1Red \<tau>move1Throw)

lemma Try_\<tau>red1r_xt:
  "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red1gr uf P t h (try e catch(C V) e2, xs) (try e' catch(C V) e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl Try1Red \<tau>move1Try)

lemma \<tau>red1t_ThrowD [dest]: "\<tau>red1gt uf P t h (Throw a, xs) (e'', xs'') \<Longrightarrow> e'' = Throw a \<and> xs'' = xs"
by(induct rule: tranclp_induct2)(auto)

lemma \<tau>red1r_ThrowD [dest]: "\<tau>red1gr uf P t h (Throw a, xs) (e'', xs'') \<Longrightarrow> e'' = Throw a \<and> xs'' = xs"
by(induct rule: rtranclp_induct2)(auto)

lemma \<tau>Red1_conv [iff]:
  "\<tau>Red1g uf P t h (ex, exs) (ex', exs') = (uf,P,t \<turnstile>1 \<langle>ex/exs, h\<rangle> -\<epsilon>\<rightarrow> \<langle>ex'/exs', h\<rangle> \<and> \<tau>Move1 P h (ex, exs))"
by(simp add: \<tau>Red1g_def)


lemma \<tau>red1t_into_\<tau>Red1t:
  "\<tau>red1gt uf P t h (e, xs) (e'', xs'') \<Longrightarrow> \<tau>Red1gt uf P t h ((e, xs), exs) ((e'', xs''), exs)"
by(induct rule: tranclp_induct2)(fastforce dest: red1Red intro: \<tau>move1Block tranclp.intros)+

lemma \<tau>red1r_into_\<tau>Red1r:
  "\<tau>red1gr uf P t h (e, xs) (e'', xs'') \<Longrightarrow> \<tau>Red1gr uf P t h ((e, xs), exs) ((e'', xs''), exs)"
by(induct rule: rtranclp_induct2)(fastforce dest: red1Red intro: \<tau>move1Block rtranclp.intros)+

lemma red1_max_vars: "uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> max_vars e' \<le> max_vars e"
  and reds1_max_varss: "uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> max_varss es' \<le> max_varss es"
by(induct rule: red1_reds1.inducts) auto

lemma \<tau>red1t_max_vars: "\<tau>red1gt uf P t h (e, xs) (e', xs') \<Longrightarrow> max_vars e' \<le> max_vars e"
by(induct rule: tranclp_induct2)(auto dest: red1_max_vars)

lemma \<tau>red1r_max_vars: "\<tau>red1gr uf P t h (e, xs) (e', xs') \<Longrightarrow> max_vars e' \<le> max_vars e"
by(induct rule: rtranclp_induct2)(auto dest: red1_max_vars)

lemma \<tau>red1r_Val:
  "\<tau>red1gr uf P t h (Val v, xs) s' \<longleftrightarrow> s' = (Val v, xs)"
proof
  assume "\<tau>red1gr uf P t h (Val v, xs) s'"
  thus "s' = (Val v, xs)" by induct(auto)
qed auto

lemma \<tau>red1t_Val:
  "\<tau>red1gt uf P t h (Val v, xs) s' \<longleftrightarrow> False"
proof
  assume "\<tau>red1gt uf P t h (Val v, xs) s'"
  thus False by induct auto
qed auto

lemma \<tau>reds1r_map_Val:
  "\<tau>reds1gr uf P t h (map Val vs, xs) s' \<longleftrightarrow> s' = (map Val vs, xs)"
proof
  assume "\<tau>reds1gr uf P t h (map Val vs, xs) s'"
  thus "s' = (map Val vs, xs)" by induct auto
qed auto

lemma \<tau>reds1t_map_Val:
  "\<tau>reds1gt uf P t h (map Val vs, xs) s' \<longleftrightarrow> False"
proof
  assume "\<tau>reds1gt uf P t h (map Val vs, xs) s'"
  thus "False" by induct auto
qed auto

lemma \<tau>reds1r_map_Val_Throw:
  "\<tau>reds1gr uf P t h (map Val vs @ Throw a # es, xs) s' \<longleftrightarrow> s' = (map Val vs @ Throw a # es, xs)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs by induct auto
qed auto

lemma \<tau>reds1t_map_Val_Throw:
  "\<tau>reds1gt uf P t h (map Val vs @ Throw a # es, xs) s' \<longleftrightarrow> False"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs by induct auto
qed auto

lemma \<tau>red1r_Throw:
  "\<tau>red1gr uf P t h (Throw a, xs) s' \<longleftrightarrow> s' = (Throw a, xs)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs by induct auto
qed simp

lemma \<tau>red1t_Throw:
  "\<tau>red1gt uf P t h (Throw a, xs) s' \<longleftrightarrow> False" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs by induct auto
qed simp

lemma red1_False_into_red1_True:
  "False,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> True,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  and reds1_False_into_reds1_True:
  "False,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> True,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>"
by(induct rule: red1_reds1.inducts)(auto intro: red1_reds1.intros)

lemma Red1_False_into_Red1_True:
  assumes "False,P,t \<turnstile>1 \<langle>ex/exs,shr s\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>"
  shows "True,P,t \<turnstile>1 \<langle>ex/exs,shr s\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>"
using assms
by(cases)(auto dest: Red1.intros red1_False_into_red1_True)

lemma red1_Suspend_is_call:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> call1 e' \<noteq> None"
  and reds_Suspend_is_calls:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> calls1 es' \<noteq> None"
by(induct rule: red1_reds1.inducts)(auto dest: red_external_Suspend_StaySame)

lemma Red1_Suspend_is_call:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>(e, xs)/exs, h\<rangle> -ta\<rightarrow> \<langle>(e', xs')/exs', h'\<rangle>; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> call1 e' \<noteq> None"
by(auto elim!: Red1.cases dest: red1_Suspend_is_call)

lemma Red1_mthr: "multithreaded final_expr1 (mred1g uf P)"
by(unfold_locales)(fastforce elim!: Red1.cases dest: red1_new_thread_heap)+

lemma red1_\<tau>move1_heap_unchanged: "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<tau>move1 P (hp s) e \<rbrakk> \<Longrightarrow> hp s' = hp s"
  and red1_\<tau>moves1_heap_unchanged: "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<tau>moves1 P (hp s) es \<rbrakk> \<Longrightarrow> hp s' = hp s"
apply(induct rule: red1_reds1.inducts)
apply(fastforce simp add: map_eq_append_conv \<tau>external'_def \<tau>external_def dest: \<tau>external'_red_external_heap_unchanged)+
done

lemma Red1_\<tau>mthr_wf: "\<tau>multithreaded_wf final_expr1 (mred1g uf P) (\<tau>MOVE1 P)"
proof -
  interpret multithreaded final_expr1 "mred1g uf P" convert_RA
    by(rule Red1_mthr)
  show ?thesis
  proof
    fix x1 m1 t ta1 x1' m1'
    assume "mred1g uf P t (x1, m1) ta1 (x1', m1')" "\<tau>MOVE1 P (x1, m1) ta1 (x1', m1')"
    thus "m1 = m1'" by(cases x1)(fastforce elim!: Red1.cases dest: red1_\<tau>move1_heap_unchanged)
  next
    fix s ta s'
    assume "\<tau>MOVE1 P s ta s'"
    thus "ta = \<epsilon>" by(simp add: split_beta)
  qed
qed

end

sublocale J1_heap_base < Red1_mthr: 
  \<tau>multithreaded_wf 
    final_expr1
    "mred1g uf P"
    convert_RA
    "\<tau>MOVE1 P"
  for uf P
by(rule Red1_\<tau>mthr_wf)

context J1_heap_base begin

lemma \<tau>Red1't_into_Red1'_\<tau>mthr_silent_movet:
  "\<tau>Red1gt uf P t h (ex2, exs2) (ex2'', exs2'')
  \<Longrightarrow> Red1_mthr.silent_movet uf P t ((ex2, exs2), h) ((ex2'', exs2''), h)"
apply(induct rule: tranclp_induct2)
 apply clarsimp
 apply(rule tranclp.r_into_trancl)
 apply(simp add: Red1_mthr.silent_move_iff)
apply(erule tranclp.trancl_into_trancl)
apply(simp add: Red1_mthr.silent_move_iff)
done

lemma \<tau>Red1t_into_Red1'_\<tau>mthr_silent_moves:
  "\<tau>Red1gt uf P t h (ex2, exs2) (ex2'', exs2'')
  \<Longrightarrow> Red1_mthr.silent_moves uf P t ((ex2, exs2), h) ((ex2'', exs2''), h)"
by(rule tranclp_into_rtranclp)(rule \<tau>Red1't_into_Red1'_\<tau>mthr_silent_movet)

lemma \<tau>Red1'r_into_Red1'_\<tau>mthr_silent_moves:
  "\<tau>Red1gr uf P t h (ex, exs) (ex', exs') \<Longrightarrow> Red1_mthr.silent_moves uf P t ((ex, exs), h) ((ex', exs'), h)"
apply(induct rule: rtranclp_induct2)
 apply blast
apply(erule rtranclp.rtrancl_into_rtrancl)
apply(simp add: Red1_mthr.silent_move_iff)
done

lemma \<tau>Red1r_rtranclpD:
  "\<tau>Red1gr uf P t h s s' \<Longrightarrow> \<tau>trsys.silent_moves (mred1g uf P t) (\<tau>MOVE1 P) (s, h) (s', h)"
apply(induct rule: rtranclp_induct)
apply(auto elim!: rtranclp.rtrancl_into_rtrancl intro: \<tau>trsys.silent_move.intros)
done

lemma \<tau>Red1t_tranclpD:
  "\<tau>Red1gt uf P t h s s' \<Longrightarrow> \<tau>trsys.silent_movet (mred1g uf P t) (\<tau>MOVE1 P) (s, h) (s', h)"
apply(induct rule: tranclp_induct)
apply(rule tranclp.r_into_trancl)
apply(auto elim!: tranclp.trancl_into_trancl intro!: \<tau>trsys.silent_move.intros simp: \<tau>Red1g_def split_def)
done

lemma \<tau>mreds1_Val_Nil: "\<tau>trsys.silent_moves (mred1g uf P t) (\<tau>MOVE1 P) (((Val v, xs), []), h) s \<longleftrightarrow> s = (((Val v, xs), []), h)"
proof
  assume "\<tau>trsys.silent_moves (mred1g uf P t) (\<tau>MOVE1 P) (((Val v, xs), []), h) s"
  thus "s = (((Val v, xs), []), h)"
    by induct(auto elim!: Red1_mthr.silent_move.cases Red1.cases)
qed auto

lemma \<tau>mreds1_Throw_Nil:
  "\<tau>trsys.silent_moves (mred1g uf P t) (\<tau>MOVE1 P) (((Throw a, xs), []), h) s \<longleftrightarrow> s = (((Throw a, xs), []), h)"
proof
  assume "\<tau>trsys.silent_moves (mred1g uf P t) (\<tau>MOVE1 P) (((Throw a, xs), []), h) s"
  thus "s = (((Throw a, xs), []), h)"
    by induct(auto elim!: Red1_mthr.silent_move.cases Red1.cases)
qed auto

end

end
