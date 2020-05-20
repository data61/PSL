(*  Title:       Jive Data and Store Model
    Author:      Norbert Schirmer <schirmer at informatik.tu-muenchen.de>, 2003
    Maintainer:  Nicole Rauch <rauch at informatik.uni-kl.de>
    License:     LGPL
*)

section \<open>Store Properties\<close>

theory StoreProperties
imports Store
begin

text \<open>This theory formalizes advanced concepts and properties of stores.\<close>

subsection \<open>Reachability of a Location from a Reference\<close>

text \<open>For a given store, the function \<open>reachS\<close> yields the set of all pairs 
$(l,v)$ where $l$ is a location that is reachable from the value $v$ (which must be a reference)
in the given store.
The predicate \<open>reach\<close> decides whether a location is reachable from a value in a store.
\<close>

inductive
  reach :: "Store \<Rightarrow> Location \<Rightarrow> Value \<Rightarrow> bool" 
    ("_\<turnstile> _ reachable'_from _" [91,91,91]90)
  for s :: Store
where
  Immediate: "ref l \<noteq> nullV \<Longrightarrow> s\<turnstile> l reachable_from (ref l)"
| Indirect: "\<lbrakk>s\<turnstile> l reachable_from (s@@k); ref k \<noteq> nullV\<rbrakk> 
             \<Longrightarrow> s\<turnstile> l reachable_from (ref k)" 

text \<open>Note that we explicitly exclude \<open>nullV\<close> as legal reference
for reachability. 
Keep in mind that static fields are not associated to any object,
therefore \<open>ref\<close> yields \<open>nullV\<close> if invoked on static fields 
(see the
definition of the function \<open>ref\<close>, Sect. \ref{ref_def}).
Reachability only describes the locations directly 
reachable from the object or array by following the pointers and should not include 
the static fields if we encounter a \<open>nullV\<close> reference in the pointer 
chain.\<close>

text \<open>We formalize some properties of reachability. 
Especially, Lemma 3.2 as given in \cite[p. 53]{Poetzsch-Heffter97specification} is proven.\<close>

lemma unreachable_Null: 
  assumes reach: "s\<turnstile> l reachable_from x" shows "x\<noteq>nullV"
  using reach by (induct) auto

corollary unreachable_Null_simp [simp]:
  "\<not> s\<turnstile> l reachable_from nullV"
  by (iprover dest: unreachable_Null)

corollary unreachable_NullE [elim]:
  "s\<turnstile> l reachable_from nullV \<Longrightarrow> P"
  by (simp)

lemma reachObjLoc [simp,intro]: 
  "C=cls cf \<Longrightarrow> s\<turnstile> objLoc cf a reachable_from objV C a"
  by (iprover intro: reach.Immediate [of "objLoc cf a",simplified])

lemma reachArrLoc [simp,intro]: "s\<turnstile> arrLoc T a i reachable_from arrV T a"
  by (rule reach.Immediate [of "arrLoc T a i",simplified])

lemma reachArrLen [simp,intro]: "s\<turnstile> arrLenLoc T a reachable_from arrV T a"
  by (rule reach.Immediate [of "arrLenLoc T a",simplified])

lemma unreachStatic [simp]: "\<not> s\<turnstile> staticLoc f reachable_from x"
proof -
  {
    fix y assume "s\<turnstile> y reachable_from x" "y=staticLoc f"
    then have False
      by induct auto
  }
  thus ?thesis
    by auto
qed

lemma unreachStaticE [elim]: "s\<turnstile> staticLoc f reachable_from x \<Longrightarrow> P"
  by (simp add: unreachStatic)

lemma reachable_from_ArrLoc_impl_Arr [simp,intro]:
  assumes reach_loc: "s\<turnstile> l reachable_from (s@@arrLoc T a i)"
  shows "s\<turnstile> l reachable_from (arrV T a)"
  using reach.Indirect [OF reach_loc]
  by simp

lemma reachable_from_ObjLoc_impl_Obj [simp,intro]:
  assumes reach_loc: "s\<turnstile> l reachable_from (s@@objLoc cf a)"
  assumes C: "C=cls cf"
  shows "s\<turnstile> l reachable_from (objV C a)"
  using C reach.Indirect [OF reach_loc]
  by simp


text \<open>Lemma 3.2 (i)\<close>
lemma reach_update [simp]:
  assumes unreachable_l_x: "\<not> s\<turnstile> l reachable_from x" 
  shows "s\<langle>l:=y\<rangle>\<turnstile> k reachable_from  x = s\<turnstile> k reachable_from x"
proof
  assume "s\<turnstile> k reachable_from x"
  from this unreachable_l_x
  show "s\<langle>l := y\<rangle>\<turnstile> k reachable_from x"
  proof (induct)
    case (Immediate k)
    have "ref k \<noteq> nullV" by fact
    then show "s\<langle>l := y\<rangle>\<turnstile> k reachable_from (ref k)"
      by (rule reach.Immediate)
  next
    case (Indirect k m)
    have hyp: "\<not> s\<turnstile> l reachable_from (s@@m) 
               \<Longrightarrow> s\<langle>l:=y\<rangle> \<turnstile> k reachable_from (s@@m)" by fact
    have "ref m \<noteq> nullV" and "\<not> s\<turnstile> l reachable_from (ref m)" by fact+
    hence "l\<noteq>m" "\<not> s\<turnstile> l reachable_from (s@@m)"
      by (auto intro: reach.intros)
    with hyp have "s\<langle>l := y\<rangle> \<turnstile> k reachable_from (s\<langle>l := y\<rangle>@@m)"
      by simp
    then show "s\<langle>l := y\<rangle>\<turnstile> k reachable_from (ref m)"
      by (rule reach.Indirect) (rule Indirect.hyps)
  qed
next
  assume "s\<langle>l := y\<rangle>\<turnstile> k reachable_from x"
  from this unreachable_l_x
  show "s\<turnstile> k reachable_from x"
  proof (induct)
    case (Immediate k)
    have "ref k \<noteq> nullV" by fact
    then show "s \<turnstile> k reachable_from (ref k)"
      by (rule reach.Immediate)
  next
    case (Indirect k m)
    with Indirect.hyps 
    have hyp: "\<not> s\<turnstile> l reachable_from (s\<langle>l := y\<rangle>@@m)  
               \<Longrightarrow> s\<turnstile> k reachable_from (s\<langle>l := y\<rangle>@@m)" by simp
    have "ref m \<noteq> nullV" and "\<not> s\<turnstile> l reachable_from (ref m)" by fact+
    hence "l\<noteq>m" "\<not> s \<turnstile> l reachable_from (s@@m)"  
      by (auto intro: reach.intros)
    with hyp have "s \<turnstile> k reachable_from (s@@m)"
      by simp
    thus "s\<turnstile> k reachable_from (ref m)"
      by (rule reach.Indirect) (rule Indirect.hyps)
  qed
qed


text \<open>Lemma 3.2 (ii)\<close>
lemma reach2: 
  "\<not> s\<turnstile> l reachable_from x \<Longrightarrow> \<not> s\<langle>l:=y\<rangle>\<turnstile> l reachable_from x"
  by (simp)

text \<open>Lemma 3.2 (iv)\<close>
lemma reach4: "\<not> s \<turnstile> l reachable_from (ref k) \<Longrightarrow> k \<noteq> l \<or> (ref k) = nullV"
  by (auto intro: reach.intros)

lemma reachable_isRef: 
  assumes reach: "s\<turnstile>l reachable_from x" 
  shows "isRefV x"
  using reach 
proof (induct)
  case (Immediate l)
  show "isRefV (ref l)"
    by (cases l) simp_all
next
  case (Indirect l k)
  show "isRefV (ref k)"
    by (cases k) simp_all
qed


lemma val_ArrLen_IntgT: "isArrLenLoc l \<Longrightarrow> typeof (s@@l) = IntgT"
proof -
  assume isArrLen: "isArrLenLoc l"
  have T: "typeof (s@@l) \<le> ltype l"
    by (simp)
  also from isArrLen have I: "ltype l = IntgT"
    by (cases l) simp_all
  finally show ?thesis
    by (auto elim: rtranclE simp add: le_Javatype_def subtype_defs)
qed

lemma access_alloc' [simp]:
  assumes no_arr_len: "\<not> isArrLenLoc l"
  shows "s\<langle>t\<rangle>@@l = s@@l"
proof -
  from no_arr_len 
  have "isNewArr t \<longrightarrow> l \<noteq> arr_len (new s t)"
    by (cases t) (auto simp add: new_def isArrLenLoc_def split: Location.splits)
  thus ?thesis 
    by (rule access_alloc)
qed
 
text \<open>Lemma 3.2 (v)\<close>
lemma reach_alloc [simp]: "s\<langle>t\<rangle>\<turnstile> l reachable_from x = s\<turnstile> l reachable_from x"
proof 
  assume "s\<langle>t\<rangle>\<turnstile> l reachable_from x"
  thus "s\<turnstile> l reachable_from x"
  proof (induct)
    case (Immediate l)
    thus "s\<turnstile> l reachable_from ref l"
      by (rule reach.intros)
  next
    case (Indirect l k)
    have reach_k: "s\<turnstile> l reachable_from (s\<langle>t\<rangle>@@k)" by fact
    moreover
    have "s\<langle>t\<rangle>@@k = s@@k"
    proof -
      from reach_k have isRef: "isRefV (s\<langle>t\<rangle>@@k)"
        by (rule reachable_isRef)
      have "\<not> isArrLenLoc k"
      proof (rule ccontr,simp)
        assume "isArrLenLoc k"
        then have "typeof (s\<langle>t\<rangle>@@k) = IntgT"
          by (rule val_ArrLen_IntgT)
        with isRef 
        show "False"
          by (cases "(s\<langle>t\<rangle>@@k)") simp_all
      qed
      thus ?thesis
        by (rule access_alloc')
    qed
    ultimately have "s\<turnstile> l reachable_from (s@@k)"
      by simp
    thus "s\<turnstile> l reachable_from ref k"
      by (rule reach.intros) (rule Indirect.hyps)
  qed
next
  assume "s\<turnstile> l reachable_from x"
  thus "s\<langle>t\<rangle>\<turnstile> l reachable_from x"
  proof (induct)
    case (Immediate l)
    thus "s\<langle>t\<rangle>\<turnstile> l reachable_from ref l"
      by (rule reach.intros)
  next
    case (Indirect l k)
    have reach_k: "s\<langle>t\<rangle>\<turnstile> l reachable_from (s@@k)" by fact
    moreover
    have "s\<langle>t\<rangle>@@k = s@@k"
    proof -
      from reach_k have isRef: "isRefV (s@@k)"
        by (rule reachable_isRef)
      have "\<not> isArrLenLoc k"
      proof (rule ccontr,simp)
        assume "isArrLenLoc k"
        then have "typeof (s@@k) = IntgT"
          by (rule val_ArrLen_IntgT)
        with isRef 
        show "False"
          by (cases "(s@@k)") simp_all
      qed
      thus ?thesis
        by (rule access_alloc')
    qed
    ultimately have "s\<langle>t\<rangle>\<turnstile> l reachable_from (s\<langle>t\<rangle>@@k)"
      by simp
    thus "s\<langle>t\<rangle>\<turnstile> l reachable_from ref k"
      by (rule reach.intros) (rule Indirect.hyps)
  qed
qed
       

text \<open>Lemma 3.2 (vi)\<close>
lemma reach6: "isprimitive(typeof x) \<Longrightarrow> \<not> s \<turnstile> l reachable_from x"
proof 
  assume prim: "isprimitive(typeof x)"
  assume "s \<turnstile> l reachable_from x"
  hence "isRefV x"
    by (rule reachable_isRef)
  with prim show False
    by (cases x) simp_all
qed

text \<open>Lemma 3.2 (iii)\<close>
lemma reach3: 
  assumes k_y: "\<not> s\<turnstile> k reachable_from y"
  assumes k_x: "\<not> s\<turnstile> k reachable_from x"
  shows "\<not> s\<langle>l:=y\<rangle>\<turnstile> k reachable_from x"
proof
  assume "s\<langle>l:=y\<rangle>\<turnstile> k reachable_from x"
  from this k_y k_x
  show False
  proof (induct)
    case (Immediate l)
    have "\<not> s\<turnstile> l reachable_from ref l" and "ref l \<noteq> nullV" by fact+
    thus False
      by (iprover intro: reach.intros)
  next
    case (Indirect m k)
    have k_not_Null: "ref k \<noteq> nullV" by fact
    have not_m_y: "\<not> s\<turnstile> m reachable_from y" by fact
    have not_m_k: "\<not> s\<turnstile> m reachable_from ref k" by fact
    have hyp: "\<lbrakk>\<not> s\<turnstile> m reachable_from y; \<not> s\<turnstile> m reachable_from (s\<langle>l := y\<rangle>@@k)\<rbrakk>
               \<Longrightarrow> False" by fact
    have m_upd_k: "s\<langle>l := y\<rangle>\<turnstile> m reachable_from (s\<langle>l := y\<rangle>@@k)" by fact
    show False
    proof (cases "l=k")
      case False
      then have "s\<langle>l := y\<rangle>@@k = s@@k" by simp
      moreover 
      from not_m_k k_not_Null have "\<not> s\<turnstile> m reachable_from (s@@k)"
        by (iprover intro: reach.intros)
      ultimately show False
        using not_m_y hyp by simp
    next
      case True note eq_l_k = this
      show ?thesis
      proof (cases "alive (ref l) s \<and> alive y s \<and> typeof y \<le> ltype l")
        case True
        with eq_l_k have "s\<langle>l := y\<rangle>@@k = y"
          by simp
        with not_m_y hyp show False by simp
      next
        case False
        hence "s\<langle>l := y\<rangle> = s"
          by auto
        moreover 
        from not_m_k k_not_Null have "\<not> s\<turnstile> m reachable_from (s@@k)"
          by (iprover intro: reach.intros)
        ultimately show False
          using not_m_y hyp by simp
      qed
    qed
  qed
qed



text \<open>Lemma 3.2 (vii).\<close>

lemma unreachable_from_init [simp,intro]: "\<not> s\<turnstile> l reachable_from (init T)"
  using reach6 by (cases T) simp_all

lemma ref_reach_unalive: 
  assumes unalive_x:"\<not> alive x s" 
  assumes l_x: "s\<turnstile> l reachable_from x" 
  shows "x = ref l"
using l_x unalive_x
proof induct
  case (Immediate l)
  show "ref l = ref l"
    by simp
next
  case (Indirect l k)
  have "ref k \<noteq> nullV" by fact
  have "\<not> alive (ref k) s" by fact
  hence "s@@k = init (ltype k)" by simp
  moreover have "s\<turnstile> l reachable_from (s@@k)" by fact
  ultimately have False by simp
  thus ?case ..
qed

lemma loc_new_reach: 
  assumes l: "ref l = new s t"
  assumes l_x: "s\<turnstile> l reachable_from x"
  shows "x = new s t"
using l_x l
proof induct
  case (Immediate l)
  show "ref l = new s t" by fact
next
  case (Indirect l k)
  hence "s@@k = new s t" by iprover
  moreover 
  have "\<not> alive (new s t) s"
    by simp
  moreover 
  have "alive (s@@k) s"
    by simp
  ultimately have False by simp
  thus ?case ..
qed
 

text \<open>Lemma 3.2 (viii)\<close>
lemma alive_reach_alive: 
  assumes alive_x: "alive x s" 
  assumes reach_l: "s \<turnstile> l reachable_from x" 
  shows "alive (ref l) s"
using reach_l alive_x
proof (induct)
  case (Immediate l)
  show ?case by fact
next
  case (Indirect l k)
  have hyp: "alive (s@@k) s \<Longrightarrow> alive (ref l) s" by fact
  moreover have "alive (s@@k) s" by simp
  ultimately
  show "alive (ref l) s"
    by iprover
qed
 
text \<open>Lemma 3.2 (ix)\<close>
lemma reach9: 
  assumes reach_impl_access_eq: "\<forall>l. s1\<turnstile>l reachable_from x \<longrightarrow> (s1@@l = s2@@l)"
  shows "s1\<turnstile> l reachable_from x = s2\<turnstile> l reachable_from x"
proof 
  assume "s1\<turnstile> l reachable_from x"
  from this reach_impl_access_eq 
  show "s2\<turnstile> l reachable_from x"
  proof (induct)
    case (Immediate l)
    show "s2\<turnstile> l reachable_from ref l"
      by (rule reach.intros) (rule Immediate.hyps)
  next
    case (Indirect l k)
    have hyp: "\<forall>l. s1\<turnstile> l reachable_from (s1@@k) \<longrightarrow> s1@@l = s2@@l 
               \<Longrightarrow> s2\<turnstile> l reachable_from (s1@@k)" by fact
    have k_not_Null: "ref k \<noteq> nullV" by fact
    have reach_impl_access_eq: 
      "\<forall>l. s1\<turnstile> l reachable_from ref k \<longrightarrow> s1@@l = s2@@l" by fact
    have "s1\<turnstile> l reachable_from (s1@@k)" by fact
    with k_not_Null
    have "s1@@k = s2@@k"
      by (iprover intro: reach_impl_access_eq [rule_format] reach.intros)
    moreover from reach_impl_access_eq k_not_Null
    have "\<forall>l. s1\<turnstile> l reachable_from (s1@@k) \<longrightarrow> s1@@l = s2@@l"
      by (iprover intro: reach.intros)
    then have "s2\<turnstile> l reachable_from (s1@@k)"
      by (rule hyp)
    ultimately have "s2\<turnstile> l reachable_from (s2@@k)"
      by simp
    thus "s2\<turnstile> l reachable_from ref k"
      by (rule reach.intros) (rule Indirect.hyps)
  qed
next
  assume "s2\<turnstile> l reachable_from x"
  from this reach_impl_access_eq 
  show "s1\<turnstile> l reachable_from x"
  proof (induct)
    case (Immediate l)
    show "s1\<turnstile> l reachable_from ref l"
      by (rule reach.intros) (rule Immediate.hyps)
  next
    case (Indirect l k)
    have hyp: "\<forall>l. s1\<turnstile> l reachable_from (s2@@k) \<longrightarrow> s1@@l = s2@@l 
               \<Longrightarrow> s1\<turnstile> l reachable_from (s2@@k)" by fact
    have k_not_Null: "ref k \<noteq> nullV" by fact
    have reach_impl_access_eq: 
      "\<forall>l. s1\<turnstile> l reachable_from ref k \<longrightarrow> s1@@l = s2@@l" by fact
    have "s1\<turnstile> k reachable_from ref k"
      by (rule reach.intros) (rule Indirect.hyps)
    with reach_impl_access_eq
    have eq_k: "s1@@k = s2@@k"
      by simp
    from reach_impl_access_eq k_not_Null
    have "\<forall>l. s1\<turnstile> l reachable_from (s1@@k) \<longrightarrow> s1@@l = s2@@l"
      by (iprover intro: reach.intros)
    then 
    have "\<forall>l. s1\<turnstile> l reachable_from (s2@@k) \<longrightarrow> s1@@l = s2@@l"
      by (simp add: eq_k)
    with eq_k hyp have "s1\<turnstile> l reachable_from (s1@@k)"
      by simp
    thus "s1\<turnstile> l reachable_from ref k"
      by (rule reach.intros) (rule Indirect.hyps)
   qed
qed


subsection \<open>Reachability of a Reference from a Reference\<close>

text \<open>The predicate \<open>rreach\<close> tests whether a value is reachable from
another value. This is an extension of the predicate \<open>oreach\<close> as described
in \cite[p. 54]{Poetzsch-Heffter97specification} because now arrays are handled as well.
\<close>

definition rreach:: "Store \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> bool" 
  ("_\<turnstile>Ref _ reachable'_from _" [91,91,91]90) where
"s\<turnstile>Ref y reachable_from x = (\<exists> l. s\<turnstile> l reachable_from x \<and> y = ref l)"


subsection \<open>Disjointness of Reachable Locations\<close>

text \<open>The predicate \<open>disj\<close> tests whether two values are disjoint
in a given store. Its properties as given in 
\cite[Lemma 3.3, p. 54]{Poetzsch-Heffter97specification} are then proven.
\<close>

definition disj:: "Value \<Rightarrow> Value \<Rightarrow> Store \<Rightarrow> bool" where
"disj x y s = (\<forall> l. \<not> s\<turnstile> l reachable_from x \<or> \<not> s\<turnstile> l reachable_from y)"


lemma disjI1: "\<lbrakk>\<And> l. s\<turnstile> l reachable_from x \<Longrightarrow> \<not> s\<turnstile> l reachable_from y\<rbrakk> 
 \<Longrightarrow> disj x y s"
  by (simp add: disj_def)

lemma disjI2: "\<lbrakk>\<And> l. s\<turnstile> l reachable_from y \<Longrightarrow> \<not> s\<turnstile> l reachable_from x\<rbrakk> 
 \<Longrightarrow> disj x y s"
  by (auto simp add: disj_def)

lemma disj_cases [consumes 1]: 
  assumes "disj x y s"
  assumes "\<And> l.  \<not> s\<turnstile> l reachable_from x \<Longrightarrow> P"
  assumes "\<And> l.  \<not> s\<turnstile> l reachable_from y \<Longrightarrow> P"
  shows "P"
  using assms by (auto simp add: disj_def)

text \<open>Lemma 3.3 (i) in \cite{Poetzsch-Heffter97specification}\<close>
lemma disj1: "\<lbrakk>disj x y s; \<not> s\<turnstile> l reachable_from x; \<not> s\<turnstile> l reachable_from y\<rbrakk> 
              \<Longrightarrow> disj x y (s\<langle>l:=z\<rangle>)"
  by (auto simp add: disj_def)

text \<open>Lemma 3.3 (ii)\<close>
lemma disj2: 
  assumes disj_x_y: "disj x y s" 
  assumes disj_x_z: "disj x z s"
  assumes unreach_l_x: "\<not> s\<turnstile> l reachable_from x"
  shows "disj x y (s\<langle>l:=z\<rangle>)"
proof (rule disjI1)
  fix k 
  assume reach_k_x: "s\<langle>l := z\<rangle>\<turnstile> k reachable_from x"
  show "\<not> s\<langle>l := z\<rangle>\<turnstile> k reachable_from y"
  proof - 
    from unreach_l_x reach_k_x 
    have reach_s_k_x: "s\<turnstile> k reachable_from x"
      by simp
    with disj_x_z 
    have "\<not> s\<turnstile> k reachable_from z"
      by (simp add: disj_def)
    moreover from reach_s_k_x disj_x_y
    have "\<not> s\<turnstile> k reachable_from y"
      by (simp add: disj_def)
    ultimately show ?thesis
      by (rule reach3)
  qed
qed

   

text \<open>Lemma 3.3 (iii)\<close>
lemma disj3: assumes alive_x_s: "alive x s" 
  shows "disj x (new s t) (s\<langle>t\<rangle>)"
proof (rule disjI1,simp only: reach_alloc)
  fix l
  assume reach_l_x: "s\<turnstile> l reachable_from x"
  show "\<not> s\<turnstile> l reachable_from new s t"
  proof 
    assume reach_l_new: "s\<turnstile> l reachable_from new s t" 
    have unalive_new: "\<not> alive (new s t) s" by simp
    from this reach_l_new
    have  "new s t = ref l"
      by (rule ref_reach_unalive)
    moreover from alive_x_s reach_l_x 
    have "alive (ref l) s"
      by (rule alive_reach_alive)
    ultimately show False
      using unalive_new
      by simp
  qed
qed

text \<open>Lemma 3.3 (iv)\<close>
lemma disj4: "\<lbrakk>disj (objV C a) y s; CClassT C \<le> dtype f \<rbrakk>  
              \<Longrightarrow> disj (s@@(objV C a)..f) y s"
  by (auto simp add: disj_def)
  
lemma disj4': "\<lbrakk>disj (arrV T a) y s \<rbrakk>  
              \<Longrightarrow> disj (s@@(arrV T a).[i]) y s"
  by (auto simp add: disj_def)


subsection \<open>X-Equivalence\<close>

text \<open>We call two stores $s_1$ and $s_2$ equivalent wrt. a given value $X$
(which is called X-equivalence)
 iff $X$ and all values
reachable from $X$ in $s_1$ or $s_2$ have the same state \cite[p. 55]{Poetzsch-Heffter97specification}. 
This is tested by  the predicate
\<open>xeq\<close>. Lemma 3.4 of  \cite{Poetzsch-Heffter97specification} is then proven for \<open>xeq\<close>.
\<close> 

definition xeq:: "Value \<Rightarrow> Store \<Rightarrow> Store \<Rightarrow> bool" where
"xeq x s t = (alive x s = alive x t \<and> 
             (\<forall> l. s\<turnstile> l reachable_from x \<longrightarrow> s@@l = t@@l))"

abbreviation xeq_syntax :: "Store \<Rightarrow> Value \<Rightarrow> Store \<Rightarrow> bool"
  ("_/ (\<equiv>[_])/ _" [900,0,900] 900)
where "s \<equiv>[x] t == xeq x s t"


lemma xeqI: "\<lbrakk>alive x s = alive x t;  
             \<And> l. s\<turnstile> l reachable_from x \<Longrightarrow> s@@l = t@@l
             \<rbrakk> \<Longrightarrow> s \<equiv>[x] t"
  by (auto simp add: xeq_def)

text \<open>Lemma 3.4 (i) in  \cite{Poetzsch-Heffter97specification}.\<close>
lemma xeq1_refl: "s \<equiv>[x] s"
  by (simp add: xeq_def)

text \<open>Lemma 3.4 (i)\<close>
lemma xeq1_sym': 
  assumes s_t: "s \<equiv>[x] t"
  shows "t \<equiv>[x] s"
proof -
  from s_t have "alive x s = alive x t" by (simp add: xeq_def)
  moreover
  from s_t have "\<forall> l. s\<turnstile> l reachable_from x \<longrightarrow> s@@l = t@@l" 
    by (simp add: xeq_def)
  with reach9 [OF this]
  have "\<forall> l. t\<turnstile> l reachable_from x \<longrightarrow> t@@l = s@@l" 
    by simp
  ultimately show ?thesis
    by (simp add: xeq_def)
qed
 
lemma xeq1_sym: "s \<equiv>[x] t = t \<equiv>[x] s"
  by (auto intro: xeq1_sym')


text \<open>Lemma 3.4 (i)\<close>
lemma xeq1_trans [trans]: 
  assumes s_t: "s \<equiv>[x] t" 
  assumes t_r: "t \<equiv>[x] r" 
  shows "s \<equiv>[x] r"
proof -
  from s_t t_r
  have "alive x s = alive x r"
    by (simp add: xeq_def)
  moreover
  have "\<forall> l. s\<turnstile> l reachable_from x \<longrightarrow> s@@l = r@@l"
  proof (intro allI impI)
    fix l
    assume reach_l: "s\<turnstile> l reachable_from x"
    show "s@@l = r@@l"
    proof -
      from reach_l s_t have "s@@l=t@@l"
        by (simp add: xeq_def)
      also have "t@@l = r@@l"
      proof -
        from s_t have "\<forall> l. s\<turnstile> l reachable_from x \<longrightarrow> s@@l = t@@l"
          by (simp add: xeq_def)
        from reach9 [OF this] reach_l have "t\<turnstile> l reachable_from x"
          by simp
        with t_r show ?thesis
          by (simp add: xeq_def)
      qed
      finally show ?thesis .
    qed
  qed
  ultimately show ?thesis
    by (simp add: xeq_def)
qed
   

  
text \<open>Lemma 3.4 (ii)\<close>
lemma xeq2: 
  assumes xeq: "\<forall> x. s \<equiv>[x] t" 
  assumes static_eq: "\<forall> f. s@@(staticLoc f) = t@@(staticLoc f)" 
  shows "s = t"
proof (rule Store_eqI)
  from xeq 
  show "\<forall>x. alive x s = alive x t"
    by (simp add: xeq_def)
next
  show "\<forall>l. s@@l = t@@l"
  proof 
    fix l 
    show "s@@l = t@@l"
    proof (cases l)
      case (objLoc cf a)
      have "l = objLoc cf a" by fact
      hence "s\<turnstile> l reachable_from (objV (cls cf) a)"
        by simp
      with xeq show ?thesis
        by (simp add: xeq_def)
    next
      case (staticLoc f)
      have "l = staticLoc f" by fact
      with static_eq show ?thesis 
        by (simp add: xeq_def)
    next
      case (arrLenLoc T a)
      have "l = arrLenLoc T a" by fact
      hence "s\<turnstile> l reachable_from (arrV T a)"
        by simp
      with xeq show ?thesis
        by (simp add: xeq_def)
    next
      case (arrLoc T a i)
      have "l = arrLoc T a i" by fact
      hence "s\<turnstile> l reachable_from (arrV T a)"
        by simp
      with xeq show ?thesis
        by (simp add: xeq_def)
    qed
  qed
qed


text \<open>Lemma 3.4 (iii)\<close>
lemma xeq3: 
  assumes unreach_l: "\<not> s\<turnstile> l reachable_from x" 
  shows "s \<equiv>[x] s\<langle>l:=y\<rangle>"
proof (rule xeqI)
  show "alive x s = alive x (s\<langle>l := y\<rangle>)"
    by simp
next
  fix k 
  assume reach_k: "s\<turnstile> k reachable_from x"
  with unreach_l have "l\<noteq>k" by auto
  then show "s@@k = s\<langle>l := y\<rangle>@@k"
    by simp
qed



text \<open>Lemma 3.4 (iv)\<close>
lemma xeq4: assumes not_new: "x \<noteq> new s t" 
  shows "s \<equiv>[x] s\<langle>t\<rangle>"
proof (rule xeqI)
  from not_new 
  show "alive x s = alive x (s\<langle>t\<rangle>)"
    by (simp add: alive_alloc_exhaust)
next
  fix l
  assume reach_l: "s\<turnstile> l reachable_from x"
  show "s@@l = s\<langle>t\<rangle>@@l"
  proof (cases "isNewArr t \<longrightarrow> l \<noteq> arr_len (new s t)")
    case True
    with reach_l show ?thesis
      by simp
  next
    case False
    then obtain T n where t: "t = new_array T n" and
                          l: "l = arr_len (new s t)"
      by (cases t) auto
    hence "ref l = new s t"
      by simp
    from this reach_l
    have "x = new s t"
      by (rule loc_new_reach)
    with not_new show ?thesis ..
  qed
qed

text \<open>Lemma 3.4 (v)\<close>
lemma xeq5: "s \<equiv>[x] t \<Longrightarrow> s\<turnstile> l reachable_from x = t\<turnstile> l reachable_from x"
  by (rule reach9) (simp add:  xeq_def)
  

subsection \<open>T-Equivalence\<close>

text \<open>T-equivalence is the extension of X-equivalence from values to types. Two stores are
T-equivalent iff they are X-equivalent for all values of type T. This is formalized by the
predicate \<open>teq\<close> \cite[p. 55]{Poetzsch-Heffter97specification}.\<close>

definition teq:: "Javatype \<Rightarrow> Store \<Rightarrow> Store \<Rightarrow> bool" where
"teq t s1 s2 = (\<forall> x. typeof x \<le> t \<longrightarrow> s1 \<equiv>[x] s2)"

subsection \<open>Less Alive\<close>

text \<open>To specify that methods have no side-effects, the following binary relation on stores 
plays a prominent role. It expresses that the two stores differ only in values that are alive
in the store passed as first argument. This is formalized by the predicate \<open>lessalive\<close>
\cite[p. 55]{Poetzsch-Heffter97specification}.
The stores have to be X-equivalent for the references of the
first store that are alive, and the values of the static fields have to be the same in both stores.
\<close>

definition lessalive:: "Store \<Rightarrow> Store \<Rightarrow> bool" ("_/ \<lless> _" [70,71] 70)
  where "lessalive s t = ((\<forall> x. alive x s \<longrightarrow> s \<equiv>[x] t) \<and> (\<forall> f. s@@staticLoc f = t@@staticLoc f))"

text \<open>We define an introduction rule for the new operator.\<close>

lemma lessaliveI: 
  "\<lbrakk>\<And> x. alive x s \<Longrightarrow>  s \<equiv>[x] t; \<And> f. s@@staticLoc f = t@@staticLoc f\<rbrakk>
   \<Longrightarrow> s \<lless> t"
by (simp add: lessalive_def)

text \<open>It can be shown that \<open>lessalive\<close> is reflexive, transitive and antisymmetric.\<close>

lemma lessalive_refl: "s \<lless> s"
  by (simp add: lessalive_def xeq1_refl)

lemma lessalive_trans [trans]: 
  assumes s_t: "s \<lless> t"
  assumes t_w: "t \<lless> w"
  shows "s \<lless> w"
proof (rule lessaliveI)
  fix x 
  assume alive_x_s: "alive x s"
  with s_t have "s \<equiv>[x] t"
    by (simp add: lessalive_def)
  also
  have "t \<equiv>[x] w"
  proof -
    from alive_x_s s_t have "alive x t" by (simp add: lessalive_def xeq_def)
    with t_w show ?thesis
      by (simp add: lessalive_def)
  qed
  finally show "s \<equiv>[x] w".
next
  fix f
  from s_t t_w show "s@@staticLoc f = w@@staticLoc f"
    by (simp add: lessalive_def)
qed

lemma lessalive_antisym:
  assumes s_t: "s \<lless> t"
  assumes t_s: "t \<lless> s"
  shows "s = t"
proof (rule xeq2)
  show "\<forall>x. s \<equiv>[x] t"
  proof 
    fix x show "s \<equiv>[x] t"
    proof (cases "alive x s")
      case True
      with s_t show ?thesis by (simp add: lessalive_def)
    next
      case False note unalive_x_s = this
      show ?thesis
      proof (cases "alive x t")
        case True
        with t_s show ?thesis 
          by (subst xeq1_sym) (simp add: lessalive_def)
      next
        case False 
        show ?thesis
        proof (rule xeqI)
          from False unalive_x_s show "alive x s = alive x t" by simp
        next
          fix l assume reach_s_x: "s\<turnstile> l reachable_from x"
          with unalive_x_s have x: "x = ref l" 
            by (rule ref_reach_unalive)
          with unalive_x_s have "s@@l = init (ltype l)"
            by simp
          also from reach_s_x x have "t\<turnstile> l reachable_from x"
            by (auto intro: reach.Immediate unreachable_Null)
          with False x have "t@@l = init (ltype l)"
            by simp
          finally show "s@@l = t@@l"
            by simp
        qed
      qed
    qed
  qed
next
  from s_t show "\<forall>f. s@@staticLoc f = t@@staticLoc f"
    by (simp add: lessalive_def)
qed

text \<open>This gives us a partial ordering on the store. Thus, the type @{typ "Store"}
can be added to the appropriate type class @{term "ord"} which lets us define the $<$ and
$\leq$ symbols, and to the type class  @{term "order"} which axiomatizes partial orderings.
\<close>

instantiation Store :: order
begin

definition
  le_Store_def: "s \<le> t \<longleftrightarrow> s \<lless> t"

definition
  less_Store_def: "(s::Store) < t \<longleftrightarrow> s \<le> t \<and> \<not> t \<le> s"

text \<open>We prove Lemma 3.5 of \cite[p. 56]{Poetzsch-Heffter97specification} for this relation.
\<close>

text \<open>Lemma 3.5 (i)\<close>

instance  proof 
  fix s t w:: "Store"
  {
    show "s \<le> s"
      by (simp add: le_Store_def lessalive_refl)
  next
    assume "s \<le> t" "t \<le> w"
    then show "s \<le> w"
      by (unfold le_Store_def) (rule lessalive_trans) 
  next
    assume "s \<le> t" "t \<le> s" 
    then show "s = t"
      by (unfold le_Store_def) (rule lessalive_antisym) 
  next
    show "(s < t) = (s \<le> t \<and> \<not> t \<le> s)"
      by (simp add: less_Store_def)
  }
qed

end

text \<open>Lemma 3.5 (ii)\<close>
lemma lessalive2: "\<lbrakk>s \<lless> t; alive x s\<rbrakk> \<Longrightarrow> alive x t"
  by (simp add: lessalive_def xeq_def)
  

text \<open>Lemma 3.5 (iii)\<close>
lemma lessalive3: 
  assumes s_t: "s \<lless> t" 
  assumes alive: "alive x s \<or> \<not> alive x t"
  shows "s \<equiv>[x] t"
proof (cases "alive x s")
  case True
  with s_t show ?thesis
    by (simp add: lessalive_def)
next
  case False
  note unalive_x_s = this
  with alive have unalive_x_t: "\<not> alive x t"
    by simp
  show ?thesis
  proof (rule xeqI)
    from False alive show "alive x s = alive x t"
      by simp
  next
    fix l assume reach_s_x: "s\<turnstile> l reachable_from x"
    with unalive_x_s have x: "x = ref l" 
      by (rule ref_reach_unalive)
    with unalive_x_s have "s@@l = init (ltype l)"
      by simp
    also from reach_s_x x have "t\<turnstile> l reachable_from x"
      by (auto intro: reach.Immediate unreachable_Null)
    with unalive_x_t x have "t@@l = init (ltype l)"
      by simp
    finally show "s@@l = t@@l"
      by simp
  qed
qed
   
text \<open>Lemma 3.5 (iv)\<close>
lemma lessalive_update [simp,intro]: 
  assumes s_t: "s \<lless> t" 
  assumes unalive_l: "\<not> alive (ref l) t"
  shows "s \<lless> t\<langle>l:=x\<rangle>"
proof -
  from unalive_l have "t\<langle>l:=x\<rangle> = t"
    by simp
  with s_t show ?thesis by simp
qed

lemma Xequ4':  
  assumes alive: "alive x s" 
  shows "s \<equiv>[x] s\<langle>t\<rangle>"
proof -
  from alive have "x \<noteq> new s t"
    by auto
  thus ?thesis
    by (rule xeq4)
qed

  

text \<open>Lemma 3.5 (v)\<close>
lemma lessalive_alloc [simp,intro]: "s \<lless> s\<langle>t\<rangle>"
  by (simp add: lessalive_def Xequ4')
 

subsection \<open>Reachability of Types from Types\<close>

text \<open>The predicate \<open>treach\<close> denotes the fact that the first type reaches 
the second type by stepping finitely many times from a type to the range type of one 
of its fields. This formalization diverges from \cite[p. 106]{Poetzsch-Heffter97specification} 
in that it does not include the number of steps that are allowed to reach the second type.
Reachability of types is a static approximation of reachability in
the store. If I cannot reach the type of a location from the type of a
reference, I cannot reach the location from the reference. See lemma  
\<open>not_treach_ref_impl_not_reach\<close> below.
\<close>

inductive
  treach :: "Javatype \<Rightarrow> Javatype \<Rightarrow> bool"
where
  Subtype:       "U \<le> T \<Longrightarrow> treach T U"
| Attribute:     "\<lbrakk>treach T S; S \<le> dtype f; U \<le> rtype f\<rbrakk>  \<Longrightarrow> treach T U"
| ArrLength:     "treach (ArrT AT) IntgT"
| ArrElem:       "treach (ArrT AT) (at2jt AT)"
| Trans [trans]: "\<lbrakk>treach T U; treach U V\<rbrakk> \<Longrightarrow> treach T V"


lemma treach_ref_l [simp,intro]: 
  assumes not_Null: "ref l \<noteq> nullV"
  shows "treach (typeof (ref l)) (ltype l)"
proof (cases l)
  case (objLoc cf a)
  have "l=objLoc cf a" by fact
  moreover
  have "treach (CClassT (cls cf)) (rtype (att cf))"
    by (rule treach.Attribute [where ?f="att cf" and ?S="CClassT (cls cf)"])
       (auto intro: treach.Subtype)
  ultimately show ?thesis
    by simp
next
  case (staticLoc f)
  have "l=staticLoc f" by fact
  hence "ref l = nullV" by simp
  with not_Null show ?thesis
    by simp
next
  case (arrLenLoc T a)
  have "l=arrLenLoc T a" by fact
  then show ?thesis
    by (auto intro: treach.ArrLength)
next
  case (arrLoc T a i)
  have "l=arrLoc T a i" by fact
  then show ?thesis
    by (auto intro: treach.ArrElem)
qed

lemma treach_ref_l' [simp,intro]:
  assumes not_Null: "ref l \<noteq> nullV"
  shows "treach (typeof (ref l)) (typeof (s@@l))"
proof -
  from not_Null have "treach (typeof (ref l)) (ltype l)" by (rule treach_ref_l)
  also have "typeof (s@@l) \<le> ltype l"
    by simp
  hence "treach (ltype l) (typeof (s@@l))"
    by (rule treach.intros)
  finally show ?thesis .
qed
  

lemma reach_impl_treach: 
  assumes reach_l: "s \<turnstile> l reachable_from x"
  shows "treach (typeof x) (ltype l)"
using reach_l
proof (induct)
  case (Immediate l)
  have "ref l \<noteq> nullV" by fact
  then show "treach (typeof (ref l)) (ltype l)"
    by (rule treach_ref_l)
next
  case (Indirect l k)
  have "treach (typeof (s@@k)) (ltype l)" by fact
  moreover
  have "ref k \<noteq> nullV" by fact
  hence "treach (typeof (ref k)) (typeof (s@@k))"
    by simp
  ultimately show "treach (typeof (ref k)) (ltype l)"
    by (iprover intro: treach.Trans)
qed

lemma not_treach_ref_impl_not_reach: 
  assumes not_treach: "\<not> treach (typeof x) (typeof (ref l))"
  shows "\<not> s \<turnstile> l reachable_from x"
proof 
  assume reach_l: "s\<turnstile> l reachable_from x"
  from this not_treach
  show False
  proof (induct)
    case (Immediate l)
    have "\<not> treach (typeof (ref l)) (typeof (ref l))" by fact
    thus False by (iprover intro: treach.intros order_refl)
  next
    case (Indirect l k)
    have hyp: "\<not> treach (typeof (s@@k)) (typeof (ref l)) \<Longrightarrow> False" by fact
    have not_Null: "ref k \<noteq> nullV" by fact
    have not_k_l:"\<not> treach (typeof (ref k)) (typeof (ref l))" by fact
    show False
    proof (cases "treach (typeof (s@@k)) (typeof (ref l))")
      case False thus False by (rule hyp)
    next
      case True
      from not_Null have "treach (typeof (ref k)) (typeof (s@@k))"
        by (rule treach_ref_l')
      also note True
      finally have "treach (typeof (ref k)) (typeof (ref l))" .
      with not_k_l show False ..
    qed
  qed
qed

text \<open>Lemma 4.6 in \cite[p. 107]{Poetzsch-Heffter97specification}.\<close>
lemma treach1: 
  assumes x_t: "typeof x \<le> T" 
  assumes not_treach: "\<not> treach T (typeof (ref l))"
  shows "\<not> s \<turnstile> l reachable_from x"
proof -
  have "\<not> treach (typeof x) (typeof (ref l))"
  proof 
    from x_t have "treach T (typeof x)" by (rule treach.intros)
    also assume "treach (typeof x) (typeof (ref l))"
    finally have "treach T (typeof (ref l))" .
    with not_treach show False ..
  qed
  thus ?thesis
    by (rule not_treach_ref_impl_not_reach)
qed

  
end
