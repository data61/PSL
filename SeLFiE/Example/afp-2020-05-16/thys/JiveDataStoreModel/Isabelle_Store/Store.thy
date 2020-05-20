(*  Title:       Jive Data and Store Model
    Author:      Norbert Schirmer <schirmer at informatik.tu-muenchen.de>, 2003
    Maintainer:  Nicole Rauch <rauch at informatik.uni-kl.de>
    License:     LGPL
*)

section \<open>Store\<close>

theory Store
imports Location
begin

subsection \<open>New\<close>
text \<open>The store provides a uniform interface to allocate new objects and
new arrays. The constructors of this datatype distinguish both cases.
\<close>
datatype New = new_instance CTypeId    \<comment> \<open>New object, can only be of a concrete class type\<close> 
             | new_array Arraytype nat \<comment> \<open>New array with given size\<close>

text \<open>The discriminator \<open>isNewArr\<close> can be used to distinguish both 
kinds of newly created elements.
\<close>

definition isNewArr :: "New \<Rightarrow> bool" where
"isNewArr t = (case t of 
                 new_instance C \<Rightarrow> False     
               | new_array T l \<Rightarrow> True)"   

lemma isNewArr_simps [simp]:
"isNewArr (new_instance C) = False"
"isNewArr (new_array T l)  = True"
  by (simp_all add: isNewArr_def)

text \<open>The function \<open>typeofNew\<close> yields the type of the newly created
element.\<close>

definition typeofNew :: "New \<Rightarrow> Javatype" where
"typeofNew n = (case n of
                  new_instance C \<Rightarrow> CClassT C
                | new_array T l  \<Rightarrow> ArrT T)"

lemma typeofNew_simps:
"typeofNew (new_instance C) = CClassT C"
"typeofNew (new_array T l)  = ArrT T"
  by (simp_all add: typeofNew_def)

subsection \<open>The Definition of the Store\<close>

text \<open>In our store model, all objects\footnote{In the following, the term ``objects'' 
includes arrays. This keeps the explanations compact.}
of all classes exist at all times, but only those objects that have already been allocated
are alive. Objects cannot be deallocated, thus an object that once gained
the aliveness status cannot lose it later on.
\\[12pt]
 To model the store, we need two functions that give us fresh object Id's for 
the allocation of new objects (function \<open>newOID\<close>) and arrays
(function \<open>newAID\<close>) as well as a function that maps locations to
their contents (function \<open>vals\<close>).\<close>

record StoreImpl = newOID :: "CTypeId \<Rightarrow> ObjectId"
                   newAID :: "Arraytype \<Rightarrow> ObjectId"
                   vals   :: "Location \<Rightarrow> Value"

text \<open>The function \<open>aliveImpl\<close> determines for a given value whether
it is alive in a given store.
\<close>

definition aliveImpl::"Value \<Rightarrow> StoreImpl \<Rightarrow> bool" where
"aliveImpl x s = (case x of
                    boolV b  \<Rightarrow> True
                  | intgV i  \<Rightarrow> True
                  | shortV s  \<Rightarrow> True
                  | byteV by  \<Rightarrow> True
                  | objV C a \<Rightarrow> (a < newOID s C)
                  | arrV T a \<Rightarrow> (a < newAID s T)
                  | nullV    \<Rightarrow> True)"


text \<open>The store itself is defined as new type. The store ensures
and maintains the following 
properties: All stored values are alive; for all locations whose values are
not alive, the store yields the location type's init value; and
all stored values are of the correct type (i.e.~of the type of the location
they are stored in).
\<close>

definition "Store = {s. (\<forall> l. aliveImpl (vals s l) s) \<and> 
                  (\<forall> l. \<not> aliveImpl (ref l) s \<longrightarrow> vals s l = init (ltype l)) \<and>
                  (\<forall> l. typeof (vals s l) \<le> ltype l)}"

typedef Store = Store
  unfolding Store_def
  apply (rule exI [where ?x="\<lparr> newOID = (\<lambda>C. 0),
                          newAID = (\<lambda>T. 0),
                          vals = (\<lambda>l. init (ltype l)) \<rparr>"])
  apply (auto simp add: aliveImpl_def init_def NullT_leaf_array split: Javatype.splits)
  done

text \<open>One might also model the Store as axiomatic type class and prove that the type StoreImpl belongs
to this type class. This way, a clearer separation between the axiomatic description of the store and its
properties on the one hand and the realization that has been chosen in this formalization on the other hand
could be achieved. Additionally, it would be easier to make use of  different store implementations that
might have different additional features. This separation remains to be performed as future work.
\<close>

subsection\<open>The Store Interface\<close>

text \<open>The Store interface consists of five functions:
\<open>access\<close> to read the value that is stored at a location;
\<open>alive\<close> to test whether a value is alive in the store;
\<open>alloc\<close> to allocate a new element in the store;
\<open>new\<close> to read the value of a newly allocated element;
\<open>update\<close> to change the value that is stored at a location.
\<close>

consts access:: "Store \<Rightarrow> Location \<Rightarrow> Value"  ("_@@_" [71,71] 70)     
       alive:: "Value \<Rightarrow> Store \<Rightarrow> bool"
       alloc:: "Store \<Rightarrow> New \<Rightarrow> Store" 
       new:: "Store \<Rightarrow> New \<Rightarrow> Value"
       update:: "Store \<Rightarrow> Location \<Rightarrow> Value \<Rightarrow> Store"
       
nonterminal smodifybinds and smodifybind
syntax
  "_smodifybind" :: "['a, 'a]     \<Rightarrow> smodifybind" ("(2_ :=/ _)")
  ""         :: "smodifybind \<Rightarrow> smodifybinds"     ("_")
  ""         :: "CTypeId \<Rightarrow> smodifybind"          ("_")
  "_smodifybinds":: "[smodifybind, smodifybinds] => smodifybinds" ("_,/ _")
  "_sModify"  :: "['a, smodifybinds] \<Rightarrow> 'a"       ("_/\<langle>(_)\<rangle>" [900,0] 900)
translations
  "_sModify s (_smodifybinds b bs)"  == "_sModify (_sModify s b) bs"
  "s\<langle>x:=y\<rangle>"                          == "CONST update s x y"
  "s\<langle>c\<rangle>"                             == "CONST alloc s c" 
 

text \<open>With this syntactic setup we can write chains of (array) updates and 
allocations like in the
following term  
@{term "s\<langle>new_instance Node,x:=y,z:=intgV 3,new_array IntgAT 3,a.[i]:=intgV 4,k:=boolV True\<rangle>"}. 
\<close>

text \<open>In the following, the definitions of the five store interface functions and some lemmas 
about them are given.\<close>

overloading alive \<equiv> alive
begin
  definition alive where "alive x s \<equiv> aliveImpl x (Rep_Store s)"
end

lemma alive_trivial_simps [simp,intro]:
"alive (boolV b) s"
"alive (intgV i) s"
"alive (shortV sh) s"
"alive (byteV by) s"
"alive nullV     s"
  by (simp_all add: alive_def aliveImpl_def)

overloading
  access \<equiv> access
  update \<equiv> update
  alloc \<equiv> alloc
  new \<equiv> new
begin

definition access
  where "access s l \<equiv> vals (Rep_Store s) l"

definition update
  where "update s l v \<equiv>
    if alive (ref l) s \<and> alive v s \<and> typeof v \<le> ltype l 
    then Abs_Store ((Rep_Store s)\<lparr>vals:=(vals (Rep_Store s))(l:=v)\<rparr>)
    else s"

definition alloc
  where "alloc s t \<equiv>
    (case t of 
       new_instance C 
        \<Rightarrow> Abs_Store 
            ((Rep_Store s)\<lparr>newOID := \<lambda> D. if C=D 
                              then Suc (newOID (Rep_Store s) C) 
                              else newOID (Rep_Store s) D\<rparr>)
     | new_array T l
        \<Rightarrow> Abs_Store
            ((Rep_Store s)\<lparr>newAID := \<lambda> S. if T=S 
                             then Suc (newAID (Rep_Store s) T)
                             else newAID (Rep_Store s) S,
                           vals :=  (vals (Rep_Store s))
                                      (arrLenLoc T (newAID (Rep_Store s) T) 
                                        := intgV (int l))\<rparr>))"

definition new
  where "new s t \<equiv>
    (case t of
      new_instance C \<Rightarrow> objV C (newOID (Rep_Store s) C)
    | new_array T l  \<Rightarrow> arrV T (newAID (Rep_Store s) T))"

end

text \<open>The predicate \<open>wts\<close> tests whether the store is well-typed.\<close>

definition
wts :: "Store \<Rightarrow> bool" where
"wts OS = (\<forall> (l::Location) . (typeof (OS@@l)) \<le> (ltype l))"


subsection \<open>Derived Properties of the Store\<close>

text \<open>In this subsection, a number of lemmas formalize various properties of the Store.
Especially the 13 axioms are proven that must hold for a modelling of a Store 
(see \cite[p. 45]{Poetzsch-Heffter97specification}). They are labeled with
Store1 to Store13.\<close>

lemma alive_init [simp,intro]: "alive (init T) s"
  by (cases T) (simp_all add: alive_def aliveImpl_def) 

lemma alive_loc [simp]: 
  "\<lbrakk>isObjV x; typeof x \<le> dtype f\<rbrakk> \<Longrightarrow> alive (ref (x..f)) s = alive x s"
  by (cases x) (simp_all)

lemma alive_arr_loc [simp]: 
  "isArrV x \<Longrightarrow> alive (ref (x.[i])) s = alive x s"
  by (cases x) (simp_all)

lemma alive_arr_len [simp]: 
  "isArrV x \<Longrightarrow> alive (ref (arr_len x)) s = alive x s"
  by (cases x) (simp_all)

lemma ref_arr_len_new [simp]: 
  "ref (arr_len (new s (new_array T n))) = new s (new_array T n)"
  by (simp add: new_def)

lemma ref_arr_loc_new [simp]: 
  "ref ((new s (new_array T n)).[i]) = new s (new_array T n)"
  by (simp add: new_def)

lemma ref_loc_new [simp]: "CClassT C \<le> dtype f 
  \<Longrightarrow> ref ((new s (new_instance C))..f) = new s (new_instance C)"
  by (simp add: new_def)

lemma access_type_safe [simp,intro]: "typeof (s@@l) \<le> ltype l" 
proof -
  have "Rep_Store s \<in> Store"    
    by (rule Rep_Store)
  thus ?thesis
    by (auto simp add: access_def Store_def)
qed

text \<open>The store is well-typed by construction.\<close>
lemma always_welltyped_store: "wts OS"
  by (simp add: wts_def access_type_safe)


text \<open>Store8\<close>
lemma alive_access [simp,intro]: "alive (s@@l) s"
proof -
  have "Rep_Store s \<in> Store"
    by (rule Rep_Store)
  thus ?thesis
    by (auto simp add: access_def Store_def alive_def aliveImpl_def)
qed

text \<open>Store3\<close>
lemma access_unalive [simp]: 
  assumes unalive: "\<not> alive (ref l) s" 
  shows "s@@l = init (ltype l)"
proof -
  have "Rep_Store s \<in> Store"
    by (rule Rep_Store)
  with unalive show ?thesis
    by (simp add: access_def Store_def alive_def aliveImpl_def)
qed


lemma update_induct:
  assumes skip: "P s"
  assumes update: "\<lbrakk>alive (ref l) s; alive v s; typeof v \<le> ltype l\<rbrakk> \<Longrightarrow>
               P (Abs_Store ((Rep_Store s)\<lparr>vals:=(vals (Rep_Store s))(l:=v)\<rparr>))" 
  shows "P (s\<langle>l:=v\<rangle>)"
  using update skip 
  by (simp add: update_def)

lemma vals_update_in_Store:
  assumes alive_l: "alive (ref l) s" 
  assumes alive_y: "alive y s" 
  assumes type_conform: "typeof y \<le> ltype l"
  shows "(Rep_Store s\<lparr>vals := (vals (Rep_Store s))(l := y)\<rparr>) \<in> Store" 
  (is "?s_upd \<in> Store")
proof -
  have s: "Rep_Store s \<in> Store"
    by (rule Rep_Store)
  have alloc_eq: "newOID ?s_upd = newOID (Rep_Store s)"
    by simp
  have "\<forall> l. aliveImpl (vals ?s_upd l) ?s_upd"
  proof 
    fix k
    show "aliveImpl (vals ?s_upd k) ?s_upd"
    proof (cases "k=l")
      case True
      with alive_y show ?thesis
        by (simp add: alloc_eq alive_def aliveImpl_def split: Value.splits)
    next
      case False
      from s have "\<forall> l. aliveImpl (vals (Rep_Store s) l) (Rep_Store s)"
        by (simp add: Store_def)
      with False show ?thesis
        by (simp add: aliveImpl_def split: Value.splits)
    qed
  qed
  moreover
  have "\<forall> l. \<not> aliveImpl (ref l) ?s_upd \<longrightarrow> vals ?s_upd l = init (ltype l)"
  proof (intro allI impI)
    fix k
    assume unalive: "\<not> aliveImpl (ref k) ?s_upd"
    show "vals ?s_upd k = init (ltype k)"
    proof -
      from unalive alive_l
      have "k\<noteq>l"
        by (auto simp add: alive_def aliveImpl_def split: Value.splits)
      hence "vals ?s_upd k = vals (Rep_Store s) k"
        by simp
      moreover from unalive 
      have "\<not> aliveImpl (ref k) (Rep_Store s)"
        by (simp add: aliveImpl_def split: Value.splits)
      ultimately show ?thesis
        using s by (simp add: Store_def)
    qed
  qed
  moreover
  have "\<forall> l. typeof (vals ?s_upd l) \<le> ltype l"
  proof
    fix k show "typeof (vals ?s_upd k) \<le> ltype k"
    proof (cases "k=l")
      case True
      with type_conform show ?thesis
        by simp
    next
      case False
      hence "vals ?s_upd k = vals (Rep_Store s) k"
        by simp
      with s show ?thesis
        by (simp add: Store_def)
    qed
  qed
  ultimately show ?thesis
    by (simp add: Store_def)
qed

text \<open>Store6\<close>
lemma alive_update_invariant [simp]: "alive x (s\<langle>l:=y\<rangle>) = alive x s"
proof (rule update_induct)
  show "alive x s = alive x s"..
next
  assume "alive (ref l) s" "alive y s" "typeof y \<le> ltype l"
  hence "Rep_Store 
          (Abs_Store (Rep_Store s\<lparr>vals := (vals (Rep_Store s))(l := y)\<rparr>))
         = Rep_Store s\<lparr>vals := (vals (Rep_Store s))(l := y)\<rparr>"
    by (rule vals_update_in_Store [THEN Abs_Store_inverse])
  thus "alive x
         (Abs_Store (Rep_Store s\<lparr>vals := (vals (Rep_Store s))(l := y)\<rparr>)) =
        alive x s"
    by (simp add: alive_def aliveImpl_def split: Value.split)
qed

text \<open>Store1\<close>
lemma access_update_other [simp]: 
  assumes neq_l_m: "l \<noteq> m" 
  shows "s\<langle>l:=x\<rangle>@@m = s@@m"
proof (rule update_induct)
  show "s@@m = s@@m" ..
next
  assume "alive (ref l) s" "alive x s" "typeof x \<le> ltype l"
  hence "Rep_Store 
          (Abs_Store (Rep_Store s\<lparr>vals := (vals (Rep_Store s))(l := x)\<rparr>))
         = Rep_Store s\<lparr>vals := (vals (Rep_Store s))(l := x)\<rparr>"
    by (rule vals_update_in_Store [THEN Abs_Store_inverse])
  with neq_l_m 
  show "Abs_Store (Rep_Store s\<lparr>vals := (vals (Rep_Store s))(l := x)\<rparr>)@@m = s@@m"
    by (auto simp add: access_def)
qed

text \<open>Store2\<close>
lemma update_access_same [simp]: 
  assumes alive_l: "alive (ref l) s" 
  assumes alive_x: "alive x s" 
  assumes widen_x_l: "typeof x \<le> ltype l"
  shows "s\<langle>l:=x\<rangle>@@l = x"
proof -
  from alive_l alive_x widen_x_l
  have "Rep_Store 
          (Abs_Store (Rep_Store s\<lparr>vals := (vals (Rep_Store s))(l := x)\<rparr>))
         = Rep_Store s\<lparr>vals := (vals (Rep_Store s))(l := x)\<rparr>"
    by (rule vals_update_in_Store [THEN Abs_Store_inverse])
  hence "Abs_Store (Rep_Store s\<lparr>vals := (vals (Rep_Store s))(l := x)\<rparr>)@@l = x"
    by (simp add: access_def)
  with alive_l alive_x widen_x_l 
  show ?thesis
    by (simp add: update_def)
qed

text \<open>Store4\<close>
lemma update_unalive_val [simp,intro]: "\<not> alive x s \<Longrightarrow> s\<langle>l:=x\<rangle> = s"
  by (simp add: update_def)

lemma update_unalive_loc [simp,intro]: "\<not> alive (ref l) s \<Longrightarrow> s\<langle>l:=x\<rangle> = s"
  by (simp add: update_def)

lemma update_type_mismatch [simp,intro]: "\<not> typeof x \<le> ltype l \<Longrightarrow> s\<langle>l:=x\<rangle> = s"
  by (simp add: update_def)


text \<open>Store9\<close>
lemma alive_primitive [simp,intro]: "isprimitive (typeof x) \<Longrightarrow> alive x s"
  by (cases x) (simp_all)

text \<open>Store10\<close>
lemma new_unalive_old_Store [simp]: "\<not> alive (new s t) s"
  by (cases t) (simp_all add: alive_def aliveImpl_def new_def)

lemma alloc_new_instance_in_Store:
"(Rep_Store s\<lparr>newOID := \<lambda>D. if C = D
                                   then Suc (newOID (Rep_Store s) C)
                                   else newOID (Rep_Store s) D\<rparr>) \<in> Store"
(is "?s_alloc \<in> Store")
proof -
  have s: "Rep_Store s \<in> Store"
    by (rule Rep_Store)
  hence "\<forall> l. aliveImpl (vals (Rep_Store s) l) (Rep_Store s)"
    by (simp add: Store_def)
  then
  have "\<forall> l. aliveImpl (vals ?s_alloc l) ?s_alloc"
    by (auto intro: less_SucI simp add: aliveImpl_def split: Value.splits)
  moreover
  have "\<forall> l. \<not> aliveImpl (ref l) ?s_alloc \<longrightarrow> vals ?s_alloc l = init (ltype l)"
  proof (intro allI impI)
    fix l
    assume "\<not> aliveImpl (ref l) ?s_alloc"
    hence "\<not> aliveImpl (ref l) (Rep_Store s)"
      by (simp add: aliveImpl_def split: Value.splits if_split_asm)
    with s have "vals (Rep_Store s) l = init (ltype l)"
      by (simp add: Store_def)
    thus "vals ?s_alloc l = init (ltype l)"
      by simp
  qed
  moreover 
  from s have "\<forall> l. typeof (vals ?s_alloc l) \<le> ltype l"
    by (simp add: Store_def)
  ultimately
  show ?thesis
    by (simp add: Store_def)
qed

lemma alloc_new_array_in_Store:
"(Rep_Store s \<lparr>newAID :=
                  \<lambda>S. if T = S
                      then Suc (newAID (Rep_Store s) T)
                      else newAID (Rep_Store s) S,
               vals := (vals (Rep_Store s))
                         (arrLenLoc T
                           (newAID (Rep_Store s) T) :=
                           intgV (int n))\<rparr>) \<in> Store"
(is "?s_alloc \<in> Store")
proof -
  have s: "Rep_Store s \<in> Store"
    by (rule Rep_Store)
  have "\<forall> l. aliveImpl (vals ?s_alloc l) ?s_alloc"
  proof 
    fix l show "aliveImpl (vals ?s_alloc l) ?s_alloc"
    proof (cases "l = arrLenLoc T (newAID (Rep_Store s) T)")
      case True
      thus ?thesis
        by (simp add: aliveImpl_def split: Value.splits)
    next
      case False
      from s have "\<forall> l. aliveImpl (vals (Rep_Store s) l) (Rep_Store s)"
        by (simp add: Store_def)
      with False show ?thesis
        by (auto intro: less_SucI simp add: aliveImpl_def split: Value.splits)
    qed
  qed
  moreover
  have "\<forall> l. \<not> aliveImpl (ref l) ?s_alloc \<longrightarrow> vals ?s_alloc l = init (ltype l)"
  proof (intro allI impI)
    fix l
    assume unalive: "\<not> aliveImpl (ref l) ?s_alloc"
    show "vals ?s_alloc l = init (ltype l)"
    proof (cases "l = arrLenLoc T (newAID (Rep_Store s) T)")
      case True
      with unalive show ?thesis by (simp add: aliveImpl_def)
    next
      case False
      from unalive
      have "\<not> aliveImpl (ref l) (Rep_Store s)"
        by (simp add: aliveImpl_def split: Value.splits if_split_asm)
      with s have "vals (Rep_Store s) l = init (ltype l)"
        by (simp add: Store_def)
      with False show ?thesis 
        by simp
    qed
  qed
  moreover 
  from s have "\<forall> l. typeof (vals ?s_alloc l) \<le> ltype l"
    by (simp add: Store_def)
  ultimately
  show ?thesis
    by (simp add: Store_def)
qed


lemma new_alive_alloc [simp,intro]: "alive (new s t) (s\<langle>t\<rangle>)"
proof (cases t)
  case new_instance thus ?thesis 
    by (simp add: alive_def aliveImpl_def new_def alloc_def
                  alloc_new_instance_in_Store [THEN Abs_Store_inverse])
next
  case new_array thus ?thesis
    by (simp add: alive_def aliveImpl_def new_def alloc_def
                  alloc_new_array_in_Store [THEN Abs_Store_inverse])
qed
 
lemma value_class_inhabitants: 
"(\<forall>x. typeof x = CClassT typeId \<longrightarrow> P x) = (\<forall> a. P (objV typeId a))"
  (is "(\<forall> x. ?A x) = ?B")
proof 
  assume "\<forall> x. ?A x" thus "?B"
    by simp
next
  assume B: "?B" show "\<forall> x. ?A x"
  proof
    fix x from B show "?A x"
      by (cases x) auto
  qed
qed
   
lemma value_array_inhabitants: 
"(\<forall>x. typeof x = ArrT typeId \<longrightarrow> P x) = (\<forall> a. P (arrV typeId a))"
  (is "(\<forall> x. ?A x) = ?B")
proof 
  assume "\<forall> x. ?A x" thus "?B"
    by simp
next
  assume B: "?B" show "\<forall> x. ?A x"
  proof
    fix x from B show "?A x"
      by (cases x) auto
  qed
qed


text \<open>The following three lemmas are helper lemmas that are not related to the store theory.
They might as well be stored in a separate helper theory.
\<close>

lemma le_Suc_eq: "(\<forall>a. (a < Suc n) = (a < Suc m)) = (\<forall>a. (a < n) = (a < m))"
 (is "(\<forall>a. ?A a) = (\<forall> a. ?B a)")
proof
  assume "\<forall>a. ?A a" thus "\<forall> a. ?B a"
    by fastforce
next
  assume B: "\<forall> a. ?B a"
  show "\<forall>a. ?A a"
  proof
    fix a 
    from B show "?A a"
      by (cases a) simp_all
  qed
qed

lemma all_le_eq_imp_eq: "\<And> c::nat. (\<forall>a. (a < d) = (a < c)) \<longrightarrow> (d = c)" 
proof (induct d)
  case 0 thus ?case by fastforce
next
  case (Suc n c)
  thus ?case
    by (cases c) (auto simp add: le_Suc_eq)
qed
 
lemma all_le_eq: "(\<forall> a::nat. (a < d) = (a < c)) = (d = c)"
using all_le_eq_imp_eq by auto

text \<open>Store11\<close>
lemma typeof_new: "typeof (new s t) = typeofNew t"
  by (cases t) (simp_all add: new_def typeofNew_def)

text \<open>Store12\<close>
lemma new_eq: "(new s1 t = new s2 t) = 
                 (\<forall> x. typeof x = typeofNew t \<longrightarrow> alive x s1 = alive x s2)"
by (cases t)
   (auto simp add: new_def typeofNew_def alive_def aliveImpl_def
                   value_class_inhabitants value_array_inhabitants all_le_eq)

lemma new_update [simp]: "new (s\<langle>l:=x\<rangle>) t = new s t"
  by (simp add: new_eq)

lemma alive_alloc_propagation: 
  assumes alive_s: "alive x s" shows  "alive x (s\<langle>t\<rangle>)"
proof (cases t)
  case new_instance with alive_s show ?thesis
    by (cases x) 
       (simp_all add: alive_def aliveImpl_def alloc_def 
                      alloc_new_instance_in_Store [THEN Abs_Store_inverse])
next
  case new_array with alive_s show ?thesis
    by (cases x) 
       (simp_all add: alive_def aliveImpl_def alloc_def 
                      alloc_new_array_in_Store [THEN Abs_Store_inverse])
qed
  
text \<open>Store7\<close> 
lemma alive_alloc_exhaust: "alive x (s\<langle>t\<rangle>) = (alive x s \<or> (x = new s t))"
proof 
  assume alive_alloc: "alive x (s\<langle>t\<rangle>)"
  show "alive x s \<or> x = new s t"
  proof (cases t)
    case (new_instance C) 
    with alive_alloc show ?thesis 
      by (cases x) (auto split: if_split_asm 
                         simp add: alive_def new_def alloc_def aliveImpl_def
                              alloc_new_instance_in_Store [THEN Abs_Store_inverse])
  next
    case (new_array T l)
    with alive_alloc show ?thesis
      by (cases x) (auto split: if_split_asm
                         simp add: alive_def new_def alloc_def aliveImpl_def
                         alloc_new_array_in_Store [THEN Abs_Store_inverse])
  qed
next
  assume "alive x s \<or> x = new s t"
  then show "alive x (s\<langle>t\<rangle>)"
  proof 
    assume "alive x s" thus ?thesis by (rule alive_alloc_propagation)
  next
    assume new: "x=new s t" show ?thesis 
    proof (cases t)
      case new_instance with new show ?thesis
        by (simp add: alive_def aliveImpl_def new_def alloc_def
                      alloc_new_instance_in_Store [THEN Abs_Store_inverse])
    next
      case new_array with new show ?thesis
        by (simp add: alive_def aliveImpl_def new_def alloc_def
                      alloc_new_array_in_Store [THEN Abs_Store_inverse])
    qed
  qed
qed

lemma alive_alloc_cases [consumes 1]: 
  "\<lbrakk>alive x (s\<langle>t\<rangle>); alive x s \<Longrightarrow> P; x=new s t \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp add: alive_alloc_exhaust)

lemma aliveImpl_vals_independent: "aliveImpl x (s\<lparr>vals := z\<rparr>) = aliveImpl x s"
  by (cases x) (simp_all add: aliveImpl_def)

lemma access_arr_len_new_alloc [simp]: 
  "s\<langle>new_array T l\<rangle>@@arr_len (new s (new_array T l)) = intgV (int l)"
  by (subst access_def) 
     (simp add: new_def alloc_def alive_def 
                alloc_new_array_in_Store [THEN Abs_Store_inverse] access_def)

lemma access_new [simp]:
  assumes ref_new: "ref l = new s t"
  assumes no_arr_len: "isNewArr t \<longrightarrow> l \<noteq> arr_len (new s t)"
  shows "s\<langle>t\<rangle>@@l = init (ltype l)"
proof -
  from ref_new 
  have "\<not> alive (ref l) s"
    by simp
  hence "s@@l = init (ltype l)"
    by simp
  moreover
  from ref_new
  have "alive (ref l) (s\<langle>t\<rangle>)"
    by simp
  moreover
  from no_arr_len
  have "vals (Rep_Store (s\<langle>t\<rangle>)) l = s@@l"
    by (cases t)
       (simp_all add: alloc_def new_def access_def
                  alloc_new_instance_in_Store [THEN Abs_Store_inverse] 
                  alloc_new_array_in_Store [THEN Abs_Store_inverse] )
  ultimately show "s\<langle>t\<rangle>@@l = init (ltype l)"
    by (subst access_def) (simp)
qed

text \<open>Store5. We have to take into account that the length of an array
is changed during allocation.\<close>
lemma access_alloc [simp]:
  assumes no_arr_len_new: "isNewArr t \<longrightarrow> l \<noteq> arr_len (new s t)"
  shows "s\<langle>t\<rangle>@@l = s@@l"
proof -
  show ?thesis
  proof (cases "alive (ref l) (s\<langle>t\<rangle>)")
    case True
    then
    have access_alloc_vals: "s\<langle>t\<rangle>@@l = vals (Rep_Store (s\<langle>t\<rangle>)) l"
      by (simp add: access_def alloc_def)
    from True show ?thesis
    proof (cases rule: alive_alloc_cases)
      assume alive_l_s: "alive (ref l) s"
      with new_unalive_old_Store
      have l_not_new: "ref l \<noteq> new s t"
        by fastforce
      hence "vals (Rep_Store (s\<langle>t\<rangle>)) l = s@@l"
        by (cases t) 
           (auto simp add: alloc_def new_def access_def 
                 alloc_new_instance_in_Store [THEN Abs_Store_inverse] 
                 alloc_new_array_in_Store [THEN Abs_Store_inverse])
      with access_alloc_vals 
      show ?thesis 
        by simp
    next
      assume ref_new: "ref l = new s t"
      with no_arr_len_new
      have "s\<langle>t\<rangle>@@l = init (ltype l)"
        by (simp add: access_new)
      moreover
      from ref_new have "s@@l = init (ltype l)"
        by simp
      ultimately
      show ?thesis by simp
    qed
  next
    case False
    hence "s\<langle>t\<rangle>@@l = init (ltype l)"
      by (simp)
    moreover
    from False have "\<not> alive (ref l) s"
      by (auto simp add: alive_alloc_propagation)
    hence "s@@l = init (ltype l)"
      by simp
    ultimately show ?thesis by simp
  qed
qed
   
text \<open>Store13\<close>
lemma Store_eqI: 
  assumes eq_alive: "\<forall> x. alive x s1 = alive x s2" 
  assumes eq_access: "\<forall> l. s1@@l = s2@@l"
  shows "s1=s2"
proof (cases "s1=s2")
  case True thus ?thesis .
next
  case False note neq_s1_s2 = this
  show ?thesis
  proof (cases "newOID (Rep_Store s1) = newOID (Rep_Store s2)")
    case False
    have "\<exists> C. newOID (Rep_Store s1) C \<noteq> newOID (Rep_Store s2) C"
    proof (rule ccontr)
      assume "\<not> (\<exists>C. newOID (Rep_Store s1) C \<noteq> newOID (Rep_Store s2) C)"
      then have "newOID (Rep_Store s1) = newOID (Rep_Store s2)"
        by (blast intro: ext)
      with False show False ..
    qed
    with eq_alive obtain C 
      where "newOID (Rep_Store s1) C \<noteq> newOID (Rep_Store s2) C"
            "\<forall> a. alive (objV C a) s1 = alive (objV C a) s2" by auto
    then show ?thesis
      by (simp add: all_le_eq alive_def aliveImpl_def)
  next
    case True note eq_newOID = this
    show ?thesis
    proof (cases "newAID (Rep_Store s1) = newAID (Rep_Store s2)")
      case False
      have "\<exists> T. newAID (Rep_Store s1) T \<noteq> newAID (Rep_Store s2) T"
      proof (rule ccontr)
        assume "\<not> (\<exists>T. newAID (Rep_Store s1) T \<noteq> newAID (Rep_Store s2) T)"
        then have "newAID (Rep_Store s1) = newAID (Rep_Store s2)"
          by (blast intro: ext)
        with False show False ..
      qed
      with eq_alive obtain T 
        where "newAID (Rep_Store s1) T \<noteq> newAID (Rep_Store s2) T"
              "\<forall> a. alive (arrV T a) s1 = alive (arrV T a) s2" by auto
      then show ?thesis
        by (simp add: all_le_eq alive_def aliveImpl_def)
    next
      case True note eq_newAID = this
      show ?thesis
      proof (cases "vals (Rep_Store s1) = vals (Rep_Store s2)")
        case True
        with eq_newOID eq_newAID 
        have "(Rep_Store s1) = (Rep_Store s2)"
          by (cases "Rep_Store s1",cases "Rep_Store s2") simp
        hence "s1=s2"
          by (simp add: Rep_Store_inject)
        with neq_s1_s2 show ?thesis
          by simp
      next
        case False
        have "\<exists> l. vals (Rep_Store s1) l \<noteq> vals (Rep_Store s2) l"
        proof (rule ccontr)
          assume "\<not> (\<exists>l. vals (Rep_Store s1) l \<noteq> vals (Rep_Store s2) l)"
          hence "vals (Rep_Store s1) = vals (Rep_Store s2)"
            by (blast intro: ext)
          with False show False ..
        qed
        then obtain l
          where "vals (Rep_Store s1) l \<noteq> vals (Rep_Store s2) l"
          by auto
        with eq_access have "False"
          by (simp add: access_def)
        thus ?thesis ..
      qed
    qed
  qed
qed

text \<open>Lemma 3.1 in [Poetzsch-Heffter97]. The proof of this lemma is quite an
impressive demostration of readable Isar proofs since it closely follows the
textual proof.\<close>
lemma comm: 
  assumes neq_l_new: "ref l \<noteq> new s t"
  assumes neq_x_new: "x \<noteq> new s t"
  shows "s\<langle>t\<rangle>\<langle>l:=x\<rangle> = s\<langle>l:=x\<rangle>\<langle>t\<rangle>"
proof (rule Store_eqI [rule_format])
  fix y
  show "alive y (s\<langle>t\<rangle>\<langle>l:=x\<rangle>) = alive y (s\<langle>l:=x\<rangle>\<langle>t\<rangle>)"                          
  proof -
    have "alive y (s\<langle>t\<rangle>\<langle>l:=x\<rangle>) = alive y (s\<langle>t\<rangle>)"
      by (rule alive_update_invariant)
    also have "\<dots> = (alive y s \<or> (y = new s t))"
      by (rule alive_alloc_exhaust)
    also have "\<dots> = (alive y (s\<langle>l:=x\<rangle>) \<or> y = new s t)"
      by (simp only: alive_update_invariant)
    also have "\<dots> = (alive y (s\<langle>l:=x\<rangle>) \<or> y = new (s\<langle>l:=x\<rangle>) t)"
    proof -
      have "new s t = new (s\<langle>l:=x\<rangle>) t"
        by simp
      thus ?thesis by simp
    qed
    also have "\<dots> = alive y (s\<langle>l:=x\<rangle>\<langle>t\<rangle>)"
      by (simp add: alive_alloc_exhaust)
    finally show ?thesis .
  qed
next
  fix k
  show "s\<langle>t\<rangle>\<langle>l := x\<rangle>@@k = s\<langle>l := x\<rangle>\<langle>t\<rangle>@@k"
  proof (cases "l=k")
    case False note neq_l_k = this
    show ?thesis
    proof (cases "isNewArr t \<longrightarrow> k \<noteq> arr_len (new s t)")
      case True
      from neq_l_k 
      have  "s\<langle>t\<rangle>\<langle>l := x\<rangle>@@k = s\<langle>t\<rangle>@@k" by simp
      also from True 
      have "\<dots> = s@@k" by simp
      also from neq_l_k 
      have "\<dots> = s\<langle>l:=x\<rangle>@@k" by simp
      also from True
      have "\<dots> = s\<langle>l := x\<rangle>\<langle>t\<rangle>@@k"  by simp
      finally show ?thesis .
    next
      case False
      then obtain T n where 
        t: "t=new_array T n" and k: "k=arr_len (new s (new_array T n))"
        by (cases t) auto
      from k have k': "k=arr_len (new (s\<langle>l := x\<rangle>) (new_array T n))"
        by simp
      from neq_l_k 
      have  "s\<langle>t\<rangle>\<langle>l := x\<rangle>@@k = s\<langle>t\<rangle>@@k" by simp
      also from t k 
      have "\<dots> = intgV (int n)"
        by simp
      also from t k'
      have "\<dots> = s\<langle>l := x\<rangle>\<langle>t\<rangle>@@k"
        by (simp del: new_update)
      finally show ?thesis .
    qed
  next
    case True note eq_l_k = this
    have lemma_3_1: 
      "ref l \<noteq> new s t \<Longrightarrow> alive (ref l) (s\<langle>t\<rangle>) = alive (ref l) s"         
      by (simp add: alive_alloc_exhaust)
    have lemma_3_2: 
      "x \<noteq> new s t \<Longrightarrow> alive x (s\<langle>t\<rangle>) = alive x s"    
      by (simp add: alive_alloc_exhaust)
    have lemma_3_3: "s\<langle>l:=x,t\<rangle>@@l = s\<langle>l:=x\<rangle>@@l"
    proof -
      from neq_l_new have "ref l \<noteq> new (s\<langle>l:=x\<rangle>) t"
        by simp
      hence "isNewArr t \<longrightarrow> l \<noteq> arr_len (new (s\<langle>l:=x\<rangle>) t)"
        by (cases t) auto
      thus ?thesis
        by (simp)
    qed
    show ?thesis
    proof (cases "alive x s")
      case True note alive_x = this
      show ?thesis
      proof (cases "alive (ref l) s")
        case True note alive_l = this
        show ?thesis
        proof (cases "typeof x \<le> ltype l")
          case True 
          with alive_l alive_x
          have "s\<langle>l:=x\<rangle>@@l = x"
            by (rule update_access_same)
          moreover
          have "s\<langle>t\<rangle>\<langle>l:=x\<rangle>@@l = x"
          proof -
            from alive_l neq_l_new have "alive (ref l) (s\<langle>t\<rangle>)"
              by (simp add: lemma_3_1)
            moreover
            from alive_x neq_x_new have "alive x (s\<langle>t\<rangle>)"
              by (simp add: lemma_3_2)
            ultimately
            show "s\<langle>t\<rangle>\<langle>l:=x\<rangle>@@l = x"
              using True by (rule update_access_same)
          qed
          ultimately show ?thesis 
            using eq_l_k lemma_3_3 by simp
        next
          case False
          thus ?thesis by simp
        qed
      next
        case False note not_alive_l = this
        from not_alive_l neq_l_new have "\<not> alive (ref l) (s\<langle>t\<rangle>)"
          by (simp add: lemma_3_1)
        then have "s\<langle>t\<rangle>\<langle>l:=x\<rangle>@@l = init (ltype l)"
          by simp
        also from not_alive_l have "\<dots> = s\<langle>l:=x\<rangle>@@l"
          by simp
        also have "\<dots> = s\<langle>l:=x\<rangle>\<langle>t\<rangle>@@l" 
          by (simp add: lemma_3_3)
        finally show ?thesis by (simp add: eq_l_k)
      qed
    next
      case False note not_alive_x = this
      from not_alive_x neq_x_new have "\<not> alive x (s\<langle>t\<rangle>)"
        by (simp add: lemma_3_2)
      then have "s\<langle>t\<rangle>\<langle>l:=x\<rangle>@@l = s\<langle>t\<rangle>@@l"
        by (simp)
      also have "\<dots> = s@@l"
      proof -
        from neq_l_new 
        have "isNewArr t \<longrightarrow> l \<noteq> arr_len (new s t)"
          by (cases t) auto
        thus ?thesis
          by (simp)
      qed
      also from not_alive_x have "\<dots> = s\<langle>l:=x\<rangle>@@l"
        by (simp)
      also have "\<dots> = s\<langle>l:=x\<rangle>\<langle>t\<rangle>@@l"
        by (simp add: lemma_3_3)
      finally show ?thesis by (simp add: eq_l_k)
    qed
  qed
qed


end 
