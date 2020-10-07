section \<open>Lazy Lists\<close>

theory LazyList
imports HOLCF "HOLCF-Library.Int_Discrete"
begin

domain 'a LList = LNil | LCons (lazy 'a) (lazy "'a LList")
 
fixrec
  mapL :: "('a \<rightarrow> 'b) \<rightarrow> 'a LList \<rightarrow> 'b LList"
where
  "mapL\<cdot>f\<cdot>LNil = LNil"
| "mapL\<cdot>f\<cdot>(LCons\<cdot>x\<cdot>xs) = LCons\<cdot>(f\<cdot>x)\<cdot>(mapL\<cdot>f\<cdot>xs)"

lemma mapL_strict [simp]: "mapL\<cdot>f\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

fixrec
  filterL :: "('a \<rightarrow> tr) \<rightarrow> 'a LList \<rightarrow> 'a LList"
where
  "filterL\<cdot>p\<cdot>LNil = LNil"
| "filterL\<cdot>p\<cdot>(LCons\<cdot>x\<cdot>xs) =
    (If p\<cdot>x then LCons\<cdot>x\<cdot>(filterL\<cdot>p\<cdot>xs) else filterL\<cdot>p\<cdot>xs)"

lemma filterL_strict [simp]: "filterL\<cdot>p\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

fixrec
  foldrL :: "('a \<rightarrow> 'b \<rightarrow> 'b) \<rightarrow> 'b \<rightarrow> 'a LList \<rightarrow> 'b"
where
  "foldrL\<cdot>f\<cdot>z\<cdot>LNil = z"
| "foldrL\<cdot>f\<cdot>z\<cdot>(LCons\<cdot>x\<cdot>xs) = f\<cdot>x\<cdot>(foldrL\<cdot>f\<cdot>z\<cdot>xs)"

lemma foldrL_strict [simp]: "foldrL\<cdot>f\<cdot>z\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

fixrec
  enumFromToL :: "int\<^sub>\<bottom> \<rightarrow> int\<^sub>\<bottom> \<rightarrow> (int\<^sub>\<bottom>) LList"
where
  "enumFromToL\<cdot>(up\<cdot>x)\<cdot>(up\<cdot>y) =
    (if x \<le> y then LCons\<cdot>(up\<cdot>x)\<cdot>(enumFromToL\<cdot>(up\<cdot>(x+1))\<cdot>(up\<cdot>y)) else LNil)"

lemma enumFromToL_simps' [simp]:
  "x \<le> y \<Longrightarrow>
    enumFromToL\<cdot>(up\<cdot>x)\<cdot>(up\<cdot>y) = LCons\<cdot>(up\<cdot>x)\<cdot>(enumFromToL\<cdot>(up\<cdot>(x+1))\<cdot>(up\<cdot>y))"
  "\<not> x \<le> y \<Longrightarrow> enumFromToL\<cdot>(up\<cdot>x)\<cdot>(up\<cdot>y) = LNil"
  by simp_all

declare enumFromToL.simps [simp del]

lemma enumFromToL_strict [simp]:
  "enumFromToL\<cdot>\<bottom>\<cdot>y = \<bottom>"
  "enumFromToL\<cdot>x\<cdot>\<bottom> = \<bottom>"
apply (subst enumFromToL.unfold, simp)
apply (induct x)
apply (subst enumFromToL.unfold, simp)+
done

fixrec
  appendL :: "'a LList \<rightarrow> 'a LList \<rightarrow> 'a LList"
where
  "appendL\<cdot>LNil\<cdot>ys = ys"
| "appendL\<cdot>(LCons\<cdot>x\<cdot>xs)\<cdot>ys = LCons\<cdot>x\<cdot>(appendL\<cdot>xs\<cdot>ys)"

lemma appendL_strict [simp]: "appendL\<cdot>\<bottom>\<cdot>ys = \<bottom>"
by fixrec_simp

lemma appendL_LNil_right: "appendL\<cdot>xs\<cdot>LNil = xs"
by (induct xs) simp_all

fixrec
  zipWithL :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> 'a LList \<rightarrow> 'b LList \<rightarrow> 'c LList"
where
  "zipWithL\<cdot>f\<cdot>LNil\<cdot>ys = LNil"
| "zipWithL\<cdot>f\<cdot>(LCons\<cdot>x\<cdot>xs)\<cdot>LNil = LNil"
| "zipWithL\<cdot>f\<cdot>(LCons\<cdot>x\<cdot>xs)\<cdot>(LCons\<cdot>y\<cdot>ys) = LCons\<cdot>(f\<cdot>x\<cdot>y)\<cdot>(zipWithL\<cdot>f\<cdot>xs\<cdot>ys)"

lemma zipWithL_strict [simp]:
  "zipWithL\<cdot>f\<cdot>\<bottom>\<cdot>ys = \<bottom>"
  "zipWithL\<cdot>f\<cdot>(LCons\<cdot>x\<cdot>xs)\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

fixrec
  concatMapL :: "('a \<rightarrow> 'b LList) \<rightarrow> 'a LList \<rightarrow> 'b LList"
where
  "concatMapL\<cdot>f\<cdot>LNil = LNil"
| "concatMapL\<cdot>f\<cdot>(LCons\<cdot>x\<cdot>xs) = appendL\<cdot>(f\<cdot>x)\<cdot>(concatMapL\<cdot>f\<cdot>xs)"

lemma concatMapL_strict [simp]: "concatMapL\<cdot>f\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

end
