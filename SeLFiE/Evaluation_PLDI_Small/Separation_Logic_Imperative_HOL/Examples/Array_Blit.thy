section \<open>Bit Block Transfer and Other Array Optimizations\<close>
theory Array_Blit
imports 
  "../Sep_Main" 
  "HOL-Library.Code_Target_Numeral"
begin

subsection "Definition"

  (* TODO/FIXME: Does not work with same arrays and overlapping ranges.
    Currently, the generated code will throw an exception if the arrays are the same.

    If only used with blit_rule, separation logic guarantees that arrays will be disjoint.
  *)
  primrec blit :: "_ array \<Rightarrow> nat \<Rightarrow> _ array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
    "blit _ _ _ _ 0 = return ()"
  | "blit src si dst di (Suc l) = do {
      x \<leftarrow> Array.nth src si;
      Array.upd di x dst;
      blit src (si+1) dst (di+1) l
    }"
  
  lemma blit_rule[sep_heap_rules]:
    assumes LEN: "si+len \<le> length lsrc" "di+len \<le> length ldst"
    shows
    "< src \<mapsto>\<^sub>a lsrc 
      * dst \<mapsto>\<^sub>a ldst >
    blit src si dst di len
    <\<lambda>_. src \<mapsto>\<^sub>a lsrc 
      * dst \<mapsto>\<^sub>a (take di ldst @ take len (drop si lsrc) @ drop (di+len) ldst)
    >"
    using LEN
  proof (induction len arbitrary: si di ldst)
    case 0 thus ?case by sep_auto
  next
    case (Suc len) 
    note [sep_heap_rules] = Suc.IH

    have [simp]: "\<And>x. lsrc ! si # take len (drop (Suc si) lsrc) @ x
      = take (Suc len) (drop si lsrc) @ x"
      apply simp
      by (metis Suc.prems(1) add_Suc_right Cons_nth_drop_Suc
        less_Suc_eq_le add.commute not_less_eq take_Suc_Cons 
        Nat.trans_le_add2)

    from Suc.prems show ?case
      by (sep_auto simp: take_update_last drop_upd_irrelevant)
  qed

  definition nth_oo where "nth_oo v a i \<equiv> do {
    l\<leftarrow>Array.len a;
    if i<l then
      Array.nth a i
    else 
      return v
  }"

  definition upd_oo where "upd_oo f i x a \<equiv> do {
    l\<leftarrow>Array.len a;
    if i<l then
      Array.upd i x a
    else
      f
  }"

ML_val Array.update

subsection "Code Generator Setup"
  code_printing code_module "array_blit" \<rightharpoonup> (SML)
    \<open>
   fun array_blit src si dst di len = (
      src=dst andalso raise Fail ("array_blit: Same arrays");
      ArraySlice.copy {
        di = IntInf.toInt di,
        src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
        dst = dst})

    fun array_nth_oo v a i () = Array.sub(a,IntInf.toInt i) handle Subscript => v | Overflow => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,IntInf.toInt i,x); a) handle Subscript => f () | Overflow => f ()

\<close>

  definition blit' where
    [code del]: "blit' src si dst di len 
      = blit src (nat_of_integer si) dst (nat_of_integer di) 
          (nat_of_integer len)"

  lemma [code]:
    "blit src si dst di len 
      = blit' src (integer_of_nat si) dst (integer_of_nat di) 
          (integer_of_nat len)" by (simp add: blit'_def)

  (* TODO: Export to other languages: OCaml, Haskell *)
  code_printing constant blit' \<rightharpoonup>
    (SML) "(fn/ ()/ => /array'_blit _ _ _ _ _)"
    and (Scala) "{ ('_: Unit)/=>/
      def safecopy(src: Array['_], srci: Int, dst: Array['_], dsti: Int, len: Int) = {
        if (src eq dst)
          sys.error(\"array'_blit: Same arrays\")
        else
          System.arraycopy(src, srci, dst, dsti, len)
      }
      safecopy(_.array,_.toInt,_.array,_.toInt,_.toInt)
    }"
  
  definition [code del]: "nth_oo' v a == nth_oo v a o nat_of_integer"
  definition [code del]: "upd_oo' f == upd_oo f o nat_of_integer"

  lemma [code]: 
    "nth_oo v a == nth_oo' v a o integer_of_nat"
    "upd_oo f == upd_oo' f o integer_of_nat"
    by (simp_all add: nth_oo'_def upd_oo'_def o_def)

  text \<open>Fallbacks\<close>
  lemmas [code] = nth_oo'_def[unfolded nth_oo_def[abs_def]]
  lemmas [code] = upd_oo'_def[unfolded upd_oo_def[abs_def]]

  code_printing constant nth_oo' \<rightharpoonup> (SML) "array'_nth'_oo _ _ _"
    | constant upd_oo' \<rightharpoonup> (SML) "array'_upd'_oo _ _ _ _"

subsection \<open>Derived Functions\<close>
  definition "array_shrink a s \<equiv> do {
    \<comment> \<open>Avoiding the need for default value\<close>
    l\<leftarrow>Array.len a;
    if l=s then 
      return a
    else if l=0 then 
      Array.of_list []
    else do {
      x\<leftarrow>Array.nth a 0;
      a'\<leftarrow>Array.new s x;
      blit a 0 a' 0 s;
      return a'
    }
  }"

  lemma array_shrink_rule[sep_heap_rules]:
    assumes "s\<le>length la"
    shows "< a\<mapsto>\<^sub>ala > array_shrink a s <\<lambda>a'. a'\<mapsto>\<^sub>atake s la >\<^sub>t"
    using assms unfolding array_shrink_def
    by sep_auto

  definition "array_grow a s x \<equiv> do {
    l\<leftarrow>Array.len a;
    if l=s then 
      return a
    else do {
      a'\<leftarrow>Array.new s x;
      blit a 0 a' 0 l;
      return a'
    }
  }"

  lemma array_grow_rule[sep_heap_rules]:
    assumes "s\<ge>length la"
    shows "
      < a\<mapsto>\<^sub>ala > 
        array_grow a s x 
      <\<lambda>a'. a'\<mapsto>\<^sub>a (la @ replicate (s-length la) x)>\<^sub>t"
    using assms
    unfolding array_grow_def
    by sep_auto

      
  export_code array_grow checking SML Scala    

    
  (* TODO: Are there system-calls for array-copy? *)
  definition "array_copy a \<equiv> do {
    l\<leftarrow>Array.len a;
    if l=0 then 
      Array.of_list []
    else do {
      s \<leftarrow> Array.nth a 0;
      a'\<leftarrow>Array.new l s;
      blit a 0 a' 0 l;
      return a'
    }
  }"
  
  lemma array_copy_rule[sep_heap_rules]:
    "
      < a\<mapsto>\<^sub>al> 
        array_copy a 
      <\<lambda>a'. a\<mapsto>\<^sub>al * a'\<mapsto>\<^sub>a l>"
    unfolding array_copy_def
    by sep_auto
    
  export_code array_copy checking SML Scala    
    
    
end
