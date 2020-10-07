(*
  File: Rect_Intersect.thy
  Author: Bohua Zhan
*)

section \<open>Rectangle intersection\<close>

theory Rect_Intersect
  imports Interval_Tree
begin

text \<open>
  Functional version of algorithm for detecting rectangle intersection.
  See \cite[Exercise 14.3-7]{cormen2009introduction} for a reference.
\<close>

subsection \<open>Definition of rectangles\<close>

datatype 'a rectangle = Rectangle (xint: "'a interval") (yint: "'a interval")
setup \<open>add_simple_datatype "rectangle"\<close>

definition is_rect :: "('a::linorder) rectangle \<Rightarrow> bool" where [rewrite]:
  "is_rect rect \<longleftrightarrow> is_interval (xint rect) \<and> is_interval (yint rect)"

definition is_rect_list :: "('a::linorder) rectangle list \<Rightarrow> bool" where [rewrite]:
  "is_rect_list rects \<longleftrightarrow> (\<forall>i<length rects. is_rect (rects ! i))"

lemma is_rect_listD: "is_rect_list rects \<Longrightarrow> i < length rects \<Longrightarrow> is_rect (rects ! i)" by auto2
setup \<open>add_forward_prfstep_cond @{thm is_rect_listD} [with_term "?rects ! ?i"]\<close>

setup \<open>del_prfstep_thm_eqforward @{thm is_rect_list_def}\<close>

definition is_rect_overlap :: "('a::linorder) rectangle \<Rightarrow> ('a::linorder) rectangle \<Rightarrow> bool" where [rewrite]:
  "is_rect_overlap A B \<longleftrightarrow> (is_overlap (xint A) (xint B) \<and> is_overlap (yint A) (yint B))"

definition has_rect_overlap :: "('a::linorder) rectangle list \<Rightarrow> bool" where [rewrite]:
  "has_rect_overlap As \<longleftrightarrow> (\<exists>i<length As. \<exists>j<length As. i \<noteq> j \<and> is_rect_overlap (As ! i) (As ! j))"

subsection \<open>INS / DEL operations\<close>

datatype 'a operation =
  INS (pos: 'a) (op_idx: nat) (op_int: "'a interval")
| DEL (pos: 'a) (op_idx: nat) (op_int: "'a interval")
setup \<open>fold add_rewrite_rule_back @{thms operation.collapse}\<close>
setup \<open>fold add_rewrite_rule @{thms operation.sel}\<close>
setup \<open>fold add_rewrite_rule @{thms operation.case}\<close>
setup \<open>add_resolve_prfstep @{thm operation.distinct(1)}\<close>
setup \<open>add_forward_prfstep_cond @{thm operation.disc(1)} [with_term "INS ?x11.0 ?x12.0 ?x13.0"]\<close>
setup \<open>add_forward_prfstep_cond @{thm operation.disc(2)} [with_term "DEL ?x21.0 ?x22.0 ?x23.0"]\<close>

instantiation operation :: (linorder) linorder begin

definition less: "(a < b) = (if pos a \<noteq> pos b then pos a < pos b else
                             if is_INS a \<noteq> is_INS b then is_INS a \<and> \<not>is_INS b
                             else if op_idx a \<noteq> op_idx b then op_idx a < op_idx b else op_int a < op_int b)"
definition less_eq: "(a \<le> b) = (if pos a \<noteq> pos b then pos a < pos b else
                              if is_INS a \<noteq> is_INS b then is_INS a \<and> \<not>is_INS b
                              else if op_idx a \<noteq> op_idx b then op_idx a < op_idx b else op_int a \<le> op_int b)"

instance proof
  fix x y z :: "'a operation"
  show a: "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (smt Rect_Intersect.less Rect_Intersect.less_eq leD le_cases3 not_less_iff_gr_or_eq)
  show b: "x \<le> x"
    by (simp add: local.less_eq)
  show c: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (smt Rect_Intersect.less Rect_Intersect.less_eq a dual_order.trans less_trans)
  show d: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (metis Rect_Intersect.less Rect_Intersect.less_eq a le_imp_less_or_eq operation.expand)
  show e: "x \<le> y \<or> y \<le> x"
    using local.less_eq by fastforce
qed end

setup \<open>fold add_rewrite_rule [@{thm less_eq}, @{thm less}]\<close>

lemma operation_leD [forward]:
  "(a::('a::linorder operation)) \<le> b \<Longrightarrow> pos a \<le> pos b" by auto2

lemma operation_lessI [backward]:
  "p1 \<le> p2 \<Longrightarrow> INS p1 n1 i1 < DEL p2 n2 i2"
@proof
  @have "is_INS (INS p1 n1 i1) = True"
  @have "is_INS (DEL p2 n2 i2) = False"
@qed

setup \<open>fold del_prfstep_thm [@{thm less_eq}, @{thm less}]\<close>

subsection \<open>Set of operations corresponding to a list of rectangles\<close>

fun ins_op :: "'a rectangle list \<Rightarrow> nat \<Rightarrow> ('a::linorder) operation" where
  "ins_op rects i = INS (low (yint (rects ! i))) i (xint (rects ! i))"
setup \<open>add_rewrite_rule @{thm ins_op.simps}\<close>

fun del_op :: "'a rectangle list \<Rightarrow> nat \<Rightarrow> ('a::linorder) operation" where
  "del_op rects i = DEL (high (yint (rects ! i))) i (xint (rects ! i))"
setup \<open>add_rewrite_rule @{thm del_op.simps}\<close>

definition ins_ops :: "'a rectangle list \<Rightarrow> ('a::linorder) operation list" where [rewrite]:
  "ins_ops rects = list (\<lambda>i. ins_op rects i) (length rects)"

definition del_ops :: "'a rectangle list \<Rightarrow> ('a::linorder) operation list" where [rewrite]:
  "del_ops rects = list (\<lambda>i. del_op rects i) (length rects)"

lemma ins_ops_distinct [forward]: "distinct (ins_ops rects)"
@proof
  @let "xs = ins_ops rects"
  @have "\<forall>i<length xs. \<forall>j<length xs. i \<noteq> j \<longrightarrow> xs ! i \<noteq> xs ! j"
@qed

lemma del_ops_distinct [forward]: "distinct (del_ops rects)"
@proof
  @let "xs = del_ops rects"
  @have "\<forall>i<length xs. \<forall>j<length xs. i \<noteq> j \<longrightarrow> xs ! i \<noteq> xs ! j"
@qed

lemma set_ins_ops [rewrite]:
  "oper \<in> set (ins_ops rects) \<longleftrightarrow> op_idx oper < length rects \<and> oper = ins_op rects (op_idx oper)"
@proof
  @case "oper \<in> set (ins_ops rects)" @with
    @obtain i where "i < length rects" "ins_ops rects ! i = oper" @end
  @case "op_idx oper < length rects \<and> oper = ins_op rects (op_idx oper)" @with
    @have "oper = (ins_ops rects) ! (op_idx oper)" @end
@qed

lemma set_del_ops [rewrite]:
  "oper \<in> set (del_ops rects) \<longleftrightarrow> op_idx oper < length rects \<and> oper = del_op rects (op_idx oper)"
@proof
  @case "oper \<in> set (del_ops rects)" @with
    @obtain i where "i < length rects" "del_ops rects ! i = oper" @end
  @case "op_idx oper < length rects \<and> oper = del_op rects (op_idx oper)" @with
    @have "oper = (del_ops rects) ! (op_idx oper)" @end
@qed

definition all_ops :: "'a rectangle list \<Rightarrow> ('a::linorder) operation list" where [rewrite]:
  "all_ops rects = sort (ins_ops rects @ del_ops rects)"

lemma all_ops_distinct [forward]: "distinct (all_ops rects)"
@proof @have "distinct (ins_ops rects @ del_ops rects)" @qed

lemma set_all_ops_idx [forward]:
  "oper \<in> set (all_ops rects) \<Longrightarrow> op_idx oper < length rects" by auto2

lemma set_all_ops_ins [forward]:
  "INS p n i \<in> set (all_ops rects) \<Longrightarrow> INS p n i = ins_op rects n" by auto2

lemma set_all_ops_del [forward]:
  "DEL p n i \<in> set (all_ops rects) \<Longrightarrow> DEL p n i = del_op rects n" by auto2

lemma ins_in_set_all_ops:
  "i < length rects \<Longrightarrow> ins_op rects i \<in> set (all_ops rects)" by auto2
setup \<open>add_forward_prfstep_cond @{thm ins_in_set_all_ops} [with_term "ins_op ?rects ?i"]\<close>

lemma del_in_set_all_ops:
  "i < length rects \<Longrightarrow> del_op rects i \<in> set (all_ops rects)" by auto2
setup \<open>add_forward_prfstep_cond @{thm del_in_set_all_ops} [with_term "del_op ?rects ?i"]\<close>

lemma all_ops_sorted [forward]: "sorted (all_ops rects)" by auto2

lemma all_ops_nonempty [backward]: "rects \<noteq> [] \<Longrightarrow> all_ops rects \<noteq> []"
@proof @have "length (all_ops rects) > 0" @qed

setup \<open>del_prfstep_thm @{thm all_ops_def}\<close>

subsection \<open>Applying a set of operations\<close>

definition apply_ops_k :: "('a::linorder) rectangle list \<Rightarrow> nat \<Rightarrow> nat set" where [rewrite]:
  "apply_ops_k rects k = (let ops = all_ops rects in
     {i. i < length rects \<and> (\<exists>j<k. ins_op rects i = ops ! j) \<and> \<not>(\<exists>j<k. del_op rects i = ops ! j)})"
setup \<open>register_wellform_data ("apply_ops_k rects k", ["k < length (all_ops rects)"])\<close>

lemma apply_ops_set_mem [rewrite]:
  "ops = all_ops rects \<Longrightarrow>
   i \<in> apply_ops_k rects k \<longleftrightarrow> (i < length rects \<and> (\<exists>j<k. ins_op rects i = ops ! j) \<and> \<not>(\<exists>j<k. del_op rects i = ops ! j))"
  by auto2
setup \<open>del_prfstep_thm @{thm apply_ops_k_def}\<close>

definition xints_of :: "'a rectangle list \<Rightarrow> nat set \<Rightarrow> (('a::linorder) idx_interval) set" where [rewrite]:
  "xints_of rect is = (\<lambda>i. IdxInterval (xint (rect ! i)) i) ` is"

lemma xints_of_mem [rewrite]:
  "IdxInterval it i \<in> xints_of rect is \<longleftrightarrow> (i \<in> is \<and> xint (rect ! i) = it)" using xints_of_def by auto

lemma xints_diff [rewrite]:
  "xints_of rects (A - B) = xints_of rects A - xints_of rects B"
@proof @have "inj (\<lambda>i. IdxInterval (xint (rects ! i)) i)" @qed

definition has_overlap_at_k :: "('a::linorder) rectangle list \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "has_overlap_at_k rects k \<longleftrightarrow> (
    let S = apply_ops_k rects k; ops = all_ops rects in
      is_INS (ops ! k) \<and> has_overlap (xints_of rects S) (op_int (ops ! k)))"
setup \<open>register_wellform_data ("has_overlap_at_k rects k", ["k < length (all_ops rects)"])\<close>

lemma has_overlap_at_k_equiv [forward]:
  "is_rect_list rects \<Longrightarrow> ops = all_ops rects \<Longrightarrow> k < length ops \<Longrightarrow>
   has_overlap_at_k rects k \<Longrightarrow> has_rect_overlap rects"
@proof
  @let "S = apply_ops_k rects k"
  @have "has_overlap (xints_of rects S) (op_int (ops ! k))"
  @obtain "xs' \<in> xints_of rects S" where "is_overlap (int xs') (op_int (ops ! k))"
  @let "xs = int xs'" "i = idx xs'"
  @let "j = op_idx (ops ! k)"
  @have "ops ! k = ins_op rects j"
  @have "i \<noteq> j" @with @contradiction
    @obtain k' where "k' < k" "ops ! k' = ins_op rects i"
    @have "ops ! k = ops ! k'"
  @end
  @have "low (yint (rects ! i)) \<le> pos (ops ! k)" @with
    @obtain k' where "k' < k" "ops ! k' = ins_op rects i"
    @have "ops ! k' \<le> ops ! k"
  @end
  @have "high (yint (rects ! i)) \<ge> pos (ops ! k)" @with
    @obtain k' where "k' < length ops" "ops ! k' = del_op rects i"
    @have "ops ! k' \<ge> ops ! k"
  @end
  @have "is_rect_overlap (rects ! i) (rects ! j)"
@qed

lemma has_overlap_at_k_equiv2 [resolve]:
  "is_rect_list rects \<Longrightarrow> ops = all_ops rects \<Longrightarrow> has_rect_overlap rects \<Longrightarrow>
   \<exists>k<length ops. has_overlap_at_k rects k"
@proof
  @obtain i j where "i < length rects" "j < length rects" "i \<noteq> j"
                    "is_rect_overlap (rects ! i) (rects ! j)"
  @have "is_rect_overlap (rects ! j) (rects ! i)"
  @obtain i1 where "i1 < length ops" "ops ! i1 = ins_op rects i"
  @obtain j1 where "j1 < length ops" "ops ! j1 = ins_op rects j"
  @obtain i2 where "i2 < length ops" "ops ! i2 = del_op rects i"
  @obtain j2 where "j2 < length ops" "ops ! j2 = del_op rects j"
  @case "ins_op rects i < ins_op rects j" @with
    @have "i1 < j1"
    @have "j1 < i2" @with @have "ops ! j1 < ops ! i2" @end
    @have "is_overlap (int (IdxInterval (xint (rects ! i)) i)) (xint (rects ! j))"
    @have "has_overlap_at_k rects j1"
  @end
  @case "ins_op rects j < ins_op rects i" @with
    @have "j1 < i1"
    @have "i1 < j2" @with @have "ops ! i1 < ops ! j2" @end
    @have "is_overlap (int (IdxInterval (xint (rects ! j)) j)) (xint (rects ! i))"
    @have "has_overlap_at_k rects i1"
  @end
@qed

definition has_overlap_lst :: "('a::linorder) rectangle list \<Rightarrow> bool" where [rewrite]:
  "has_overlap_lst rects = (let ops = all_ops rects in (\<exists>k<length ops. has_overlap_at_k rects k))"

lemma has_overlap_equiv [rewrite]:
  "is_rect_list rects \<Longrightarrow> has_overlap_lst rects \<longleftrightarrow> has_rect_overlap rects" by auto2

subsection \<open>Implementation of apply\_ops\_k\<close>

lemma apply_ops_k_next1 [rewrite]:
  "is_rect_list rects \<Longrightarrow> ops = all_ops rects \<Longrightarrow> n < length ops \<Longrightarrow> is_INS (ops ! n) \<Longrightarrow>
   apply_ops_k rects (n + 1) = apply_ops_k rects n \<union> {op_idx (ops ! n)}"
@proof
  @have "\<forall>i. i\<in>apply_ops_k rects (n + 1) \<longleftrightarrow> i\<in>apply_ops_k rects n \<union> {op_idx (ops ! n)}" @with
    @case "i \<in> apply_ops_k rects n \<union> {op_idx (ops ! n)}" @with
      @case "i = op_idx (ops ! n)" @with
        @have "ins_op rects i < del_op rects i"
      @end
    @end
  @end
@qed

lemma apply_ops_k_next2 [rewrite]:
  "is_rect_list rects \<Longrightarrow> ops = all_ops rects \<Longrightarrow> n < length ops \<Longrightarrow> \<not>is_INS (ops ! n) \<Longrightarrow>
   apply_ops_k rects (n + 1) = apply_ops_k rects n - {op_idx (ops ! n)}" by auto2

definition apply_ops_k_next :: "('a::linorder) rectangle list \<Rightarrow> 'a idx_interval set \<Rightarrow> nat \<Rightarrow> 'a idx_interval set" where
  "apply_ops_k_next rects S k = (let ops = all_ops rects in
   (case ops ! k of
      INS p n i \<Rightarrow> S \<union> {IdxInterval i n}
    | DEL p n i \<Rightarrow> S - {IdxInterval i n}))"
setup \<open>add_rewrite_rule @{thm apply_ops_k_next_def}\<close>

lemma apply_ops_k_next_is_correct [rewrite]:
  "is_rect_list rects \<Longrightarrow> ops = all_ops rects \<Longrightarrow> n < length ops \<Longrightarrow>
   S = xints_of rects (apply_ops_k rects n) \<Longrightarrow>
   xints_of rects (apply_ops_k rects (n + 1)) = apply_ops_k_next rects S n"
@proof @case "is_INS (ops ! n)" @qed

function rect_inter :: "nat rectangle list \<Rightarrow> nat idx_interval set \<Rightarrow> nat \<Rightarrow> bool" where
  "rect_inter rects S k = (let ops = all_ops rects in
    if k \<ge> length ops then False
    else if is_INS (ops ! k) then
      if has_overlap S (op_int (ops ! k)) then True
      else if k = length ops - 1 then False
      else rect_inter rects (apply_ops_k_next rects S k) (k + 1)
    else if k = length ops - 1 then False
      else rect_inter rects (apply_ops_k_next rects S k) (k + 1))"
  by auto
  termination by (relation "measure (\<lambda>(rects,S,k). length (all_ops rects) - k)") auto

lemma rect_inter_correct_ind [rewrite]:
  "is_rect_list rects \<Longrightarrow> ops = all_ops rects \<Longrightarrow> n < length ops \<Longrightarrow>
   rect_inter rects (xints_of rects (apply_ops_k rects n)) n \<longleftrightarrow>
   (\<exists>k<length ops. k \<ge> n \<and> has_overlap_at_k rects k)"
@proof
  @let "ints = xints_of rects (apply_ops_k rects n)"
  @fun_induct "rect_inter rects ints n"
  @unfold "rect_inter rects ints n"
  @case "n \<ge> length ops"
  @case "is_INS (ops ! n) \<and> has_overlap ints (op_int (ops ! n))"
  @case "n = length ops - 1"
@qed

text \<open>Correctness of functional algorithm.\<close>
theorem rect_inter_correct [rewrite]:
  "is_rect_list rects \<Longrightarrow> rect_inter rects {} 0 \<longleftrightarrow> has_rect_overlap rects"
@proof
  @have "{} = xints_of rects (apply_ops_k rects 0)"
  @have "rect_inter rects {} 0 = has_overlap_lst rects" @with
    @unfold "rect_inter rects {} 0"
  @end
@qed

end
