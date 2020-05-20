(*  Title:       Termination of McCarthy's 91 function
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2017
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Termination of McCarthy's 91 Function\<close>

theory McCarthy_91
imports "HOL-Library.Multiset_Order"
begin

(* TODO: move to Isabelle *)
lemma funpow_rec: "f ^^ n = (if n = 0 then id else f \<circ> f ^^ (n - 1))"
  by (induct n) auto

text \<open>
The \<open>f\<close> function captures the semantics of McCarthy's 91 function. The
\<open>g\<close> function is a tail-recursive implementation of the function, whose
termination is established using the multiset order. The definitions follow
Dershowitz and Manna.
\<close>

definition f :: "int \<Rightarrow> int" where
  "f x = (if x > 100 then x - 10 else 91)"

definition \<tau> :: "nat \<Rightarrow> int \<Rightarrow> int multiset" where
  "\<tau> n z = mset (map (\<lambda>i. (f ^^ nat i) z) [0..int n - 1])"

function g :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "g n z = (if n = 0 then z else if z > 100 then g (n - 1) (z - 10) else g (n + 1) (z + 11))"
  by pat_completeness auto
termination
proof -
  define lt :: "(int \<times> int) set" where
    "lt = {(a, b). b < a \<and> a \<le> 111}"

  have lt_trans: "trans lt"
    unfolding trans_def lt_def by simp
  have lt_irrefl: "irrefl lt"
    unfolding irrefl_def lt_def by simp

  let ?LT = "mult lt"
  let ?T = "\<lambda>(n, z). \<tau> n z"
  let ?R = "inv_image ?LT ?T"

  show ?thesis
  proof (relation ?R)
    show "wf ?R"
      by (auto simp: lt_def intro!: wf_inv_image[OF wf_mult]
        wf_subset[OF wf_measure[of "\<lambda>z. nat (111 - z)"]])
  next
    fix n :: nat and z :: int
    assume n_ne_0: "n \<noteq> 0"

    {
      assume z_gt_100: "z > 100"

      have "map (\<lambda>i. (f ^^ nat i) (z - 10)) [0..int n - 2] =
        map (\<lambda>i. (f ^^ nat i) z) [1..int n - 1]"
        using n_ne_0
      proof (induct n rule: less_induct)
        case (less n)
        note ih = this(1) and n_ne_0 = this(2)
        show ?case
        proof (cases "n = 1")
          case True
          thus ?thesis
            by simp
        next
          case False
          hence n_ge_2: "n \<ge> 2"
            using n_ne_0 by simp

          have
            split_l: "[0..int n - 2] = [0..int (n - 1) - 2] @ [int n - 2]" and
            split_r: "[1..int n - 1] = [1..int (n - 1) - 1] @ [int n - 1]"
            using n_ge_2 by (induct n) (auto simp: upto_rec2)
          have f_repeat: "(f ^^ (n - 2)) (z - 10) = (f ^^ (n - 1)) z"
            using z_gt_100 n_ge_2 by (induct n, simp) (rename_tac m; case_tac m; simp add: f_def)+

          show ?thesis
            using n_ge_2 by (auto intro!: ih simp: split_l split_r f_repeat nat_diff_distrib')
        qed
      qed
      hence image_mset_eq: "{#(f ^^ nat i) (z - 10). i \<in># mset [0..int n - 2]#} =
        {#(f ^^ nat i) z. i \<in># mset [1..int n - 1]#}"
        by (fold mset_map) (intro arg_cong[of _ _ mset])

      have mset_eq_add_0_mset: "mset [0..int n - 1] = add_mset 0 (mset [1..int n - 1])"
        using n_ne_0 by (induct n) (auto simp: upto.simps)

      have nm1m1: "int (n - 1) - 1 = int n - 2"
        using n_ne_0 by simp

      show "((n - 1, z - 10), (n, z)) \<in> ?R"
        by (auto simp: image_mset_eq mset_eq_add_0_mset nm1m1 \<tau>_def simp del: One_nat_def
          intro: subset_implies_mult image_mset_subset_mono)
    }
    {
      assume z_le_100: "\<not> z > 100"

      have map_eq: "map (\<lambda>x. (f ^^ nat x) (z + 11)) [2..int n] =
        map (\<lambda>i. (f ^^ nat i) z) [1..int n - 1]"
        using n_ne_0
      proof (induct n rule: less_induct)
        case (less n)
        note ih = this(1) and n_ne_0 = this(2)
        show ?case
        proof (cases "n = 1")
          case True
          thus ?thesis
            by simp
        next
          case False
          hence n_ge_2: "n \<ge> 2"
            using n_ne_0 by simp

          have
            split_l: "[2..int n] = [2..int (n - 1)] @ [int n]" and
            split_r: "[1..int n - 1] = [1..int (n - 1) - 1] @ [int n - 1]"
            using n_ge_2 by (induct n) (auto simp: upto_rec2)
          from z_le_100 have f_f_z_11: "f (f (z + 11)) = f z"
            by (simp add: f_def)
          moreover define m where "m = n - 2"
          with n_ge_2 have "n = m + 2"
            by simp
          ultimately have f_repeat: "(f ^^ n) (z + 11) = (f ^^ (n - 1)) z"
            by (simp add: funpow_Suc_right del: funpow.simps)
          with n_ge_2 show ?thesis
            by (auto intro: ih [of "nat (int n - 1)"]
              simp: less.hyps split_l split_r nat_add_distrib nat_diff_distrib)
        qed
      qed

      have "[0..int n] = [0..1] @ [2..int n]"
        using n_ne_0 by (simp add: upto_rec1)
      hence "{#(f ^^ nat x) (z + 11). x \<in># mset [0..int n]#} =
        {#(f ^^ nat x) (z + 11). x \<in># mset [0..1]#}
        + {#(f ^^ nat x) (z + 11). x \<in># mset [2..int n]#}"
        by auto
      hence factor_out_first_two: "{#(f ^^ nat x) (z + 11). x \<in># mset [0..int n]#} =
        {#z + 11, f (z + 11)#} + {#(f ^^ nat x) (z + 11). x \<in># mset [2..int n]#}"
        by (auto simp: upto_rec1)

      let ?etc1 = "{#(f ^^ nat i) (z + 11). i \<in># mset [2..int n]#}"
      let ?etc2 = "{#(f ^^ nat i) z. i \<in># mset [1..int n - 1]#}"

      show "((n + 1, z + 11), (n, z)) \<in> ?R"
      proof (cases "z \<ge> 90")
        case z_ge_90: True

        have "{#z + 11, f (z + 11)#} + ?etc1 = {#z + 11, z + 1#} + ?etc2"
          using z_ge_90
          by (auto intro!: arg_cong2[of _ _ _ _ add_mset] simp: map_eq f_def mset_map[symmetric]
            simp del: mset_map)
        hence image_mset_eq: "{#(f ^^ nat x) (z + 11). x \<in># mset [0..int n]#} =
          {#z + 11, z + 1#} + ?etc2"
          using factor_out_first_two by presburger

        have "({#z + 11, z + 1#}, {#z#}) \<in> mult1 lt"
          using z_le_100 z_ge_90 by (auto intro!: mult1I simp: lt_def)
        hence "({#z + 11, z + 1#}, {#z#}) \<in> mult lt"
          unfolding mult_def by simp
        hence "({#z + 11, z + 1#} + ?etc2, {#z#} + ?etc2) \<in> mult lt"
          by (rule mult_cancel[THEN iffD2, OF lt_trans lt_irrefl])
        thus ?thesis
          using n_ne_0 by (auto simp: image_mset_eq \<tau>_def upto_rec1[of 0 "int n - 1"])
      next
        case z_lt_90: False

        have "{#z + 11, f (z + 11)#} + ?etc1 = {#z + 11, 91#} + ?etc2"
          using z_lt_90
          by (auto intro!: arg_cong2[of _ _ _ _ add_mset] simp: map_eq f_def mset_map[symmetric]
            simp del: mset_map)
        hence image_mset_eq: "{#(f ^^ nat x) (z + 11). x \<in># mset [0..int n]#} =
          {#z + 11, 91#} + ?etc2"
          using factor_out_first_two by presburger

        have "({#z + 11, 91#}, {#z#}) \<in> mult1 lt"
          using z_le_100 z_lt_90 by (auto intro!: mult1I simp: lt_def)
        hence "({#z + 11, 91#}, {#z#}) \<in> mult lt"
          unfolding mult_def by simp
        hence "({#z + 11, 91#} + ?etc2, {#z#} + ?etc2) \<in> mult lt"
          by (rule mult_cancel[THEN iffD2, OF lt_trans lt_irrefl])
        thus ?thesis
          using n_ne_0 by (auto simp: image_mset_eq \<tau>_def upto_rec1[of 0 "int n - 1"])
      qed
    }
  qed
qed

declare g.simps [simp del]

end
