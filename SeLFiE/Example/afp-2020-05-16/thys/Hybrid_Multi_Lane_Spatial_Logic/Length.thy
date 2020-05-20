(*  Title:      Length.thy
    Author:     Sven Linker

The length of cars visible to the owner of a given view.
*)

section\<open>Visible Length of Cars with Perfect Sensors\<close>
text\<open>
Given a sensor function, we can define the length
of a car \(c\) as perceived by the owner of a view \(v\). This
length is restricted by the size of the extension of the view \(v\),
but always given by a continuous interval, which may possibly
be degenerate (i.e., a point-interval).

The lemmas connect the end-points of the perceived length
with the end-points of the current view. Furthermore, they
show how the chopping and subview relations affect
the perceived length of a car.  
\<close>

theory Length
  imports  Sensors
begin

context sensors
begin


definition len:: "view \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real_int"
  where len_def :"len v ( ts ) c ==
    if (left (space ts v c) > right (ext v))  
      then  Abs_real_int (right (ext v),right (ext v)) 
    else
      if (right (space ts v c) < left (ext v)) 
        then Abs_real_int (left (ext v),left (ext v))
      else  
        Abs_real_int (max (left (ext v)) (left (space ts v c)), 
                      min (right (ext v)) (right (space ts v c)))"

lemma len_left: " left ((len v  ts) c) \<ge> left (ext v)" 
    using Abs_real_int_inverse left_leq_right sensors.len_def sensors_axioms by auto

lemma len_right: " right ((len v  ts) c) \<le> right (ext v)" 
  using Abs_real_int_inverse left_leq_right sensors.len_def sensors_axioms by auto

lemma len_sub_int:"len v ts c \<le> ext v" 
  using less_eq_real_int_def len_left len_right by blast

lemma len_space_left: 
  "left (space ts v c) \<le> right (ext v) \<longrightarrow> left (len v ts c) \<ge> left (space ts v c)" 
proof
  assume assm:"left (space ts v c) \<le> right (ext v)"
  then show "left (len v ts c) \<ge> left (space ts v c)" 
  proof (cases "right ((space ts v) c) < left (ext v)" )
    case True
    then show ?thesis using len_def len_left real_int.left_leq_right 
      by (meson le_less_trans not_less order.asym)
  next
    case False
    then have "len v ts c = 
    Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), 
                   min (right (ext v)) (right ((space ts v) c)))"
      using len_def assm by auto
    then have "left (len v ts c) = max (left (ext v)) (left ((space ts v) c))" 
      using Abs_real_int_inverse False assm real_int.left_leq_right 
      by auto
    then show ?thesis  by linarith
  qed
qed    

lemma len_space_right: 
  "right (space ts v c) \<ge> left (ext v) \<longrightarrow> right (len v ts c) \<le> right (space ts v c)" 
proof
  assume assm:"right (space ts v c) \<ge> left (ext v)"
  then show "right (len v ts c) \<le> right (space ts v c)" 
  proof (cases "left ((space ts v) c) > right (ext v)" )
    case True
    then show ?thesis using len_def len_right real_int.left_leq_right 
      by (meson le_less_trans not_less order.asym)
  next
    case False
    then have "len v ts c = 
      Abs_real_int (max (left (ext v)) (left ((space ts v) c)), 
                     min (right (ext v)) (right ((space ts v) c)))"
      using len_def assm by auto
    then have "right (len v ts c) = min (right (ext v)) (right ((space ts v) c))" 
      using Abs_real_int_inverse False assm real_int.left_leq_right
      by auto
    then show ?thesis  by linarith
  qed
qed    


lemma len_hchop_left_right_border: 
  "(len v ts c = ext v) \<and> (v=v1\<parallel>v2) \<longrightarrow> (right (len v1 ts c) = right (ext v1))"
proof
  assume assm:"((len v ts) c = ext v) \<and> (v=v1\<parallel>v2)"
  have l1:"left ((len v ts) c) = left (ext v)" using assm by auto 
  from assm have l2:"left (ext v) = left (ext v1)" 
    by (simp add: hchop_def real_int.rchop_def)
  from l1 and l2 have l3:"left ((len v ts) c) = left (ext v1)" by simp  
  have r1:"right ((len v ts) c) = right (ext v)" using assm by auto
  have r2:"right (ext v1) \<le> right (ext v)" 
    by (metis (no_types, lifting) assm hchop_def real_int.rchop_def 
        real_int.left_leq_right )  
  have r3:"right ((len v1 ts) c) \<le> right (ext v1)" 
    using len_right by blast
  show "right ((len v1 ts) c) = right (ext v1)" 
  proof (rule ccontr)
    assume contra:"right ((len v1 ts) c) \<noteq> right (ext v1)"
    with r3 have less:"right ((len v1 ts) c) < right (ext v1)" by simp
    show False
    proof (cases "left ((space ts v) c) \<le> right (ext v1)")
      assume neg1:"\<not> left ((space ts v) c) \<le> right (ext v1)" 
      have "right ((len v1 ts) c) = right (ext v1)" 
        using Abs_real_int_inverse left_space len_def neg1 right.rep_eq by auto
      with contra show False ..
    next
      assume less1:"left ((space ts v) c) \<le> right (ext v1)"
      show False
      proof (cases "right ((space ts v) c) \<ge> left (ext v1)")
        assume neg2:"\<not> left (ext v1) \<le> right ((space ts v) c)"
        have "right ((len v1 ts) c) = right (ext v1)" 
        proof -
          have "(len v1 ts) c = Abs_real_int (left (ext v1),left (ext v1))"
            using len_def  neg2 assm hchop_def real_int.left_leq_right less1 space_def
            by auto 
          hence  "right ((len v1 ts) c) = left ((len v1 ts )c)" 
            using l3 assm contra less1 len_def neg2 r2 r3  real_int.left_leq_right
            by auto
          with l1 have r4:"right((len v1 ts)c ) = right (ext v)" 
            using assm l2 len_def neg2 assm hchop_def less1 real_int.left_leq_right r2
              space_def
            by auto
          hence "right (ext v) = right (ext v1)" 
            using r2 r3 by auto
          thus "right ((len v1 ts) c) = right (ext v1)" 
            using r4 by auto
        qed
        with contra  show False ..
      next
        assume less2:"left (ext v1) \<le> right ((space ts v) c)"
        have len_in_type:
          "(max (left (ext v1)) (left ((space ts v) c)), 
            min (right (ext v1)) (right ((space ts v) c))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
          using Rep_real_int less1 less2 by auto
        from less1 and less2 have len_def_v1:"len v1 (ts) c = 
                Abs_real_int ((max (left (ext v1)) (left ((space ts v) c))), 
                              min (right (ext v1)) (right ((space ts v) c)))" 
          using len_def assm hchop_def  space_def  by auto
        with less have 
          "min (right (ext v1)) (right ((space ts v) c)) = right ((space ts v) c)"
          using Abs_real_int_inverse len_in_type snd_conv by auto
        hence "right ((space ts v) c) \<le> right (ext v1)" by simp
        hence "right ((space ts v) c) \<le> right (ext v)" 
          using r2 by linarith
        from len_def_v1 and less and len_in_type
        have "right ((space ts v) c) < right (ext v1)" 
          using Abs_real_int_inverse sndI by auto
        hence r4:"right ((space ts v) c) < right (ext v)" 
          using r2 by linarith
        from assm have len_v_in_type:
          "(max (left (ext v)) (left ((space ts v) c)), 
            min (right (ext v)) (right ((space ts v) c))) 
          \<in> {r :: real*real . fst r \<le> snd r}"                 
          using r4 l2 len_in_type by auto            
        hence " right (len v ( ts) c) \<noteq> right (ext v)" 
          using Abs_real_int_inverse Pair_inject r4 len_def real_int.left_leq_right 
            surjective_pairing by auto 
        with r1 show False by best
      qed 
    qed
  qed
qed

lemma len_hchop_left_left_border: 
  "((len v ts) c = ext v) \<and> (v=v1\<parallel>v2) \<longrightarrow> (left ((len v1 ts) c) = left (ext v1))"
proof
  assume assm:"((len v ts) c = ext v) \<and> (v=v1\<parallel>v2)"
  have l1:"left ((len v ts) c) = left (ext v)" using assm by auto 
  from assm have l2:"left (ext v) = left (ext v1)" 
    by (simp add: hchop_def real_int.rchop_def )
  from l1 and l2 have l3:"left ((len v ts) c) = left (ext v1)" by simp  
  have r1:"right ((len v ts) c) = right (ext v)" using assm by auto
  have r2:"right (ext v1) \<le> right (ext v)" 
    by (metis (no_types, lifting) assm hchop_def real_int.rchop_def 
        real_int.left_leq_right )  
  have r3:"right ((len v1 ts) c) \<le> right (ext v1)" 
    using len_right by blast
  show "(left ((len v1 ts) c) = left (ext v1))"  
  proof (cases 
      "left ((space ts v) c) \<le> right (ext v1) \<and> right ((space ts v) c) \<ge> left (ext v1)")
    case True
    show "(left ((len v1 ts) c) = left (ext v1))" 
    proof (rule ccontr)
      assume neq:" left (len v1 ( ts) c) \<noteq> left (ext v1)"
      then have greater: "left (len v1 ( ts) c) > left (ext v1)" 
        by (meson dual_order.order_iff_strict len_left)
      have len_in_type:
        "(max (left (ext v1)) (left ((space ts v) c)), 
           min (right (ext v1)) (right ((space ts v) c))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
        using Rep_real_int True by auto
      from True have "len v1 ( ts) c =  
        Abs_real_int ((max (left (ext v1)) (left ((space ts v) c))), 
                       min (right (ext v1)) (right ((space ts v) c)))" 
        using len_def assm hchop_def space_def  by auto
      hence maximum:
        "left (len v1 ( ts) c) = max (left (ext v1)) (left ((space ts v) c))" 
        using Abs_real_int_inverse len_in_type by auto  
      have "max (left (ext v1)) (left ((space ts v) c)) = left ((space ts v) c)" 
        using maximum neq by linarith
      hence "left ((space ts v) c) > left (ext v1)" 
        using greater maximum by auto
      hence l4:"left ((space ts v) c) > left (ext v)" using l2 by auto
      with assm have len_v_in_type:
        "(max (left (ext v)) (left ((space ts v) c)), 
          min (right (ext v)) (right ((space ts v) c))) 
        \<in> {r :: real*real . fst r \<le> snd r}"   
        using len_in_type r2 by auto 
      hence " left (len v ( ts) c) \<noteq> left (ext v)" 
        using Abs_real_int_inverse l4 sensors.len_def sensors_axioms by auto
      thus False using l1 by best
    qed
  next
    case False
    then have 
      "\<not>left ((space ts v) c) \<le> right (ext v1) \<or> \<not>right ((space ts v) c) \<ge> left (ext v1)"
      by auto
    then show "(left ((len v1 ts) c) = left (ext v1))"
    proof
      assume negative:"\<not> left ((space ts v) c) \<le> right (ext v1)"
      then have "len v1 ( ts) c = Abs_real_int (right (ext v1),right (ext v1))"
        using len_def assm hchop_def space_def by auto
      hence empty:"left (len v1 ( ts) c) = right (len v1 ( ts) c)" 
        by (metis real_int.chop_assoc2 real_int.chop_singleton_right real_int.rchop_def)
      have len_geq:"left(len v1 ( ts) c) \<ge> left (ext v)"  
        using l2 len_left by auto
      show "left (len v1 ( ts) c) = left (ext v1)"
      proof (rule ccontr)
        assume contra:"left (len v1 ( ts) c) \<noteq> left (ext v1)"
        with len_left have "left (ext v1) < left (len v1 ( ts) c)  " 
          using dual_order.order_iff_strict by blast 
        hence l5:"left (ext v) < left (len v1 ( ts) c)" using l2 by auto 
        hence l6:"left (len v ( ts) c) < left (len v1 ( ts) c)" using l1 by auto
        show "False" 
        proof (cases "left ((space ts v) c) \<le> right (ext v)")
          case True
          have well_sp:"left ((space ts v) c) \<le> right ((space ts v) c)"  
            using real_int.left_leq_right by auto
          have well_v:"left (ext v) \<le> right (ext v)"
            using real_int.left_leq_right by auto   
          hence rs_geq_vl:"right ((space ts v) c) \<ge> left (ext v)" 
            using empty len_geq negative r3 well_sp by linarith
          from True and rs_geq_vl have len_in_type:
            "(max (left (ext v)) (left ((space ts v) c)), 
              min (right (ext v)) (right ((space ts v) c)))
              \<in> {r :: real*real . fst r \<le> snd r}" 
            using CollectD CollectI Rep_real_int fst_conv snd_conv by auto
          have "len v (ts) c  = 
                Abs_real_int (max (left (ext v)) (left ((space ts v) c)), 
                               min (right (ext v)) (right ((space ts v) c)))" 
            using len_def using True rs_geq_vl by auto 
          hence max_less:
            "max (left (ext v)) (left ((space ts v) c)) <  left (len v1 ( ts) c)" 
            using Abs_real_int_inverse 
            by (metis (full_types) l5 assm fst_conv left.rep_eq len_in_type)
          show False 
            using empty max_less negative r3 by auto 
        next
          case False
          then have "len v ( ts) c = Abs_real_int (right (ext v), right (ext v))"
            using len_def by auto
          hence empty_len_v:"left (len v ( ts) c) = right (ext v)" using Abs_real_int_inverse 
            by simp
          show False 
            using l6 empty empty_len_v r2 r3 by linarith
        qed 
      qed
    next
      have "space ts v1 c \<le> space ts v c" using assm hchop_def space_def  by auto
      hence r4:"right (space ts v1 c) \<le> right (space ts v c)" 
        using  less_eq_real_int_def by auto 
      assume left_outside:"\<not> left (ext v1) \<le> right ((space ts v) c)"
      hence "left (ext v1 ) > right (space ts v1 c)" using r4 by linarith
      then have "len v1 ( ts) c = Abs_real_int (left (ext v1),left (ext v1))"
        using len_def assm hchop_def real_int.left_leq_right r1 r2 l1 l2 l3 r3  
        by (meson le_less_trans less_trans not_less)
      thus "(left ((len v1 ts) c) = left (ext v1))"
        using  Abs_real_int_inverse by auto
    qed
  qed
qed

lemma len_view_hchop_left: 
  "((len v ts) c = ext v) \<and> (v=v1\<parallel>v2) \<longrightarrow> ((len v1 ts) c = ext v1)" 
  by (metis Rep_real_int_inverse left.rep_eq len_hchop_left_left_border 
      len_hchop_left_right_border prod.collapse right.rep_eq)

lemma len_hchop_right_left_border: 
  "((len v ts) c = ext v) \<and> (v=v1\<parallel>v2) \<longrightarrow> (left ((len v2 ts) c) = left (ext v2))"
proof
  assume assm:"((len v ts) c = ext v) \<and> (v=v1\<parallel>v2)"
  have r1:"right ((len v ts) c) = right (ext v)" using assm by auto 
  from assm have r2:"right (ext v) = right (ext v2)" 
    by (simp add: hchop_def real_int.rchop_def )
  from r1 and r2 have r3:"right ((len v ts) c) = right (ext v2)" by simp  
  have l1:"left ((len v ts) c) = left (ext v)" using assm by auto
  have l2:"left (ext v2) \<ge> left (ext v)" 
    using assm less_eq_real_int_def real_int.chop_leq2 view.hchop_def by blast
  have l3:"left ((len v2 ts) c) \<ge> left (ext v2)" 
    using len_left by blast
  show "left ((len v2 ts) c) = left (ext v2)" 
  proof (rule ccontr)
    assume contra:"left ((len v2 ts) c) \<noteq> left (ext v2)"
    with l3 have less:"left ((len v2 ts) c) > left (ext v2)" by simp
    show False
    proof (cases "left ((space ts v) c) \<le> right (ext v2)")
      assume neg1:"\<not> left ((space ts v) c) \<le> right (ext v2)" 
      have "left ((len v2 ts) c) = left (ext v2)" 
      proof -   
        have "(len v2 ts) c = Abs_real_int (right (ext v2),right (ext v2))"
          using len_def  neg1 assm hchop_def space_def  by auto
        thus "left ((len v2 ts) c) = left (ext v2)" 
          using assm l2 l3 len_def neg1 r3 by auto
      qed
      with contra show False ..
    next
      assume less1:"left ((space ts v) c) \<le> right (ext v2)"
      show False
      proof (cases "right ((space ts v) c) \<ge> left (ext v2)")
        assume neg2:"\<not> left (ext v2) \<le> right ((space ts v) c)"
        have "space ts v2 c \<le> space ts v c" using assm hchop_def space_def  by auto
        hence "right (space ts v2 c) \<le> right (space ts v c)" using less_eq_real_int_def 
          by auto
        with neg2 have greater:"left (ext v2 ) > right (space ts v2 c)" by auto
        have "left ((len v2 ts) c) = left (ext v2)"
        proof -
          have len_empty:"(len v2 ts) c = Abs_real_int (left (ext v2),left (ext v2))"
            using len_def  neg2 assm hchop_def   less1 space_def by auto
          have l4:"left((len v2 ts)c ) = left (ext v)" 
            using Abs_real_int_inverse len_def less neg2  assm hchop_def 
              CollectI len_empty prod.collapse prod.inject by auto 
          hence "left (ext v) = left (ext v2)" 
            using l2 l3 by auto
          thus "left ((len v2 ts) c) = left (ext v2)" using l4 by auto
        qed
        with contra  show False ..
      next
        assume less2:"left (ext v2) \<le> right ((space ts v) c)"
        have len_in_type:
          "(max (left (ext v2)) (left ((space ts v) c)), 
            min (right (ext v2)) (right ((space ts v) c))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
          using Rep_real_int less1 less2 by auto
        from less1 and less2 have len_def_v2:"len v2 ( ts) c = 
                Abs_real_int (max (left (ext v2)) (left ((space ts v) c)),
                              min (right (ext v2)) (right ((space ts v) c)))" 
          using len_def assm hchop_def space_def  by auto
        with less have 
          "max (left (ext v2)) (left ((space ts v) c)) = left ((space ts v) c)"
          using Abs_real_int_inverse len_in_type snd_conv by auto
        hence "left ((space ts v) c) \<ge> left (ext v2)" by simp
        hence "left ((space ts v) c) \<ge> left (ext v)" 
          using l2 by auto
        from len_def_v2 and less and len_in_type
        have "left ((space ts v) c) > left (ext v2)" 
          using Abs_real_int_inverse sndI by auto
        hence l5:"left ((space ts v) c) > left (ext v)" 
          using l2 by linarith
        with assm have len_v_in_type:
          "(max (left (ext v)) (left (space ts v c)), 
             min (right (ext v)) (right (space ts v c))) 
          \<in> {r :: real*real . fst r \<le> snd r}"                 
          using r2 len_in_type by auto
        hence "left (len v ( ts) c) \<noteq> left (ext v)" 
          using Abs_real_int_inverse Pair_inject l5 len_def real_int.left_leq_right
            surjective_pairing by auto 
        with l1 show False by best
      qed 
    qed
  qed
qed

lemma len_hchop_right_right_border: 
  "((len v ts) c = ext v) \<and> (v=v1\<parallel>v2) \<longrightarrow> (right ((len v2 ts) c) = right (ext v2))"
proof
  assume assm:"((len v ts) c = ext v) \<and> (v=v1\<parallel>v2)"
  have r1:"right ((len v ts) c) = right (ext v)" using assm by auto 
  from assm have r2:"right (ext v) = right (ext v2)" 
    by (simp add: hchop_def real_int.rchop_def )
  from r1 and r2 have r3:"right ((len v ts) c) = right (ext v2)" by simp  
  have l1:"left ((len v ts) c) = left (ext v)" using assm by auto
  have l2:"left (ext v2) \<le> right (ext v)" 
    using assm view.h_chop_middle2 by blast
  have l3:"left ((len v2 ts) c) \<ge> left (ext v2)" 
    using len_left by blast
  show "(right ((len v2 ts) c) = right (ext v2))"  
  proof (cases 
      "left ((space ts v) c) \<le> right (ext v2) \<and> right ((space ts v) c) \<ge> left (ext v2)")
    case True
    show "(right ((len v2 ts) c) = right (ext v2))" 
    proof (rule ccontr)
      assume neq:" right (len v2 ( ts) c) \<noteq> right (ext v2)"
      then have lesser: "right (len v2 ( ts) c) < right (ext v2)" 
        using len_right less_eq_real_def by blast 
      have len_in_type:
        "(max (left (ext v2)) (left (space ts v c)), 
          min (right (ext v2)) (right (space ts v c))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
        using Rep_real_int True by auto
      from True have 
        "len v2 ( ts) c = 
          Abs_real_int (max (left (ext v2)) (left (space ts v c)), 
                         min (right (ext v2)) (right (space ts v c)))" 
        using len_def assm hchop_def space_def by auto
      hence maximum:
        "right (len v2 ( ts) c) = min (right (ext v2)) (right ((space ts v) c))" 
        using Abs_real_int_inverse len_in_type by auto  
      have min_right:
        "min (right (ext v2)) (right ((space ts v) c)) = right ((space ts v) c)" 
        using maximum neq by linarith
      hence "right ((space ts v) c) < right (ext v2)" 
        using lesser maximum by auto
      hence right_v:"right ((space ts v) c) < right (ext v)" 
          using r2 by auto
      have right_inside:"right ((space ts v) c) \<ge> left (ext v)" 
        by (meson True assm less_eq_real_int_def less_eq_view_ext_def 
            order_trans view.horizontal_chop_leq2)
      with assm and True and right_inside
      have len_v_in_type:
        "(max (left (ext v)) (left (space ts v c)), 
          min (right (ext v)) (right (space ts v c))) 
        \<in> {r :: real*real . fst r \<le> snd r}"   
        using min_right r2 real_int.left_leq_right by auto
      hence " right (len v ( ts) c) \<noteq> right (ext v)" 
        using Abs_real_int_inverse Pair_inject right_v len_def 
          real_int.left_leq_right surjective_pairing 
        by auto 
      thus False using r1 by best
    qed
  next
    case False
    then have "\<not>left ((space ts v) c) \<le> right (ext v2) \<or> 
               \<not>right ((space ts v) c) \<ge> left (ext v2)"
      by auto
    thus "right ((len v2 ts) c) = right (ext v2)" 
    proof
      assume negative:"\<not> left ((space ts v) c) \<le> right (ext v2)"
      show ?thesis  
       using left_space negative r1 r3 sensors.len_def sensors_axioms by auto
    next
      assume left_outside:"\<not> left (ext v2) \<le> right ((space ts v) c)"
      hence "left (ext v2) > right (space ts v2 c)" 
        using assm hchop_def space_def by auto 
      then have len:"len v2 ( ts) c = Abs_real_int (left (ext v2),left (ext v2))" 
        by (metis (no_types, hide_lams) len_def l2 le_less_trans not_less order.asym
            space_nonempty r2)   
      show "(right ((len v2 ts) c) = right (ext v2))" 
      proof (cases "right ((space ts v) c) \<ge> left (ext v)")
        assume "\<not> left (ext v) \<le> right ((space ts v) c)"
        hence len_empty:"len v (ts) c = Abs_real_int (left (ext v), left (ext v))" 
          using len_def real_int.left_leq_right Abs_real_int_inverse  
          by (meson less_trans not_less space_nonempty)
        show "(right ((len v2 ts) c) = right (ext v2))"
          by (metis (no_types, hide_lams) Rep_real_int_inverse assm dual_order.antisym 
              left.rep_eq len len_empty prod.collapse real_int.chop_singleton_left 
              real_int.rchop_def right.rep_eq view.h_chop_middle1 view.hchop_def)
      next
        assume "left (ext v) \<le> right ((space ts v) c)"
        then show ?thesis 
          using l2 left_outside len_space_right r1  by fastforce
      qed
    qed
  qed
qed

lemma len_view_hchop_right: 
  "((len v ts) c = ext v) \<and> (v=v1\<parallel>v2) \<longrightarrow> ((len v2 ts) c = ext v2)"  
  by (metis Rep_real_int_inverse left.rep_eq len_hchop_right_left_border 
      len_hchop_right_right_border prod.collapse right.rep_eq)

lemma len_compose_hchop:
  "(v=v1\<parallel>v2) \<and> (len v1 ( ts) c = ext v1) \<and> (len v2 ( ts) c = ext v2)
     \<longrightarrow> (len v ( ts) c = ext v)" 
proof
  assume assm:"(v=v1\<parallel>v2) \<and> (len v1 ( ts) c = ext v1) \<and> (len v2 ( ts) c = ext v2)"
  then have left_v1:"left (len v1 ( ts) c) = left (ext v1)" by auto
  from assm have right_v1:"right (len v1 ( ts) c) = left (ext v2)" 
    by (simp add: hchop_def real_int.rchop_def )
  from assm have left_v2:"left (len v2 ( ts) c) = right (ext v1)" 
    using right_v1 by auto
  from assm have right_v2:"right (len v2 ( ts) c) = right (ext v2)" by auto
  show "(len v ( ts) c = ext v)" 
  proof (cases " left ((space ts v) c) > right (ext v)")
    case True     
    then have "left (space ts v c) > right (ext v2)" using assm right_v2 
      by (simp add: hchop_def real_int.rchop_def )
    then have "left (space ts v2 c) > right( ext v2)" 
      using assm hchop_def sensors.space_def sensors_axioms  by auto
    then have "len v2 ts c = Abs_real_int(right (ext v2), right (ext v2))" 
      using len_def by simp
    then have "ext v2 = Abs_real_int(right (ext v2), right (ext v2))" using assm by simp
    then have "\<parallel>ext v2\<parallel> = 0" 
      by (metis Rep_real_int_inverse fst_conv left.rep_eq
          real_int.chop_singleton_right real_int.length_zero_iff_borders_eq
          real_int.rchop_def right.rep_eq snd_conv surj_pair)
    then have "ext v = ext v1" 
      using assm hchop_def real_int.rchop_def real_int.chop_empty2
      by simp
    then show ?thesis 
      using assm hchop_def len_def sensors.space_def sensors_axioms  
      by auto
  next
    case False
    then have in_left:"left (space ts v c) \<le> right (ext v)" by simp
    show "len v ts c = ext v"
    proof (cases "right (space ts v c) < left (ext v)")
      case True
      then have "right (space ts v c) < left (ext v1)" using assm left_v1
        by (simp add: hchop_def real_int.rchop_def)
      then have out_v1:"right (space ts v1 c) < left (ext v1)"
        using assm hchop_def sensors.space_def sensors_axioms  by auto
      then have "len v1 ts c = Abs_real_int(left (ext v1), left (ext v1))" 
        using len_def in_left 
        by (meson le_less_trans less_trans not_le real_int.left_leq_right)   
      then have "ext v1 = Abs_real_int (left (ext v1), left (ext v1))" using assm by simp
      then have "\<parallel>ext v1\<parallel> = 0"
        by (metis add.right_neutral real_int.chop_singleton_left
            real_int.length_zero_iff_borders_eq real_int.rchop_def real_int.shift_def
            real_int.shift_zero)
      then have "ext v = ext v2" using assm hchop_def real_int.rchop_def real_int.chop_empty1
        by auto
      then show ?thesis 
        using assm hchop_def len_def sensors.space_def sensors_axioms by auto
    next
      case False
      then  have in_right:"right (space ts v c) \<ge> left (ext v)"  by simp
      have f1: "own v = own v2" using assm hchop_def 
        by (auto) 
      have f2: "own v = own v1"
        using assm hchop_def  by auto
      have chop:"R_Chop(ext v,ext v1,ext v2)" using assm hchop_def 
        by (auto )
      have len:"len v ts c = Abs_real_int(max (left (ext v)) (left (space ts v c)),
                      min (right (ext v)) (right (space ts v c)))"
        using len_def in_left in_right by simp
      have len1:"len v1 ts c = Abs_real_int(max (left (ext v1)) (left (space ts v1 c)),
                      min (right (ext v1)) (right (space ts v1 c)))"
        by (metis assm f2 f1 chop assm in_left in_right len_def len_space_left
            not_le real_int.rchop_def space_def)
      then have "max (left (ext v1)) (left (space ts v1 c)) = left (len v1 ts c)" 
        by (metis assm chop f1 f2 in_left len_space_left max.orderE
            real_int.rchop_def space_def)
      then have left_border:"max (left (ext v1)) (left (space ts v1 c)) = left (ext v1)"
        using left_v1 by simp
      have len2:"len v2 ts c = Abs_real_int(max (left (ext v2)) (left (space ts v2 c)),
                      min (right (ext v2)) (right (space ts v2 c)))" 
        by (metis len_def in_left in_right assm f2 f1 chop len_space_right not_le
            real_int.rchop_def space_def)
      then have "min (right (ext v2)) (right (space ts v2 c)) = right (len v2 ts c)" 
        by (metis assm chop f1 f2 in_right len_space_right min.absorb_iff1 
            real_int.rchop_def space_def)
      then have right_border:
        "min (right (ext v2)) (right (space ts v2 c)) = right (ext v2)"
        using right_v2 by simp
      have "left (space ts v c) = left (space ts v1 c)" 
        using assm hchop_def sensors.space_def sensors_axioms by auto
      then have max:
        "  max (left (ext v)) (left (space ts v c)) 
         = max (left (ext v1)) (left (space ts v1 c))" 
        using assm hchop_def real_int.rchop_def  by auto
      have "right (space ts v c) = right (space ts v2 c)" 
        using assm hchop_def sensors.space_def sensors_axioms by auto
      then have min:
        "  min (right (ext v)) (right (space ts v c)) 
         = min (right (ext v2)) (right (space ts v2 c))" 
        using assm hchop_def real_int.rchop_def by auto
      show ?thesis 
        by (metis min max left_border right_border False add.right_neutral 
            chop in_left len_def not_le real_int.rchop_def real_int.shift_def
            real_int.shift_zero)
    qed
  qed
qed


lemma len_stable:"(v=v1--v2) \<longrightarrow> len v1 ts c = len v2 ts c" 
proof
  assume assm:"v=v1--v2"
  then have ext_eq1:"ext v = ext v1" and ext_eq2:"ext v = ext v2" 
    using vchop_def by auto
  hence ext1_eq_ext2:"ext v1 = ext v2" by simp
  show "len v1 ts c = len v2 ts c" 
    using assm ext1_eq_ext2 left_space right_space sensors.len_def sensors_axioms 
      view.vertical_chop_own_trans by auto
qed

lemma len_empty_on_subview1:
  "\<parallel>len v ( ts) c\<parallel> = 0 \<and> (v=v1\<parallel>v2) \<longrightarrow> \<parallel>len v1 ( ts) c\<parallel> = 0" 
proof
  assume assm:"\<parallel>len v ( ts) c\<parallel> = 0 \<and> (v=v1\<parallel>v2)"
  then have len_v_borders:"left (len v ( ts) c) = right (len v ( ts) c)" 
    by (simp add:real_int.length_zero_iff_borders_eq)  
  show "\<parallel>len v1 ( ts) c\<parallel> = 0" 
  proof (cases "left ((space ts v) c) > right (ext v1)")
    assume left_outside_v1:"left ((space ts v) c) > right (ext v1)"  
    thus "\<parallel>len v1 ( ts) c\<parallel> = 0" 
      using Abs_real_int_inverse assm fst_conv hchop_def len_def real_int.length_zero_iff_borders_eq
        mem_Collect_eq snd_conv space_def  by auto
  next
    assume left_inside_v1:"\<not>left ((space ts v) c) > right (ext v1)"
    show "\<parallel>len v1 ( ts) c\<parallel> = 0" 
    proof (cases "left (ext v1) > right ((space ts v) c)")
      assume right_outside_v1:"left (ext v1) > right ((space ts v) c)" 
      hence "left (ext v1) > right ((space ts v1) c)" using assm hchop_def space_def
        by auto
      thus "\<parallel>len v1 (ts) c\<parallel> = 0" 
        using assm hchop_def len_def real_int.length_def  Abs_real_int_inverse by auto
    next 
      assume right_inside_v1:"\<not>left (ext v1) > right ((space ts v) c)"
      have len_v1:
        "len v1 ( ts) c = Abs_real_int (max (left (ext v1)) (left (space ts v c)), 
                                        min (right (ext v1)) (right (space ts v c)))" 
        using left_inside_v1 len_def right_inside_v1 assm hchop_def space_def by auto
      from left_inside_v1 and right_inside_v1 have inside_v:
        "\<not>left (space ts v c) > right (ext v) \<and> \<not>left (ext v) > right (space ts v c)" 
      proof -
        have "fst (Rep_real_int (ext v2)) \<le> snd (Rep_real_int (ext v))"
          using assm view.h_chop_middle2 by force
        then show ?thesis
          using assm left_inside_v1 real_int.rchop_def right_inside_v1 view.hchop_def 
          by force
      qed
      hence len_v:
        "len v ts c = Abs_real_int (max (left (ext v)) (left (space ts v c)),
                                    min (right (ext v)) (right (space ts v c)))" 
        by (simp add: len_def)
      have less_eq:
        "  max (left (ext v)) (left (space ts v c)) 
         \<le> min (right (ext v)) (right (space ts v c))"
        using inside_v real_int.left_leq_right by auto        
      from len_v have len_v_empty: 
        "  max (left (ext v)) (left ((space ts v) c)) 
         = min (right (ext v)) (right ((space ts v) c))" 
        using Abs_real_int_inverse Rep_real_int_inverse inside_v
        len_v_borders local.less_eq by auto
      have left_len_eq:
        " max (left (ext v)) (left (space ts v c)) 
        = max (left (ext v1)) (left (space ts v c))"
        using assm hchop_def real_int.rchop_def  by auto
      have right_len_leq:
        "  min (right (ext v)) (right (space ts v c)) 
         \<ge> min (right (ext v1)) (right (space ts v c))"
        by (metis (no_types, hide_lams) assm min.bounded_iff min_less_iff_conj not_le
            order_refl real_int.rchop_def view.h_chop_middle2 view.hchop_def)
      hence left_geq_right:
        "  max (left (ext v1)) (left (space ts v c))
         \<ge> min (right (ext v1)) (right (space ts v c))"
        using left_len_eq len_v_empty by auto
      thus "\<parallel>len v1 ( ts) c\<parallel> = 0" 
      proof -
        have f1: 
          " \<not> max (left (ext v)) (left (space ts v c)) 
            \<le> min (right (ext v1)) (right (space ts v c)) 
          \<or> 
              min (right (ext v1)) (right (space ts v c)) 
            = max (left (ext v)) (left (space ts v c))"
          by (metis antisym_conv left_geq_right left_len_eq)
        have 
          "\<And>r. \<not> left (ext v1) \<le> r 
             \<or> \<not> left (space ts v c) \<le> r 
             \<or> max (left (ext v)) (left (space ts v c)) \<le> r"
          using left_len_eq by auto
        then have 
          "  min (right (ext v1)) (right (space ts v c)) 
           = max (left (ext v)) (left (space ts v c))"
          using f1 inside_v left_inside_v1 real_int.left_leq_right by force
        then show ?thesis
          using assm left_len_eq len_v len_v1 len_v_empty by auto
      qed
    qed
  qed
qed

lemma len_empty_on_subview2:
  "\<parallel>len v ts c\<parallel> = 0 \<and> (v=v1\<parallel>v2) \<longrightarrow> \<parallel>len v2 ts c\<parallel> = 0"
proof
  assume assm:"\<parallel>len v ( ts) c\<parallel> = 0 \<and> (v=v1\<parallel>v2)"
  then have len_v_borders:"left (len v ( ts) c) = right (len v ( ts) c)"
     by (simp add:real_int.length_zero_iff_borders_eq)  
  show "\<parallel>len v2 ( ts) c\<parallel> = 0" 
  proof (cases "left ((space ts v) c) > right (ext v2)")
    assume left_outside_v2:"left ((space ts v) c) > right (ext v2)"  
    thus "\<parallel>len v2 ( ts) c\<parallel> = 0" 
      using Abs_real_int_inverse assm fst_conv hchop_def len_def 
        real_int.length_zero_iff_borders_eq mem_Collect_eq snd_conv space_def
      by auto
  next
    assume left_inside_v2:"\<not>left (space ts v c) > right (ext v2)"
    show "\<parallel>len v2 ( ts) c\<parallel> = 0" 
    proof (cases "left (ext v2) > right (space ts v c)")
      assume right_outside_v2:"left (ext v2) > right ((space ts v) c)" 
      thus "\<parallel>len v2 ( ts) c\<parallel> = 0" 
        using Abs_real_int_inverse assm fst_conv hchop_def len_def 
          real_int.length_zero_iff_borders_eq mem_Collect_eq snd_conv 
          right_outside_v2 space_def
        by auto
    next 
      assume right_inside_v2:"\<not>left (ext v2) > right ((space ts v) c)"
      have len_v2:
        "len v2 ts c = Abs_real_int (max (left (ext v2)) (left (space ts v c)),
                                     min (right (ext v2)) (right (space ts v c)))" 
        using left_inside_v2 len_def right_inside_v2 assm hchop_def space_def by auto
      from left_inside_v2 and right_inside_v2 have inside_v:
        "\<not>left ((space ts v) c) > right (ext v) \<and> \<not>left (ext v) > right ((space ts v) c)" 
      proof -
        have "left (ext v) \<le> right (ext v1)"
          using assm view.h_chop_middle1 by auto
        then show ?thesis
          using assm left_inside_v2 real_int.rchop_def right_inside_v2 view.hchop_def 
          by force
      qed
      hence len_v:
        "len v ts c = Abs_real_int (max (left (ext v)) (left (space ts v c)), 
                                    min (right (ext v)) (right (space ts v c)))" 
        by (simp add: len_def)
      have less_eq:
        "  max (left (ext v)) (left (space ts v c)) 
         \<le> min (right (ext v)) (right (space ts v c))"
        using inside_v real_int.left_leq_right by auto        
      from len_v have len_v_empty: 
        "  max (left (ext v)) (left (space ts v c))
         = min (right (ext v)) (right (space ts v c))"
        using Abs_real_int_inverse Rep_real_int_inverse inside_v
        using len_v_borders local.less_eq by auto
      have left_len_eq:
        "  max (left (ext v)) (left (space ts v c)) 
        \<le> max (left (ext v2)) (left (space ts v c))"
        by (metis (no_types, hide_lams) assm left_leq_right max.mono order_refl
            real_int.rchop_def view.hchop_def)
      have right_len_leq:
        "  min (right (ext v)) (right (space ts v c)) 
         = min (right (ext v2)) (right (space ts v c))"
        using assm real_int.rchop_def view.hchop_def by auto
      hence left_geq_right:
        " max (left (ext v2)) (left (space ts v c)) 
        \<ge> min (right (ext v2)) (right (space ts v c))"
        using left_len_eq len_v_empty by auto
      then have 
        "  max (left (ext v2)) (left (space ts v2 c)) 
         \<ge> min (right (ext v2)) (right (space ts v2 c))"
        using assm hchop_def space_def  by auto
      then have 
        "  max (left (ext v2)) (left (space ts v2 c))
         = min (right (ext v2)) (right (space ts v2 c))"
        by (metis (no_types, hide_lams) antisym_conv assm hchop_def len_v_empty
            max_def min.bounded_iff not_le space_def right_inside_v2 right_len_leq
            view.h_chop_middle2)
      thus "\<parallel>len v2 ( ts) c\<parallel> = 0" 
        by (metis (no_types, hide_lams)  assm hchop_def len_v len_v2 len_v_empty
            space_def right_len_leq)
    qed
  qed
qed

lemma len_hchop_add:
  "(v=v1\<parallel>v2) \<longrightarrow> \<parallel>len v ts c\<parallel> = \<parallel>len v1 ts c\<parallel> + \<parallel>len v2 ts c\<parallel>" 
proof
  assume chop:"v=v1\<parallel>v2"
  show "\<parallel>len v ts c\<parallel> = \<parallel>len v1 ts c\<parallel> + \<parallel>len v2 ts c\<parallel>"
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left (space ts v c) > right (ext v)"
    hence len_zero:"\<parallel>len v ( ts) c\<parallel> = 0" 
      by (simp add: Abs_real_int_inverse  len_def real_int.length_zero_iff_borders_eq
          snd_eqD)
    with chop have "\<parallel>len v1 ts c\<parallel> + \<parallel>len v2 ts c\<parallel> = 0" 
      by (metis add_cancel_right_left len_empty_on_subview1 len_empty_on_subview2)
    thus ?thesis using len_zero by (simp)
  next 
    assume inside_right:"\<not>left ((space ts v) c) > right (ext v)"   
    show "\<parallel>len v ts c\<parallel> = \<parallel>len v1 ts c\<parallel> + \<parallel>len v2 ts c\<parallel>"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right (space ts v c) "
      hence len_zero:"\<parallel>len v ( ts) c\<parallel> = 0" 
        by (simp add: Abs_real_int_inverse len_def real_int.length_zero_iff_borders_eq
            snd_eqD)
      with chop have "\<parallel>len v1 ts c\<parallel> + \<parallel>len v2 ts c\<parallel> = 0" 
        by (metis add_cancel_right_left len_empty_on_subview1 len_empty_on_subview2)
      thus ?thesis using len_zero by (simp )
    next 
      assume inside_left:" \<not>left (ext v) > right ((space ts v) c) "
      hence len_def_v:"len v ( ts) c = 
                Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), 
                              min (right (ext v)) (right ((space ts v) c)))"
        using len_def inside_left inside_right by simp
      from inside_left and inside_right have 
        len_in_type:"(max (left (ext v)) (left ((space ts v) c)), 
                      min (right (ext v)) (right ((space ts v) c))) 
                     \<in> {r :: real*real . fst r \<le> snd r}" 
        using CollectD CollectI Rep_real_int fst_conv snd_conv by auto          
      show "\<parallel>len v ( ts) c\<parallel> = \<parallel>len v1 ( ts) c\<parallel> + \<parallel>len v2 ( ts) c\<parallel>"
      proof (cases "right (len v ( ts) c) < right (ext v1)")
        assume inside_v1:"right (len v ( ts) c) < right (ext v1)"
        then have min_less_v1:
          "min (right (ext v)) (right (space ts v c)) < right (ext v1)" 
          using Abs_real_int_inverse len_in_type len_def_v by auto
        hence outside_v2:"right ((space ts v) c) < left (ext v2)" 
        proof -
          have "left (ext v2) = right (ext v1)"
            using chop real_int.rchop_def view.hchop_def by force
          then show ?thesis
            by (metis (no_types) chop dual_order.order_iff_strict
                min_less_iff_conj min_less_v1 not_less view.h_chop_middle2)
        qed 
        hence len_v2_0:"\<parallel>len v2 ( ts) c\<parallel> = 0" using  Abs_real_int_inverse len_def 
            real_int.length_zero_iff_borders_eq outside_v2  snd_eqD Rep_real_int_inverse
            chop hchop_def prod.collapse real_int.rchop_def real_int.chop_singleton_right
            space_def 
            by auto
        have inside_left_v1:"  \<not>left (ext v1) > right ((space ts v) c) " 
          using chop hchop_def inside_left real_int.rchop_def  by auto 
        have inside_right_v1:"\<not>left ((space ts v) c) > right (ext v1)" 
          by (meson inside_right less_trans min_less_iff_disj min_less_v1 
              order.asym space_nonempty)
        have len1_def:"len v1 ( ts) c = 
                Abs_real_int ((max (left (ext v1)) (left ((space ts v) c))), 
                              min (right (ext v1)) (right ((space ts v) c)))"        
          using len_def inside_left_v1 inside_right_v1 chop hchop_def space_def
          by auto
        hence "\<parallel>len v ts c\<parallel> = \<parallel>len v1 ts c\<parallel>" 
        proof -
          have "right (ext v1) \<le> right (ext v2)"
            using chop left_leq_right real_int.rchop_def view.hchop_def by auto
          then show ?thesis
            using chop len1_def len_def_v min_less_v1 real_int.rchop_def view.hchop_def
            by auto
        qed
        thus "\<parallel>len v ts c\<parallel> = \<parallel>len v1 ts c\<parallel> + \<parallel>len v2 ts c\<parallel>" 
          using len_v2_0 by (simp)
      next
        assume r_inside_v2:"\<not> right (len v ( ts) c) < right (ext v1)"
        show "\<parallel>len v ( ts) c\<parallel> = \<parallel>len v1 ( ts) c\<parallel> + \<parallel>len v2 ( ts) c\<parallel>"
        proof (cases "left (len v ( ts) c) > left (ext v2)")
          assume inside_v2:"left (len v ( ts) c) > left (ext v2)"
          hence max_geq_v1:"max (left (ext v)) (left ((space ts v) c)) > left (ext v2)" 
            using Abs_real_int_inverse len_in_type len_def by (simp )
          hence outside_v1:"left ((space ts v) c) > right (ext v1)" 
          proof -
            have "left (ext v) \<le> right (ext v1)"
              by (meson chop view.h_chop_middle1)
            then show ?thesis
              using chop max_geq_v1 real_int.rchop_def view.hchop_def by fastforce
          qed
          hence len_v1_0:"\<parallel>len v1 ts c\<parallel> = 0" 
            using Abs_real_int_inverse len_def real_int.length_zero_iff_borders_eq
              outside_v1 snd_eqD Rep_real_int_inverse chop hchop_def prod.collapse
              real_int.rchop_def real_int.chop_singleton_right space_def
            by auto
          have inside_left_v2:"  \<not>left (ext v2) > right ((space ts v) c) "
            by (meson inside_left less_max_iff_disj less_trans max_geq_v1 order.asym
                space_nonempty)
          have inside_right_v2:"\<not>left ((space ts v) c) > right (ext v2)" 
            using chop hchop_def inside_right real_int.rchop_def  by auto
          have len2_def:"len v2 ( ts) c = 
                Abs_real_int ((max (left (ext v2)) (left ((space ts v) c))), 
                              min (right (ext v2)) (right ((space ts v) c)))"        
            using len_def inside_left_v2 inside_right_v2 hchop_def chop space_def
            by auto
          hence "\<parallel>len v ts c\<parallel> = \<parallel>len v2 ts c\<parallel>" 
          proof -
            have "left (ext v) \<le> left (ext v2)"
              by (metis (no_types) chop real_int.rchop_def view.h_chop_middle1
                  view.hchop_def)
            then show ?thesis
              using chop inside_left inside_right len2_def len_def outside_v1
                real_int.rchop_def view.hchop_def
              by auto
          qed  
          thus "\<parallel>len v ts c\<parallel> = \<parallel>len v1 ts c\<parallel> + \<parallel>len v2 ts c\<parallel>" 
            using len_v1_0 by (simp)
        next
          assume l_inside_v1: "\<not>left (len v ( ts) c) > left (ext v2)"
          have inside_left_v1:"  \<not>left (ext v1) > right ((space ts v) c) " 
            using chop hchop_def inside_left real_int.rchop_def  by auto 
          have inside_right_v1:"\<not>left ((space ts v) c) > right (ext v1)" 
            using Abs_real_int_inverse chop hchop_def l_inside_v1 len_in_type
              len_def real_int.rchop_def
            by auto
          hence len1_def:"len v1 ( ts) c = 
                Abs_real_int ((max (left (ext v1)) (left ((space ts v) c))), 
                              min (right (ext v1)) (right ((space ts v) c)))"
            using inside_left_v1 inside_right_v1 len_def chop hchop_def space_def
            by (simp )
          from inside_left_v1 and inside_right_v1 have len1_in_type:
            "(max (left (ext v1)) (left (space ts v c)), 
              min (right (ext v1)) (right (space ts v c))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
            using CollectD CollectI Rep_real_int fst_conv snd_conv by auto
          have inside_left_v2:"  \<not>left (ext v2) > right ((space ts v) c) " 
            using real_int.rchop_def hchop_def inside_left chop Abs_real_int_inverse 
              len_def_v len_in_type r_inside_v2 snd_conv
            by auto 
          have inside_right_v2:"\<not>left ((space ts v) c) > right (ext v2)" 
            using Abs_real_int_inverse chop hchop_def l_inside_v1 len_in_type len_def
              real_int.rchop_def
            by auto
          hence len2_def:"len v2 ts c = 
                Abs_real_int (max (left (ext v2)) (left (space ts v c)), 
                              min (right (ext v2)) (right (space ts v c)))"
            using inside_left_v2 inside_right_v2 len_def chop hchop_def space_def
            by (auto )
          from inside_left_v2 and inside_right_v2 have len2_in_type:
            "(max (left (ext v2)) (left (space ts v c)), 
              min (right (ext v2)) (right (space ts v c))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
            using CollectD CollectI Rep_real_int fst_conv snd_conv 
            by auto
          have left_v_v1:"left (ext v) = left (ext v1)" 
            using chop hchop_def real_int.rchop_def  by auto
          have max: 
               "max (left (ext v)) (left (space ts v c)) = 
                max (left (ext v1)) (left (space ts v c))"
            using left_v_v1 by auto  
          have right_v_v2:"right (ext v) = right (ext v2)" 
            using chop hchop_def real_int.rchop_def  by auto
          have min: "(min (right (ext v)) (right ((space ts v) c))) = 
                (min (right (ext v2)) (right ((space ts v) c)))"                 
            using right_v_v2 by auto
          from max have left_len_v1_v:"left (len v ( ts) c) = left (len v1 ( ts) c)"
            using Abs_real_int_inverse fst_conv len1_def len1_in_type
              len_def_v len_in_type
            by auto
          from min have right_len_v2_v:"right (len v ( ts) c) = right (len v2 ( ts) c)"
            using Abs_real_int_inverse fst_conv len1_def len2_in_type len_def_v 
              len_in_type using len2_def snd_eqD by auto
          have "right (len v1 ( ts) c) = left (len v2 ( ts) c)" 
            using Abs_real_int_inverse chop hchop_def len1_def len1_in_type len2_def
              len2_in_type real_int.rchop_def
            by auto
          thus "\<parallel>len v ts c\<parallel> = \<parallel>len v1 ts c\<parallel> + \<parallel>len v2 ts c\<parallel>" 
            using left_len_v1_v real_int.consec_add right_len_v2_v  by simp 
        qed
      qed
    qed
  qed
qed

lemma len_non_empty_inside:
 "\<parallel>len v ( ts) c\<parallel> > 0 
  \<longrightarrow> left (space ts v c) < right (ext v) \<and> right (space ts v c) > left (ext v)"
proof
  assume assm: "\<parallel>len v ( ts) c\<parallel> > 0"
  show "left ((space ts v) c) < right (ext v) \<and> right ((space ts v) c) > left (ext v)"
  proof (rule ccontr)
    assume "\<not>(left ((space ts v) c) < right (ext v) 
              \<and> right ((space ts v) c) > left (ext v))"
    hence "\<not>left ((space ts v) c) < right (ext v) 
          \<or> \<not>right ((space ts v) c) > left (ext v)"
      by best
    thus False
    proof
      assume "\<not>left ((space ts v) c) < right (ext v)"
      hence "(left ((space ts v) c) = right (ext v)) 
            \<or> left ((space ts v) c) > right (ext v)"
        by auto
      thus False
      proof 
        assume left_eq:"left ((space ts v) c) = right (ext v)"
        hence inside_left:"right ((space ts v) c) \<ge> left (ext v)"
          by (metis order_trans real_int.left_leq_right)
        from left_eq and inside_left have len_v: 
          "len v ( ts) c = Abs_real_int (max (left (ext v)) (left (space ts v c)), 
                                         min (right (ext v)) (right (space ts v c)))"
          using len_def by auto
        hence "len v ( ts) c = Abs_real_int (left (space ts v c), left(space ts v c))" 
          by (metis left_eq max_def min_def real_int.left_leq_right)
        thus False using Abs_real_int_inverse assm real_int.length_def by auto
      next
        assume "left ((space ts v) c) > right (ext v)"
        thus False 
          using Abs_real_int_inverse assm len_def real_int.length_def by auto
      qed
    next
      assume "\<not>right ((space ts v) c) > left (ext v)"
      hence " right ((space ts v) c) = left (ext v) 
            \<or> right ((space ts v) c) < left (ext v)" 
        by auto
      thus False
      proof 
        assume right_eq:"right ((space ts v) c) = left (ext v)"
        hence inside_right:"right (ext v) \<ge> left ((space ts v) c)"
          by (metis order_trans real_int.left_leq_right)
        from right_eq and inside_right have len_v: 
          "len v ts c = Abs_real_int (max (left (ext v)) (left (space ts v c)), 
                              min (right (ext v)) (right (space ts v c)))"
          using len_def by auto
        hence 
          "len v ( ts) c = Abs_real_int(right (space ts v c), right (space ts v c))" 
          by (metis max.commute max_def min_def real_int.left_leq_right right_eq)
        thus False using Abs_real_int_inverse assm real_int.length_def by auto
      next
        assume right_le:"right ((space ts v) c) < left (ext v)"
        thus False 
          by (metis (no_types, hide_lams) Rep_real_int_inverse assm left.rep_eq len_def
              length_zero_iff_borders_eq less_irrefl prod.collapse real_int.rchop_def 
              right.rep_eq view.hchop_def view.horizontal_chop_empty_left 
              view.horizontal_chop_empty_right)
      qed
    qed
  qed
qed

lemma len_fills_subview:
  "\<parallel>len v ts c\<parallel> > 0 
      \<longrightarrow> (\<exists> v1 v2 v3 v'. (v=v1\<parallel>v2) \<and> (v2=v'\<parallel>v3) \<and> len v' ts c = ext v' \<and> 
                          \<parallel>len v' ts c\<parallel> = \<parallel>len v ts c\<parallel>)"
proof
  assume assm: "\<parallel>len v ( ts) c\<parallel> > 0" 
  show " \<exists> v1 v2 v3 v'. (v=v1\<parallel>v2) \<and> (v2=v'\<parallel>v3) \<and> len v' ( ts) c = ext v' \<and> 
          \<parallel>len v' ( ts) c\<parallel> = \<parallel>len v ( ts) c\<parallel>"
  proof -
    from assm have inside:
      "left ((space ts v) c) < right (ext v) \<and> right ((space ts v) c) > left (ext v)" 
      using len_non_empty_inside by auto
    hence len_v: 
      "len v ( ts) c = Abs_real_int (max (left (ext v)) (left (space ts v c)), 
                              min (right (ext v)) (right (space ts v c)))" 
      using len_def by auto
    obtain v1 and v2 and v3 and v' 
      where v1:
        "v1=\<lparr>ext =Abs_real_int(left(ext v), left (len v ts c)),
             lan = lan v,
             own = own v\<rparr>"
      and v2:
      "v2=\<lparr>ext =Abs_real_int(left(len v ts c), right (ext v)),
           lan = lan v,
           own = own v\<rparr>"
      and v':
      "v'=\<lparr>ext =Abs_real_int(left(len v ts c), right (len v ts c)),
           lan = lan v,
           own = own v\<rparr>"
      and v3:
      "v3=\<lparr>ext =Abs_real_int(right(len v ts c), right (ext v)),
           lan = lan v,
           own = own v\<rparr>" 
        by blast 
    hence 1:" (v=v1\<parallel>v2) \<and> (v2=v'\<parallel>v3)"
      using inside hchop_def real_int.rchop_def Abs_real_int_inverse real_int.left_leq_right
        v1 v2 v' v3 len_def
      by auto
    have right:"right (ext v') = right (len v ts c)" 
      by (simp add: Rep_real_int_inverse  v')
    then have right':"left ((space ts v) c) \<le> right (ext v')"
      by (metis inside len_space_left less_imp_le order_trans real_int.left_leq_right)
    have left:"left (ext v') = left (len v ts c)"
      by (simp add: Rep_real_int_inverse  v')
    then have left':"right ((space ts v) c) \<ge> left (ext v')"
      by (metis inside len_space_right less_imp_le order_trans real_int.left_leq_right)
    have inside':
      "left ((space ts v) c) < right (ext v') \<and> right ((space ts v) c) > left (ext v')"
      by (metis (no_types) left' right' antisym_conv assm inside left len_space_left
          len_space_right less_imp_le not_le real_int.left_leq_right
          real_int.length_zero_iff_borders_eq right)
    have inside'':
      "left (space ts v' c) < right (ext v') \<and> right (space ts v' c) > left (ext v')" 
      using "1" hchop_def inside' sensors.space_def sensors_axioms
      by auto
    have len_v_v':"len v ts c = ext v'" 
      by (metis left prod.collapse right left.rep_eq right.rep_eq Rep_real_int_inverse)
    have "left (len v ts c) = max (left (ext v)) (left ((space ts v) c)) "
      using len_v Abs_real_int_inverse Rep_real_int inside
      by auto
    with left have left_len':"left (ext v') = max (left (ext v)) (left (space ts v c))"
      by auto
    then have left_len:"left (ext v') = max (left (ext v')) (left (space ts v' c))" 
      using "1"  hchop_def space_def  by fastforce 
    have "right (len v ts c) = min (right (ext v)) (right ((space ts v) c))" 
      using len_v Abs_real_int_inverse inside Rep_real_int by auto
    with right have right_len':
      "right (ext v') = min (right (ext v)) (right (space ts v c))" 
      by auto
    then have right_len:
      "right (ext v') = min (right (ext v')) (right (space ts v' c))"         
      using "1"  hchop_def space_def by fastforce 
    have 2:"len v' ( ts) c = ext v'"
      by (metis left_len' right_len' len_v len_v_v' order.asym inside''
          len_def left_len right_len) 
    have 3:"  \<parallel>len v' ( ts) c\<parallel> = \<parallel>len v ( ts) c\<parallel>"
      using len_left len_right hchop_def 
      by (simp add: "2" len_v_v') 
    then show ?thesis using 1 2 3 by blast
  qed
qed

lemma ext_eq_len_eq:
  "ext v = ext v'\<and> own v = own v' \<longrightarrow> len v ts c = len v' ts c" 
  using left_space right_space sensors.len_def sensors_axioms by auto

lemma len_stable_down:"(v=v1--v2) \<longrightarrow> len v ts c = len v1 ts c" 
  using ext_eq_len_eq view.vchop_def by blast

lemma len_stable_up:"(v=v1--v2) \<longrightarrow> len v ts c = len v2 ts c"
  using ext_eq_len_eq view.vchop_def by blast

lemma len_empty_subview:"\<parallel>len v ts c\<parallel> = 0 \<and> (v' \<le> v) \<longrightarrow> \<parallel>len v' ts c\<parallel> = 0" 
proof
  assume assm:"\<parallel>len v ts c\<parallel> = 0 \<and> (v' \<le> v)"
  hence "\<exists>v1 v2 v3 vl vr vu vd. (v=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v'--vu)" using
      somewhere_leq   by auto
  then obtain v1 v2 v3 vl vr vu vd 
    where views:"(v=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v'--vu)"
    by blast
  have "\<parallel>len v1 ts c\<parallel> = 0" using views assm len_empty_on_subview2 by blast
  hence "\<parallel>len v2 ts c\<parallel> = 0" using views len_empty_on_subview1 by blast
  hence "\<parallel>len v3 ts c \<parallel> = 0" using views len_stable_up by auto
  thus "\<parallel>len v' ts c \<parallel> = 0" using views len_stable_down by auto
qed

lemma view_leq_len_leq:"(ext v \<le> ext v') \<and> (own v = own v') \<and> \<parallel>len v ts c\<parallel> > 0 
                          \<longrightarrow> len v ts c \<le> len v' ts c" 
  using Abs_real_int_inverse  length_def length_ge_zero less_eq_real_int_def 
    sensors.len_def sensors.space_def sensors_axioms by auto

end
end
