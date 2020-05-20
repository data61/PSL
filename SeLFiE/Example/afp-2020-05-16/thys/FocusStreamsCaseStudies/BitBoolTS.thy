(*<*)
(*
   Title:  Theory BitBoolTS.thy
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*)
(*>*)

section \<open>Properties of time-synchronous streams of types bool and bit\<close>

theory BitBoolTS 
imports Main stream
begin

datatype bit = Zero | One

primrec 
   negation :: "bit \<Rightarrow> bit"
where
  "negation Zero = One" |
  "negation One = Zero"


lemma ts_bit_stream_One:
  assumes h1:"ts x"
         and h2:"x i \<noteq> [Zero]"
  shows "x i = [One]"
proof -
  from h1 have sg1:"length (x i) = Suc 0" 
    by (simp add: ts_def)
  from this and h2 show ?thesis
  proof (cases "x i")
    assume Nil:"x i = []" 
    from this and sg1 show ?thesis by simp
  next
  fix a l assume Cons:"x i = a # l"
    from this and sg1 and h2 show ?thesis
    proof (cases "a")
      assume "a = Zero"
      from this and sg1 and h2 and Cons show ?thesis by auto
    next 
      assume "a = One"
      from this and sg1 and Cons show ?thesis by auto
    qed
  qed
qed

lemma ts_bit_stream_Zero:
  assumes h1:"ts x"
         and h2:"x i \<noteq> [One]"
  shows "x i = [Zero]"
proof -
  from h1 have sg1:"length (x i) = Suc 0" 
    by (simp add: ts_def)
  from this and h2 show ?thesis
  proof (cases "x i")
    assume Nil:"x i = []" 
    from this and sg1 show ?thesis by simp
  next
  fix a l assume Cons:"x i = a # l"
    from this and sg1 and h2 show ?thesis
    proof (cases "a")
      assume "a = Zero"
      from this and sg1 and Cons show ?thesis by auto
    next 
      assume "a = One"
      from this and sg1 and h2 and Cons show ?thesis by auto
    qed
  qed
qed

lemma ts_bool_True:
  assumes h1:"ts x"
         and h2:"x i \<noteq> [False]"
  shows "x i = [True]"
proof -
  from h1 have sg1:"length (x i) = Suc 0" 
    by (simp add: ts_def)
  from this and h2 show ?thesis
  proof (cases "x i")
    assume Nil:"x i = []" 
    from this and sg1 show ?thesis by simp
  next
  fix a l assume Cons:"x i = a # l"
    from this and sg1 have "x i = [a]" by simp
    from this and h2 show ?thesis by auto
  qed
qed

lemma ts_bool_False:
  assumes h1:"ts x"
         and h2:"x i \<noteq> [True]"
  shows "x i = [False]"
proof -
  from h1 have sg1:"length (x i) = Suc 0" 
    by (simp add: ts_def)
  from this and h2 show ?thesis
  proof (cases "x i")
    assume Nil:"x i = []" 
    from this and sg1 show ?thesis by simp
  next
  fix a l assume Cons:"x i = a # l"
    from this and sg1 have "x i = [a]" by simp
    from this and h2 show ?thesis by auto
  qed
qed

lemma ts_bool_True_False:
  fixes x::"bool istream"
  assumes "ts x" 
  shows "x i = [True] \<or> x i = [False]"
proof (cases "x i = [True]")
  assume "x i = [True]"
  from this and assms show ?thesis by simp
next
  assume "x i \<noteq> [True]"
  from this and assms show ?thesis by (simp add: ts_bool_False)
qed

end 
