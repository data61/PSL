section \<open>General utility lemmas\<close>
theory Utils imports Main
begin

text \<open>
This is a potpourri of various lemmas not specific to our project. Some of them could very well be included in the default Isabelle library.
\<close>

text \<open>
Lemmas about the \<open>single_valued\<close> predicate.
\<close>

lemma single_valued_empty[simp]:"single_valued {}"
by (rule single_valuedI) auto

lemma single_valued_insert:
  assumes "single_valued rel"
      and "\<And> x y . \<lbrakk>(x,y) \<in> rel; x=a\<rbrakk> \<Longrightarrow> y = b"
  shows "single_valued (insert (a,b) rel)"
using assms
by (auto intro:single_valuedI dest:single_valuedD)

text \<open>
Lemmas about \<open>ran\<close>, the range of a finite map.
\<close>

lemma ran_upd: "ran (m (k \<mapsto> v)) \<subseteq> ran m \<union> {v}"
unfolding ran_def by auto

lemma ran_map_of: "ran (map_of xs) \<subseteq> snd ` set xs"
 by (induct xs)(auto simp del:fun_upd_apply dest: ran_upd[THEN subsetD])

lemma ran_concat: "ran (m1 ++ m2) \<subseteq> ran m1 \<union> ran m2"
unfolding ran_def
by auto

lemma ran_upds:
  assumes eq_length: "length ks = length vs"
  shows "ran (map_upds m ks vs) \<subseteq> ran m \<union> set vs"
proof-
  have "ran (map_upds m ks vs) \<subseteq> ran (m++map_of (rev (zip ks vs)))"
    unfolding map_upds_def by simp
  also have "\<dots> \<subseteq> ran m \<union> ran (map_of (rev (zip ks vs)))" by (rule ran_concat)
  also have "\<dots> \<subseteq> ran m \<union> snd ` set (rev (zip ks vs))"
    by (intro Un_mono[of "ran m" "ran m"] subset_refl ran_map_of)
  also have "\<dots>\<subseteq> ran m \<union> set vs"
    by (auto intro:Un_mono[of "ran m" "ran m"] subset_refl simp del:set_map simp add:set_map[THEN sym] map_snd_zip[OF eq_length])
  finally show ?thesis .
qed

lemma ran_upd_mem[simp]: "v \<in> ran (m (k \<mapsto> v))"
unfolding ran_def by auto

text \<open>
Lemmas about \<open>map\<close>, \<open>zip\<close> and \<open>fst\<close>/\<open>snd\<close>
\<close>

lemma map_fst_zip: "length xs = length ys \<Longrightarrow> map fst (zip xs ys) = xs"
apply (induct xs ys rule:list_induct2) by auto

lemma map_snd_zip: "length xs = length ys \<Longrightarrow> map snd (zip xs ys) = ys"
apply (induct xs ys rule:list_induct2) by auto

end
