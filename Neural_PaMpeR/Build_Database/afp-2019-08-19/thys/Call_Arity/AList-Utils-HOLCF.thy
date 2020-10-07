theory "AList-Utils-HOLCF"
imports "Launchbury.HOLCF-Utils" "Launchbury.HOLCF-Join-Classes" "Launchbury.AList-Utils"
begin

syntax
  "_BLubMap" :: "[pttrn, pttrn, 'a \<rightharpoonup> 'b, 'b] \<Rightarrow> 'b" ("(3\<Squnion>/_/\<mapsto>/_/\<in>/_/./ _)" [0,0,0, 10] 10)

translations
  "\<Squnion> k\<mapsto>v\<in>m. e" == "CONST lub (CONST mapCollect (\<lambda>k v . e) m)"

lemma below_lubmapI[intro]:
  "m k = Some v \<Longrightarrow> (e k v::'a::Join_cpo) \<sqsubseteq> (\<Squnion> k\<mapsto>v\<in>m. e k v)"
unfolding mapCollect_def by auto

lemma lubmap_belowI[intro]:
  "(\<And> k v . m k = Some v \<Longrightarrow> (e k v::'a::Join_cpo) \<sqsubseteq> u) \<Longrightarrow> (\<Squnion> k\<mapsto>v\<in>m. e k v) \<sqsubseteq> u"
unfolding mapCollect_def by auto

lemma lubmap_const_bottom[simp]:
  "(\<Squnion> k\<mapsto>v\<in>m. \<bottom>) = (\<bottom>::'a::Join_cpo)"
  by (cases "m = Map.empty") auto

lemma lubmap_map_upd[simp]:
  fixes e :: "'a \<Rightarrow> 'b \<Rightarrow> ('c :: Join_cpo)"
  shows "(\<Squnion>k\<mapsto>v\<in>m(k' \<mapsto> v'). e k v) = e k' v' \<squnion> (\<Squnion>k\<mapsto>v\<in>m(k':=None). e k v)"
  by simp

lemma lubmap_below_cong:
  assumes "\<And> k v. m k = Some v \<Longrightarrow> f1 k v \<sqsubseteq> (f2 k v :: 'a :: Join_cpo)"
  shows "(\<Squnion> k\<mapsto>v\<in>m. f1 k v) \<sqsubseteq> (\<Squnion> k\<mapsto>v\<in>m. f2 k v)"
  apply (rule lubmap_belowI)
  apply (rule below_trans[OF assms], assumption)
  apply (rule below_lubmapI, assumption)
  done

lemma cont2cont_lubmap[simp, cont2cont]:
  assumes "(\<And>k v . cont (f k v))"
  shows "cont (\<lambda>x. \<Squnion> k\<mapsto>v\<in>m. (f k v x) :: 'a :: Join_cpo)"
proof (rule contI2)
  show "monofun (\<lambda>x. \<Squnion>k\<mapsto>v\<in>m. f k v x)"
    apply (rule monofunI)
    apply (rule lubmap_below_cong)
    apply (erule cont2monofunE[OF assms])
    done
next
  fix Y :: "nat \<Rightarrow> 'd"
  assume "chain Y"
  assume "chain (\<lambda>i. \<Squnion>k\<mapsto>v\<in>m. f k v (Y i))"

  show "(\<Squnion>k\<mapsto>v\<in>m. f k v (\<Squnion> i. Y i)) \<sqsubseteq> (\<Squnion> i. \<Squnion>k\<mapsto>v\<in>m. f k v (Y i))"
    apply (subst cont2contlubE[OF assms \<open>chain Y\<close>])
    apply (rule lubmap_belowI)
    apply (rule lub_mono[OF ch2ch_cont[OF assms \<open>chain Y\<close>] \<open>chain (\<lambda>i. \<Squnion>k\<mapsto>v\<in>m. f k v (Y i))\<close>])
    apply (erule below_lubmapI)
    done
qed

(*
syntax
  "_BLubMapFilter" :: "[pttrn, pttrn, 'a \<rightharpoonup> 'b, 'b, bool] \<Rightarrow> 'b" ("(3\<Squnion>/_/\<mapsto>/_/\<in>/_/./ _/ |/ _)" [0,0,0,10,10] 10)

translations
  "\<Squnion> k\<mapsto>v\<in>m. e | P" == "CONST lub (CONST mapCollectFilter (\<lambda>k v. (P,e)) m)"
*)


end
