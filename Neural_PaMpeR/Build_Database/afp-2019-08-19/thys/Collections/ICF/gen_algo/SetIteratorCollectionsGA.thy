(*  Title:       General Algorithms for Iterators
    Author:      Thomas Tuerk <tuerk@in.tum.de>
    Maintainer:  Thomas Tuerk <tuerk@in.tum.de>
*)
section \<open>General Algorithms for Iterators over Finite Sets\<close>
theory SetIteratorCollectionsGA
imports 
  "../spec/SetSpec" 
  "../spec/MapSpec" 
begin

subsection \<open>Iterate add to Set\<close>

definition iterate_add_to_set where
    "iterate_add_to_set s ins (it::('x,'x_set) set_iterator) = 
     it (\<lambda>_. True) (\<lambda>x \<sigma>. ins x \<sigma>) s"

lemma iterate_add_to_set_correct :
assumes ins_OK: "set_ins \<alpha> invar ins"
assumes s_OK: "invar s"
assumes it: "set_iterator it S0"
shows "\<alpha> (iterate_add_to_set s ins it) = S0 \<union> \<alpha> s \<and> invar (iterate_add_to_set s ins it)"
unfolding iterate_add_to_set_def
apply (rule set_iterator_no_cond_rule_insert_P [OF it,
         where ?I="\<lambda>S \<sigma>. \<alpha> \<sigma> = S \<union> \<alpha> s \<and> invar \<sigma>"])
apply (insert ins_OK s_OK)
apply (simp_all add: set_ins_def)
done

lemma iterate_add_to_set_dj_correct :
assumes ins_dj_OK: "set_ins_dj \<alpha> invar ins_dj"
assumes s_OK: "invar s"
assumes it: "set_iterator it S0"
assumes dj: "S0 \<inter> \<alpha> s = {}"
shows "\<alpha> (iterate_add_to_set s ins_dj it) = S0 \<union> \<alpha> s \<and> invar (iterate_add_to_set s ins_dj it)"
unfolding iterate_add_to_set_def
apply (rule set_iterator_no_cond_rule_insert_P [OF it,
         where ?I="\<lambda>S \<sigma>. \<alpha> \<sigma> = S \<union> \<alpha> s \<and> invar \<sigma>"])
apply (insert ins_dj_OK s_OK dj)
apply (simp_all add: set_ins_dj_def set_eq_iff)
done

subsection \<open>Iterator to Set\<close>

definition iterate_to_set where
    "iterate_to_set emp ins_dj (it::('x,'x_set) set_iterator) = 
     iterate_add_to_set (emp ()) ins_dj it"

lemma iterate_to_set_alt_def[code] :
    "iterate_to_set emp ins_dj (it::('x,'x_set) set_iterator) = 
     it (\<lambda>_. True) (\<lambda>x \<sigma>. ins_dj x \<sigma>) (emp ())"
unfolding iterate_to_set_def iterate_add_to_set_def by simp

lemma iterate_to_set_correct :
assumes ins_dj_OK: "set_ins_dj \<alpha> invar ins_dj"
assumes emp_OK: "set_empty \<alpha> invar emp"
assumes it: "set_iterator it S0"
shows "\<alpha> (iterate_to_set emp ins_dj it) = S0 \<and> invar (iterate_to_set emp ins_dj it)"
unfolding iterate_to_set_def
using iterate_add_to_set_dj_correct [OF ins_dj_OK _ it, of "emp ()"] emp_OK
by (simp add: set_empty_def)


subsection \<open>Iterate image/filter add to Set\<close>

text \<open>Iterators only visit element once. Therefore the image operations makes sense for
filters only if an injective function is used. However, when adding to a set using
non-injective functions is fine.\<close>

lemma iterate_image_filter_add_to_set_correct :
assumes ins_OK: "set_ins \<alpha> invar ins"
assumes s_OK: "invar s"
assumes it: "set_iterator it S0"
shows "\<alpha> (iterate_add_to_set s ins (set_iterator_image_filter f it)) = 
          {b . \<exists>a. a \<in> S0 \<and> f a = Some b} \<union> \<alpha> s \<and> 
       invar (iterate_add_to_set s ins  (set_iterator_image_filter f it))"
unfolding iterate_add_to_set_def set_iterator_image_filter_def
apply (rule set_iterator_no_cond_rule_insert_P [OF it,
         where ?I="\<lambda>S \<sigma>. \<alpha> \<sigma> = {b . \<exists>a. a \<in> S \<and> f a = Some b} \<union> \<alpha> s \<and> invar \<sigma>"])
apply (insert ins_OK s_OK)
apply (simp_all add: set_ins_def split: option.split)
apply auto
done


lemma iterate_image_filter_to_set_correct :
assumes ins_OK: "set_ins \<alpha> invar ins"
assumes emp_OK: "set_empty \<alpha> invar emp"
assumes it: "set_iterator it S0"
shows "\<alpha> (iterate_to_set emp ins (set_iterator_image_filter f it)) = 
          {b . \<exists>a. a \<in> S0 \<and> f a = Some b} \<and> 
       invar (iterate_to_set emp ins  (set_iterator_image_filter f it))"
unfolding iterate_to_set_def 
using iterate_image_filter_add_to_set_correct [OF ins_OK _ it, of "emp ()" f] emp_OK
by (simp add: set_empty_def)

text\<open>For completeness lets also consider injective versions.\<close>

lemma iterate_inj_image_filter_add_to_set_correct :
assumes ins_dj_OK: "set_ins_dj \<alpha> invar ins"
assumes s_OK: "invar s"
assumes it: "set_iterator it S0"
assumes dj: "{y. \<exists>x. x \<in> S0 \<and> f x = Some y} \<inter> \<alpha> s = {}"
assumes f_inj_on: "inj_on f (S0 \<inter> dom f)"
shows "\<alpha> (iterate_add_to_set s ins (set_iterator_image_filter f it)) = 
          {b . \<exists>a. a \<in> S0 \<and> f a = Some b} \<union> \<alpha> s \<and> 
       invar (iterate_add_to_set s ins  (set_iterator_image_filter f it))"
proof -
  from set_iterator_image_filter_correct [OF it f_inj_on]
  have it_f: "set_iterator (set_iterator_image_filter f it)
        {y. \<exists>x. x \<in> S0 \<and> f x = Some y}" by simp

  from iterate_add_to_set_dj_correct [OF ins_dj_OK, OF s_OK it_f dj]
  show ?thesis by auto
qed


lemma iterate_inj_image_filter_to_set_correct :
assumes ins_OK: "set_ins_dj \<alpha> invar ins"
assumes emp_OK: "set_empty \<alpha> invar emp"
assumes it: "set_iterator it S0"
assumes f_inj_on: "inj_on f (S0 \<inter> dom f)"
shows "\<alpha> (iterate_to_set emp ins (set_iterator_image_filter f it)) = 
          {b . \<exists>a. a \<in> S0 \<and> f a = Some b} \<and> 
       invar (iterate_to_set emp ins  (set_iterator_image_filter f it))"
unfolding iterate_to_set_def 
using iterate_inj_image_filter_add_to_set_correct [OF ins_OK _ it _ f_inj_on, of "emp ()"] emp_OK
by (simp add: set_empty_def)


subsection \<open>Iterate diff Set\<close>

definition iterate_diff_set where
    "iterate_diff_set s del (it::('x,'x_set) set_iterator) = 
     it (\<lambda>_. True) (\<lambda>x \<sigma>. del x \<sigma>) s"

lemma iterate_diff_correct :
assumes del_OK: "set_delete \<alpha> invar del"
assumes s_OK: "invar s"
assumes it: "set_iterator it S0"
shows "\<alpha> (iterate_diff_set s del it) = \<alpha> s - S0 \<and> invar (iterate_diff_set s del it)"
unfolding iterate_diff_set_def
apply (rule set_iterator_no_cond_rule_insert_P [OF it,
         where ?I="\<lambda>S \<sigma>. \<alpha> \<sigma> = \<alpha> s - S \<and> invar \<sigma>"])
apply (insert del_OK s_OK)
apply (auto simp add: set_delete_def set_eq_iff)
done

subsection \<open>Iterate add to Map\<close>

definition iterate_add_to_map where
    "iterate_add_to_map m update (it::('k \<times> 'v,'kv_map) set_iterator) = 
     it (\<lambda>_. True) (\<lambda>(k,v) \<sigma>. update k v \<sigma>) m"

lemma iterate_add_to_map_correct :
assumes upd_OK: "map_update \<alpha> invar upd"
assumes m_OK: "invar m"
assumes it: "map_iterator it M"
shows "\<alpha> (iterate_add_to_map m upd it) = \<alpha> m ++ M  \<and> invar (iterate_add_to_map m upd it)"
using assms
unfolding iterate_add_to_map_def
apply (rule_tac map_iterator_no_cond_rule_insert_P [OF it,
         where ?I="\<lambda>d \<sigma>. (\<alpha> \<sigma> = \<alpha> m ++ M |` d) \<and> invar \<sigma>"])
apply (simp_all add: map_update_def restrict_map_insert)
done

lemma iterate_add_to_map_dj_correct :
assumes upd_OK: "map_update_dj \<alpha> invar upd"
assumes m_OK: "invar m"
assumes it: "map_iterator it M"
assumes dj: "dom M \<inter> dom (\<alpha> m) = {}"
shows "\<alpha> (iterate_add_to_map m upd it) = \<alpha> m ++ M  \<and> invar (iterate_add_to_map m upd it)"
using assms
unfolding iterate_add_to_map_def
apply (rule_tac map_iterator_no_cond_rule_insert_P [OF it,
         where ?I="\<lambda>d \<sigma>. (\<alpha> \<sigma> = \<alpha> m ++ M |` d) \<and> invar \<sigma>"])
apply (simp_all add: map_update_dj_def restrict_map_insert set_eq_iff)
done


subsection \<open>Iterator to Map\<close>

definition iterate_to_map where
    "iterate_to_map emp upd_dj (it::('k \<times> 'v,'kv_map) set_iterator) = 
     iterate_add_to_map (emp ()) upd_dj it"

lemma iterate_to_map_alt_def[code] :
    "iterate_to_map emp upd_dj it = 
     it (\<lambda>_. True) (\<lambda>(k, v) \<sigma>. upd_dj k v \<sigma>) (emp ())"
unfolding iterate_to_map_def iterate_add_to_map_def by simp

lemma iterate_to_map_correct :
assumes upd_dj_OK: "map_update_dj \<alpha> invar upd_dj"
assumes emp_OK: "map_empty \<alpha> invar emp"
assumes it: "map_iterator it M"
shows "\<alpha> (iterate_to_map emp upd_dj it) = M \<and> invar (iterate_to_map emp upd_dj it)"
unfolding iterate_to_map_def
using iterate_add_to_map_dj_correct [OF upd_dj_OK _ it, of "emp ()"] emp_OK
by (simp add: map_empty_def)


end


