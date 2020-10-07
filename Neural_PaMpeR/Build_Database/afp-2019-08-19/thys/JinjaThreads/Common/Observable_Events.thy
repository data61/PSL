(*  Title:      JinjaThreads/Common/Observable_Events.thy
    Author:     Andreas Lochbihler
*)

section \<open>Observable events in JinjaThreads\<close>

theory Observable_Events
imports 
  Heap
  "../Framework/FWState"
begin

datatype ('addr,'thread_id) obs_event =
    ExternalCall 'addr mname "'addr val list" "'addr val"
  | ReadMem 'addr addr_loc "'addr val"
  | WriteMem 'addr addr_loc "'addr val"
  | NewHeapElem 'addr htype
  | ThreadStart 'thread_id
  | ThreadJoin 'thread_id
  | SyncLock 'addr
  | SyncUnlock 'addr
  | ObsInterrupt 'thread_id
  | ObsInterrupted 'thread_id

instance obs_event :: (type, type) obs_action
proof qed

type_synonym
  ('addr, 'thread_id, 'x, 'heap) Jinja_thread_action = 
    "('addr,'thread_id,'x,'heap,'addr,('addr, 'thread_id) obs_event) thread_action"

(* pretty printing for Jinja_thread_action type *)
print_translation \<open>
  let
    fun tr'
       [ a1, t1, x, h, a2
       , Const (@{type_syntax "obs_event"}, _) $ a3 $ t2] =
      if a1 = a2 andalso a2 = a3 andalso t1 = t2 then Syntax.const @{type_syntax "Jinja_thread_action"} $ a1 $ t1 $ x $ h
      else raise Match;
    in [(@{type_syntax "thread_action"}, K tr')]
  end
\<close>
typ "('addr, 'thread_id, 'x, 'heap) Jinja_thread_action"

lemma range_ty_of_htype: "range ty_of_htype \<subseteq> range Class \<union> range Array"
apply(rule subsetI)
apply(erule rangeE)
apply(rename_tac ht)
apply(case_tac ht)
apply auto
done

lemma some_choice: "(\<exists>a. \<forall>b. P b (a b)) \<longleftrightarrow> (\<forall>b. \<exists>a. P b a)"
by metis

definition convert_RA :: "'addr released_locks \<Rightarrow> ('addr :: addr, 'thread_id) obs_event list"
where "\<And>ln. convert_RA ln = concat (map (\<lambda>ad. replicate (ln $ ad) (SyncLock ad)) (monitor_finfun_to_list ln))"

lemma set_convert_RA_not_New [simp]:
  "\<And>ln. NewHeapElem a CTn \<notin> set (convert_RA ln)"
by(auto simp add: convert_RA_def)

lemma set_convert_RA_not_Read [simp]:
  "\<And>ln. ReadMem ad al v \<notin> set (convert_RA ln)"
by(auto simp add: convert_RA_def)

end
