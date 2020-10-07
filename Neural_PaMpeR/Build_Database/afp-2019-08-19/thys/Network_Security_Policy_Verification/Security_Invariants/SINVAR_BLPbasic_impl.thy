theory SINVAR_BLPbasic_impl
imports SINVAR_BLPbasic "../TopoS_Interface_impl"
begin


subsubsection \<open>SecurityInvariant BLPbasic List Implementation\<close>

code_identifier code_module SINVAR_BLPbasic_impl => (Scala) SINVAR_BLPbasic

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> security_level) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> set (edgesL G). (nP e1) \<le> (nP e2))"

definition BLP_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> security_level) \<Rightarrow> ('v \<times> 'v) list list" where
  "BLP_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> (nP e1) > (nP e2)] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_BLPbasic.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_BLPbasic.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "BLP_eval G P = (wf_list_graph G \<and> 
  sinvar G (SecurityInvariant.node_props SINVAR_BLPbasic.default_node_properties P))"


interpretation BLPbasic_impl:TopoS_List_Impl
  where default_node_properties=SINVAR_BLPbasic.default_node_properties
  and sinvar_spec=SINVAR_BLPbasic.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_BLPbasic.receiver_violation
  and offending_flows_impl=BLP_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=BLP_eval
  apply(unfold TopoS_List_Impl_def)
  apply(rule conjI)
   apply(simp add: TopoS_BLPBasic)
   apply(simp add: list_graph_to_graph_def; fail)
  apply(rule conjI)
   apply(simp add: list_graph_to_graph_def)
   apply(simp add: list_graph_to_graph_def BLP_offending_set BLP_offending_set_def BLP_offending_list_def; fail)
  apply(rule conjI)
   apply(simp only: NetModel_node_props_def)
   apply(metis BLPbasic.node_props.simps BLPbasic.node_props_eq_node_props_formaldef)
  apply(simp only: BLP_eval_def)
  apply(simp add: TopoS_eval_impl_proofrule[OF TopoS_BLPBasic])
  apply(simp add: list_graph_to_graph_def)
 done



subsubsection \<open>BLPbasic packing\<close>
  definition SINVAR_LIB_BLPbasic :: "('v::vertex, security_level) TopoS_packed" where
    "SINVAR_LIB_BLPbasic \<equiv> 
    \<lparr> nm_name = ''BLPbasic'', 
      nm_receiver_violation = SINVAR_BLPbasic.receiver_violation,
      nm_default = SINVAR_BLPbasic.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = BLP_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = BLP_eval
      \<rparr>"
  interpretation SINVAR_LIB_BLPbasic_interpretation: TopoS_modelLibrary SINVAR_LIB_BLPbasic 
      SINVAR_BLPbasic.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_BLPbasic_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

subsubsection\<open>Example\<close>
  definition fabNet :: "string list_graph" where
  "fabNet \<equiv> \<lparr> nodesL = [''Statistics'', ''SensorSink'', ''PresenceSensor'', ''Webcam'', ''TempSensor'', ''FireSesnsor'',
                     ''MissionControl1'', ''MissionControl2'', ''Watchdog'', ''Bot1'', ''Bot2''], 
              edgesL =[(''PresenceSensor'', ''SensorSink''), (''Webcam'', ''SensorSink''), 
                     (''TempSensor'', ''SensorSink''),  (''FireSesnsor'', ''SensorSink''),
                     (''SensorSink'', ''Statistics''),
                     (''MissionControl1'', ''Bot1''), (''MissionControl1'', ''Bot2''),
                     (''MissionControl2'', ''Bot2''),
                     (''Watchdog'', ''Bot1''), (''Watchdog'', ''Bot2'')] \<rparr>"
  value "wf_list_graph fabNet"


  definition sensorProps_try1 :: "string \<Rightarrow> security_level" where
    "sensorProps_try1 \<equiv> (\<lambda> n. SINVAR_BLPbasic.default_node_properties)(''PresenceSensor'' := 2, ''Webcam'' := 3)"
  value "BLP_offending_list fabNet sensorProps_try1"
  value "sinvar fabNet sensorProps_try1"

  definition sensorProps_try2 :: "string \<Rightarrow> security_level" where
    "sensorProps_try2 \<equiv> (\<lambda> n. SINVAR_BLPbasic.default_node_properties)(''PresenceSensor'' := 2, ''Webcam'' := 3, 
                                                       ''SensorSink'' := 3)"
  value "BLP_offending_list fabNet sensorProps_try2"
  value "sinvar fabNet sensorProps_try2"

  definition sensorProps_try3 :: "string \<Rightarrow> security_level" where
    "sensorProps_try3 \<equiv> (\<lambda> n. SINVAR_BLPbasic.default_node_properties)(''PresenceSensor'' := 2, ''Webcam'' := 3, 
                                                       ''SensorSink'' := 3, ''Statistics'' := 3)"
  value "BLP_offending_list fabNet sensorProps_try3"
  value "sinvar fabNet sensorProps_try3"

  text \<open>Another parameter set for confidential controlling information\<close>
  definition sensorProps_conf :: "string \<Rightarrow> security_level" where
    "sensorProps_conf \<equiv> (\<lambda> n. SINVAR_BLPbasic.default_node_properties)(''MissionControl1'' := 1, ''MissionControl2'' := 2,
      ''Bot1'' := 1, ''Bot2'' := 2 )"
  value "BLP_offending_list fabNet sensorProps_conf"
  value "sinvar fabNet sensorProps_conf"


text \<open>Complete example:\<close>
  
  definition sensorProps_NMParams_try3 :: "(string, nat) TopoS_Params" where
  "sensorProps_NMParams_try3 \<equiv> \<lparr> node_properties = [''PresenceSensor'' \<mapsto> 2, 
                                                    ''Webcam'' \<mapsto> 3, 
                                                    ''SensorSink'' \<mapsto> 3,
                                                    ''Statistics'' \<mapsto> 3] \<rparr>"
  value "BLP_eval fabNet sensorProps_NMParams_try3"


export_code SINVAR_LIB_BLPbasic checking Scala

hide_const (open) NetModel_node_props BLP_offending_list BLP_eval

hide_const (open) sinvar

end
