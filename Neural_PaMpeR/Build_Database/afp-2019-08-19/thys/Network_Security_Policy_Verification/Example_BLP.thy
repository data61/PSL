theory Example_BLP
imports TopoS_Library
begin

definition BLPexample1::"bool" where
  "BLPexample1 \<equiv> (nm_eval SINVAR_LIB_BLPbasic) fabNet \<lparr> node_properties = [''PresenceSensor'' \<mapsto> 2, 
                                                  ''Webcam'' \<mapsto> 3, 
                                                  ''SensorSink'' \<mapsto> 3,
                                                  ''Statistics'' \<mapsto> 3] \<rparr>"
definition BLPexample3::"(string \<times> string) list list" where
  "BLPexample3 \<equiv> (nm_offending_flows SINVAR_LIB_BLPbasic) fabNet ((nm_node_props SINVAR_LIB_BLPbasic) sensorProps_NMParams_try3)"

value "BLPexample1"
value "BLPexample3"


end
