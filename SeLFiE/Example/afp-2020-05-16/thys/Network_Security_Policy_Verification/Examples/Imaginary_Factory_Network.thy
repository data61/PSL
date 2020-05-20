section "Example: Imaginary Factory Network"
theory Imaginary_Factory_Network
imports "../TopoS_Impl"
begin

text\<open>
In this theory, we give an an example of an imaginary factory network. 
The example was chosen to show the interplay of several security invariants 
and to demonstrate their configuration effort.

The specified security invariants deliberately include some minor specification problems. 
These problems will be used to demonstrate the inner workings of the algorithms and to visualize why 
some computed results will deviate from the expected results. 



The described scenario is an imaginary factory network. 
It consists of sensors and actuators in a cyber-physical system. 
The on-site production units of the factory are completely automated and there are no humans in the production area. 
Sensors are monitoring the building.
The production units are two robots (abbreviated bots) which manufacture the actual goods.
The robots are controlled by two control systems.

The network consists of the following hosts which are responsible for monitoring the building.

  \<^item> Statistics: A server which collects, processes, and stores all data from the sensors. 
  \<^item> SensorSink: A device which receives the data from the PresenceSensor, Webcam, TempSensor, and FireSensor.
                It sends the data to the Statistics server. 
  \<^item> PresenceSensor: A sensor which detects whether a human is in the building. 
  \<^item> Webcam: A camera which monitors the building indoors. 
  \<^item> TempSensor: A sensor which measures the temperature in the building. 
  \<^item> FireSensor: A sensor which detects fire and smoke. 


The following hosts are responsible for the production line. 

  \<^item> MissionControl1: An automation device which drives and controls the robots. 
  \<^item> MissionControl2: An automation device which drives and controls the robots. 
                     It contains the logic for a secret production step, carried out only by Robot2.
  \<^item> Watchdog: Regularly checks the health and technical readings of the robots. 
  \<^item> Robot1: Production robot unit 1. 
  \<^item> Robot2: Production robot unit 2. Does a secret production step. 
  \<^item> AdminPc: A human administrator can log into this machine to supervise or troubleshoot the production. 

We model one additional special host. 

  \<^item> INET: A symbolic host which represents all hosts which are not part of this network.


The security policy is defined below.
\<close>

definition policy :: "string list_graph" where
  "policy \<equiv> \<lparr> nodesL = [''Statistics'',
                        ''SensorSink'',
                        ''PresenceSensor'',
                        ''Webcam'',
                        ''TempSensor'',
                        ''FireSensor'',
                        ''MissionControl1'',
                        ''MissionControl2'',
                        ''Watchdog'',
                        ''Robot1'',
                        ''Robot2'',
                        ''AdminPc'',
                        ''INET''],
              edgesL = [(''PresenceSensor'', ''SensorSink''),
                        (''Webcam'', ''SensorSink''),
                        (''TempSensor'', ''SensorSink''),
                        (''FireSensor'', ''SensorSink''),
                        (''SensorSink'', ''Statistics''),
                        (''MissionControl1'', ''Robot1''),
                        (''MissionControl1'', ''Robot2''),
                        (''MissionControl2'', ''Robot2''),
                        (''AdminPc'', ''MissionControl2''),
                        (''AdminPc'', ''MissionControl1''),
                        (''Watchdog'', ''Robot1''),
                        (''Watchdog'', ''Robot2'')
                        ] \<rparr>"

lemma "wf_list_graph policy" by eval


ML_val\<open>
visualize_graph @{context} @{term "[]::string SecurityInvariant list"} @{term "policy"};
\<close>

text\<open>The idea behind the policy is the following.
The sensors on the left can all send their readings in an unidirectional fashion to the sensor sink, 
which forwards the data to the statistics server.
In the production line, on the right, all devices will set up stateful connections. 
This means, once a connection is established, packet exchange can be bidirectional. 
This makes sure that the watchdog will receive the health information from the robots, 
the mission control machines will receive the current state of the robots, and the administrator can actually log into the mission control machines. 
The policy should only specify who is allowed to set up the connections. 
We will elaborate on the stateful implementation in @{file \<open>../TopoS_Stateful_Policy.thy\<close>} 
and @{file \<open>../TopoS_Stateful_Policy_Algorithm.thy\<close>}.\<close>


subsection\<open>Specification of Security Invariants\<close>


text\<open>Several security invariants are specified.\<close>

text\<open>Privacy for employees.
  The sensors in the building may record any employee. 
	Due to privacy requirements, the sensor readings, processing, and storage of the data is treated with high security levels. 
	The presence sensor does not allow do identify an individual employee, hence produces less critical data, hence has a lower level.
\<close>
context begin
  private definition "BLP_privacy_host_attributes \<equiv> [''Statistics'' \<mapsto> 3,
                           ''SensorSink'' \<mapsto> 3,
                           ''PresenceSensor'' \<mapsto> 2, \<comment> \<open>less critical data\<close>
                           ''Webcam'' \<mapsto> 3
                           ]"
  private lemma "dom (BLP_privacy_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: BLP_privacy_host_attributes_def policy_def)
  definition "BLP_privacy_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_BLPbasic \<lparr> 
        node_properties = BLP_privacy_host_attributes \<rparr> ''confidential sensor data''"
end


text\<open>Secret corporate knowledge and intellectual property:
  The production process is a corporate trade secret. 
	The mission control devices have the trade secretes in their program. 
	The important and secret step is done by MissionControl2.
\<close>
context begin
  private definition "BLP_tradesecrets_host_attributes \<equiv> [''MissionControl1'' \<mapsto> 1,
                           ''MissionControl2'' \<mapsto> 2,
                           ''Robot1'' \<mapsto> 1,
                           ''Robot2'' \<mapsto> 2
                           ]"
  private lemma "dom (BLP_tradesecrets_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: BLP_tradesecrets_host_attributes_def policy_def)
  definition "BLP_tradesecrets_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_BLPbasic \<lparr> 
        node_properties = BLP_tradesecrets_host_attributes \<rparr> ''trade secrets''"
end
text\<open>Note that Invariant 1 and Invariant 2 are two distinct specifications. 
	They specify individual security goals independent of each other. 
	For example, in Invariant 1,@{term "''MissionControl2''"} has the security level 
	@{term \<bottom>} and in Invariant 2, @{term "''PresenceSensor''"} has security level @{term \<bottom>}. 
	Consequently, both cannot interact.
\<close>




text\<open>Privacy for employees, exporting aggregated data:
  Monitoring the building while both ensuring privacy of the employees is an important goal for the company. 
	While the presence sensor only collects the single-bit information whether a human is present, the 
  webcam allows to identify individual employees. 
	The data collected by the presence sensor is classified as secret while the data produced by the webcam is top secret. 
	The sensor sink only has the secret security level, hence it is not allowed to process the 
  data generated by the webcam. 
	However, the sensor sink aggregates all data and only distributes a statistical average which does 
  not allow to identify individual employees. 
	It does not store the data over long periods. 
	Therefore, it is marked as trusted and may thus receive the webcam's data. 
	The statistics server, which archives all the data, is considered top secret.
\<close>
context begin
  private definition "BLP_employee_export_host_attributes \<equiv>
                          [''Statistics'' \<mapsto> \<lparr> security_level = 3, trusted = False \<rparr>,
                           ''SensorSink'' \<mapsto> \<lparr> security_level = 2, trusted = True \<rparr>,
                           ''PresenceSensor'' \<mapsto> \<lparr> security_level = 2, trusted = False \<rparr>,
                           ''Webcam'' \<mapsto> \<lparr> security_level = 3, trusted = False \<rparr>
                           ]"
  private lemma "dom (BLP_employee_export_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: BLP_employee_export_host_attributes_def policy_def)
  definition "BLP_employee_export_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted \<lparr> 
        node_properties = BLP_employee_export_host_attributes \<rparr> ''employee data (privacy)''"
  (*TODO: what if Sensor sink were not trusted or had lower or higher level?*)
end



text\<open>Who can access bot2?
  Robot2 carries out a mission-critical production step. 
	It must be made sure that Robot2 only receives packets from Robot1, the two mission control devices and the watchdog.
\<close>
context begin
  private definition "ACL_bot2_host_attributues \<equiv>
                          [''Robot2'' \<mapsto> Master [''Robot1'',
                                                 ''MissionControl1'',
                                                 ''MissionControl2'',
                                                 ''Watchdog''],
                           ''MissionControl1'' \<mapsto> Care,
                           ''MissionControl2'' \<mapsto> Care,
                           ''Watchdog'' \<mapsto> Care
                           ]"
  private lemma "dom (ACL_bot2_host_attributues) \<subseteq> set (nodesL policy)"
    by(simp add: ACL_bot2_host_attributues_def policy_def)
  definition "ACL_bot2_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners
                             \<lparr>node_properties = ACL_bot2_host_attributues \<rparr> ''Robot2 ACL''"
  text\<open>
  Note that Robot1 is in the access list of Robot2 but it does not have the @{const Care} attribute. 
	This means, Robot1 can never access Robot2. 
	A tool could automatically detect such inconsistencies and emit a warning. 
	However, a tool should only emit a warning (not an error) because this setting can be desirable. 
	
	In our factory, this setting is currently desirable: 
	Three months ago, Robot1 had an irreparable hardware error and needed to be removed from the production line. 
	When removing Robot1 physically, all its host attributes were also deleted. 
	The access list of Robot2 was not changed. 
	It was planned that Robot1 will be replaced and later will have the same access rights again. 
	A few weeks later, a replacement for Robot1 arrived. 
	The replacement is also called Robot1. 
	The new robot arrived neither configured nor tested for the production. 
	After carefully testing Robot1, Robot1 has been given back the host attributes for the other security invariants. 
	Despite the ACL entry of Robot2, when Robot1 was added to the network, because of its missing @{const Care} attribute, 
	it was not given automatically access to Robot2. 
	This prevented that Robot1 would accidentally impact Robot2 without being fully configured. 
	In our scenario, once Robot1 will be fully configured, tested, and verified, it will be given the @{const Care} attribute back. 
	
	In general, this design choice of the invariant template prevents that a newly added host may 
	inherit access rights due to stale entries in access lists. 
	At the same time, it does not force administrators to clean up their access lists because a host 
	may only be removed temporarily and wants to be given back its access rights later on. 
	Note that managing access lists scales quadratically in the number of hosts. 
	In contrast, the @{const Care} attribute can be considered as a Boolean flag which allows to 
	temporarily enable or disable the access rights of a host locally without touching the carefully 
	constructed access lists of other hosts. 
	It also prevents that new hosts which have the name of hosts removed long ago (but where stale 
	access rights were not cleaned up) accidentally inherit their access rights. 
\<close>
end


(*TODO: dependability*)


text\<open>Hierarchy of fab robots:
  The production line is designed according to a strict command hierarchy. 
	On top of the hierarchy are control terminals which allow a human operator to intervene and supervise the production process. 
	On the level below, one distinguishes between supervision devices and control devices. 
	The watchdog is a typical supervision device whereas the mission control devices are control devices. 
	Directly below the control devices are the robots. 
	This is the structure that is necessary for the example. 
	However, the company defined a few more sub-departments for future use. 
	The full domain hierarchy tree is visualized below. 
\<close>
text\<open>
  Apart from the watchdog, only the following linear part of the tree is used: 
  \<open>''Robots'' \<sqsubseteq> ''ControlDevices'' \<sqsubseteq> ''ControlTerminal''\<close>.
	Because the watchdog is in a different domain, it needs a trust level of $1$ to access the robots it is monitoring.\<close>
context begin
  private definition "DomainHierarchy_host_attributes \<equiv>
                [(''MissionControl1'',
                    DN (''ControlTerminal''--''ControlDevices''--Leaf, 0)),
                 (''MissionControl2'',
                    DN (''ControlTerminal''--''ControlDevices''--Leaf, 0)),
                 (''Watchdog'',
                    DN (''ControlTerminal''--''Supervision''--Leaf, 1)),
                 (''Robot1'',
                    DN (''ControlTerminal''--''ControlDevices''--''Robots''--Leaf, 0)),
                 (''Robot2'',
                    DN (''ControlTerminal''--''ControlDevices''--''Robots''--Leaf, 0)),
                 (''AdminPc'',
                    DN (''ControlTerminal''--Leaf, 0))
                 ]"
  private lemma "dom (map_of DomainHierarchy_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: DomainHierarchy_host_attributes_def policy_def)

  lemma "DomainHierarchyNG_sanity_check_config
    (map snd DomainHierarchy_host_attributes)
        (
        Department ''ControlTerminal'' [
          Department ''ControlDevices'' [
            Department ''Robots'' [],
            Department ''OtherStuff'' [],
            Department ''ThirdSubDomain'' []
          ],
          Department ''Supervision'' [
            Department ''S1'' [],
            Department ''S2'' []
          ]
        ])" by eval

  definition "Control_hierarchy_m \<equiv> new_configured_list_SecurityInvariant
                                    SINVAR_LIB_DomainHierarchyNG
                                    \<lparr> node_properties = map_of DomainHierarchy_host_attributes \<rparr>
                                    ''Production device hierarchy''"
end


text\<open>Sensor Gateway: 
  The sensors should not communicate among each other; all accesses must be mediated by the sensor sink.\<close>
context begin
  private definition "PolEnforcePoint_host_attributes \<equiv>
                [''SensorSink'' \<mapsto> PolEnforcePoint,
                 ''PresenceSensor'' \<mapsto> DomainMember,
                 ''Webcam'' \<mapsto> DomainMember,
                 ''TempSensor'' \<mapsto> DomainMember,
                 ''FireSensor'' \<mapsto> DomainMember
                 ]"
  private lemma "dom PolEnforcePoint_host_attributes \<subseteq> set (nodesL policy)"
    by(simp add: PolEnforcePoint_host_attributes_def policy_def)
  definition "PolEnforcePoint_m \<equiv> new_configured_list_SecurityInvariant
                                  SINVAR_LIB_PolEnforcePointExtended
                                    \<lparr> node_properties = PolEnforcePoint_host_attributes \<rparr>
                                  ''sensor slaves''"
end


text\<open>Production Robots are an information sink:
  The actual control program of the robots is a corporate trade secret. 
	The control commands must not leave the robots. 
	Therefore, they are declared information sinks. 
	In addition, the control command must not leave the mission control devices. 
	However, the two devices could possibly interact to synchronize and they must send their commands to the robots. 
	Therefore, they are labeled as sink pools.\<close>
context begin
  private definition "SinkRobots_host_attributes \<equiv>
                [''MissionControl1'' \<mapsto> SinkPool,
                 ''MissionControl2'' \<mapsto> SinkPool,
                 ''Robot1'' \<mapsto> Sink,
                 ''Robot2'' \<mapsto> Sink
                 ]"
  private lemma "dom SinkRobots_host_attributes \<subseteq> set (nodesL policy)"
    by(simp add: SinkRobots_host_attributes_def policy_def)
  definition "SinkRobots_m \<equiv> new_configured_list_SecurityInvariant
                                  SINVAR_LIB_Sink
                                    \<lparr> node_properties = SinkRobots_host_attributes \<rparr>
                              ''non-leaking production units''"
end

text\<open>Subnet of the fab:
  The sensors, including their sink and statistics server are located in their own subnet and must 
  not be accessible from elsewhere. 
	Also, the administrator's PC is in its own subnet. 
	The production units (mission control and robots) are already isolated by the DomainHierarchy 
  and are not added to a subnet explicitly.\<close>
context begin
  private definition "Subnets_host_attributes \<equiv>
                [''Statistics'' \<mapsto> Subnet 1,
                 ''SensorSink'' \<mapsto> Subnet 1,
                 ''PresenceSensor'' \<mapsto> Subnet 1,
                 ''Webcam'' \<mapsto> Subnet 1,
                 ''TempSensor'' \<mapsto> Subnet 1,
                 ''FireSensor'' \<mapsto> Subnet 1,
                 ''AdminPc'' \<mapsto> Subnet 4
                 ]"
  private lemma "dom Subnets_host_attributes \<subseteq> set (nodesL policy)"
    by(simp add: Subnets_host_attributes_def policy_def)
  definition "Subnets_m \<equiv> new_configured_list_SecurityInvariant
                                  SINVAR_LIB_Subnets
                                    \<lparr> node_properties = Subnets_host_attributes \<rparr>
                           ''network segmentation''"
end


text\<open>Access Gateway for the Statistics server:
  The statistics server is further protected from external accesses. 
	Another, smaller subnet is defined with the only member being the statistics server. 
	The only way it may be accessed is via that sensor sink.\<close>
context begin
  private definition "SubnetsInGW_host_attributes \<equiv>
                [''Statistics'' \<mapsto> Member,
                 ''SensorSink'' \<mapsto> InboundGateway
                 ]"
  private lemma "dom SubnetsInGW_host_attributes \<subseteq> set (nodesL policy)"
    by(simp add: SubnetsInGW_host_attributes_def policy_def)
  definition "SubnetsInGW_m \<equiv> new_configured_list_SecurityInvariant
                                  SINVAR_LIB_SubnetsInGW
                                    \<lparr> node_properties = SubnetsInGW_host_attributes \<rparr>
                               ''Protectting statistics srv''"
end


text\<open>NonInterference (for the sake of example):
	The fire sensor is managed by an external company and has a built-in GSM module to call the fire fighters in case of an emergency. 
	This additional, out-of-band connectivity is not modeled. 
	However, the contract defines that the company's administrator must not interfere in any way with the fire sensor.\<close>
context begin
  private definition "NonInterference_host_attributes \<equiv>
                [''Statistics'' \<mapsto> Unrelated,
                 ''SensorSink'' \<mapsto> Unrelated,
                 ''PresenceSensor'' \<mapsto> Unrelated,
                 ''Webcam'' \<mapsto> Unrelated,
                 ''TempSensor'' \<mapsto> Unrelated,
                 ''FireSensor'' \<mapsto> Interfering, \<comment> \<open>(!)\<close>
                 ''MissionControl1'' \<mapsto> Unrelated,
                 ''MissionControl2'' \<mapsto> Unrelated,
                 ''Watchdog'' \<mapsto> Unrelated,
                 ''Robot1'' \<mapsto> Unrelated,
                 ''Robot2'' \<mapsto> Unrelated,
                 ''AdminPc'' \<mapsto> Interfering, \<comment> \<open>(!)\<close>
                 ''INET'' \<mapsto> Unrelated
                 ]"
  private lemma "dom NonInterference_host_attributes \<subseteq> set (nodesL policy)"
    by(simp add: NonInterference_host_attributes_def policy_def)
  definition "NonInterference_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_NonInterference
                                    \<lparr> node_properties = NonInterference_host_attributes \<rparr>
                                   ''for the sake of an acdemic example!''"
end
text\<open>As discussed, this invariant is very strict and rather theoretical. 
    It is not ENF-structured and may produce an exponential number of offending flows. 
    Therefore, we exclude it by default from our algorithms.\<close>




definition "invariants \<equiv> [BLP_privacy_m, BLP_tradesecrets_m, BLP_employee_export_m,
                          ACL_bot2_m, Control_hierarchy_m,
                          PolEnforcePoint_m, SinkRobots_m, Subnets_m, SubnetsInGW_m]"
text\<open>We have excluded @{const NonInterference_m} because of its infeasible runtime.\<close>

lemma "length invariants = 9" by eval



subsection\<open>Policy Verification\<close>


text\<open>
The given policy fulfills all the specified security invariants.
Also with @{const NonInterference_m}, the policy fulfills all security invariants.
\<close>
lemma "all_security_requirements_fulfilled (NonInterference_m#invariants) policy" by eval
ML\<open>
visualize_graph @{context} @{term "invariants"} @{term "policy"};
\<close>


definition make_policy :: "('a SecurityInvariant) list \<Rightarrow> 'a list \<Rightarrow> 'a list_graph" where
  "make_policy sinvars Vs \<equiv> generate_valid_topology sinvars \<lparr>nodesL = Vs, edgesL = List.product Vs Vs \<rparr>"


definition make_policy_efficient :: "('a SecurityInvariant) list \<Rightarrow> 'a list \<Rightarrow> 'a list_graph" where
  "make_policy_efficient sinvars Vs \<equiv> generate_valid_topology_some sinvars \<lparr>nodesL = Vs, edgesL = List.product Vs Vs \<rparr>"


text\<open>
The question, ``how good are the specified security invariants?'' remains. 
Therefore, we use the algorithm from @{const make_policy} to generate a policy. 
Then, we will compare our policy with the automatically generated one. 
If we exclude the NonInterference invariant from the policy construction, we know that the resulting 
policy must be maximal. 
Therefore, the computed policy reflects the view of the specified security invariants. 
By maximality of the computed policy and monotonicity, we know that our manually specified policy 
must be a subset of the computed policy. 
This allows to compare the manually-specified policy to the policy implied by the security invariants: 
If there are too many flows which are allowed according to the computed policy but which are not in 
our manually-specified policy, we can conclude that our security invariants are not strict enough. 
\<close>
value[code] "make_policy invariants (nodesL policy)" (*15s without NonInterference*)
lemma "make_policy invariants (nodesL policy) = 
   \<lparr>nodesL =
    [''Statistics'', ''SensorSink'', ''PresenceSensor'', ''Webcam'', ''TempSensor'',
     ''FireSensor'', ''MissionControl1'', ''MissionControl2'', ''Watchdog'', ''Robot1'',
     ''Robot2'', ''AdminPc'', ''INET''],
    edgesL =
      [(''Statistics'', ''Statistics''), (''SensorSink'', ''Statistics''),
       (''SensorSink'', ''SensorSink''), (''SensorSink'', ''Webcam''),
       (''PresenceSensor'', ''SensorSink''), (''PresenceSensor'', ''PresenceSensor''),
       (''Webcam'', ''SensorSink''), (''Webcam'', ''Webcam''),
       (''TempSensor'', ''SensorSink''), (''TempSensor'', ''TempSensor''),
       (''TempSensor'', ''INET''), (''FireSensor'', ''SensorSink''),
       (''FireSensor'', ''FireSensor''), (''FireSensor'', ''INET''),
       (''MissionControl1'', ''MissionControl1''),
       (''MissionControl1'', ''MissionControl2''), (''MissionControl1'', ''Robot1''),
       (''MissionControl1'', ''Robot2''), (''MissionControl2'', ''MissionControl2''),
       (''MissionControl2'', ''Robot2''), (''Watchdog'', ''MissionControl1''),
       (''Watchdog'', ''MissionControl2''), (''Watchdog'', ''Watchdog''),
       (''Watchdog'', ''Robot1''), (''Watchdog'', ''Robot2''), (''Watchdog'', ''INET''),
       (''Robot1'', ''Robot1''), (''Robot2'', ''Robot2''), (''AdminPc'', ''MissionControl1''),
       (''AdminPc'', ''MissionControl2''), (''AdminPc'', ''Watchdog''),
       (''AdminPc'', ''Robot1''), (''AdminPc'', ''AdminPc''), (''AdminPc'', ''INET''),
       (''INET'', ''INET'')]\<rparr>" by eval

text\<open>Additional flows which would be allowed but which are not in the policy\<close>
lemma  "set [e \<leftarrow> edgesL (make_policy invariants (nodesL policy)). e \<notin> set (edgesL policy)] = 
        set [(v,v). v \<leftarrow> (nodesL policy)] \<union>
        set [(''SensorSink'', ''Webcam''),
             (''TempSensor'', ''INET''),
             (''FireSensor'', ''INET''),
             (''MissionControl1'', ''MissionControl2''),
             (''Watchdog'', ''MissionControl1''),
             (''Watchdog'', ''MissionControl2''),
             (''Watchdog'', ''INET''),
             (''AdminPc'', ''Watchdog''),
             (''AdminPc'', ''Robot1''),
             (''AdminPc'', ''INET'')]" by eval
text\<open>
We visualize this comparison below. 
The solid edges correspond to the manually-specified policy. 
The dotted edges correspond to the flow which would be additionally permitted by the computed policy.\<close>
ML_val\<open>
visualize_edges @{context} @{term "edgesL policy"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term "[e \<leftarrow> edgesL (make_policy invariants (nodesL policy)).
                e \<notin> set (edgesL policy)]"})] "";
\<close>

text\<open>
The comparison reveals that the following flows would be additionally permitted. 
We will discuss whether this is acceptable or if the additional permission indicates that 
we probably forgot to specify an additional security goal. 


  \<^item> All reflexive flows, i.e. all host can communicate with themselves. 
    Since each host in the policy corresponds to one physical entity, there is no need to explicitly 
    prohibit or allow in-host communication. 
  \<^item> The @{term "''SensorSink''"} may access the @{term "''Webcam''"}. 
    Both share the same security level, there is no problem with this possible information flow. 
    Technically, a bi-directional connection may even be desirable, since this allows the sensor 
    sink to influence the video stream, e.g. request a lower bit rate if it is overloaded. 
  \<^item> Both the @{term "''TempSensor''"} and the @{term "''FireSensor''"} may access the Internet. 
    No security levels or other privacy concerns are specified for them. 
    This may raise the question whether this data is indeed public. 
    It is up to the company to decide that this data should also be considered confidential. 
  \<^item> @{term "''MissionControl1''"} can send to @{term "''MissionControl2''"}. 
    This may be desirable since it was stated anyway that the two may need to cooperate. 
    Note that the opposite direction is definitely prohibited since the critical and secret 
    production step only known to @{term "''MissionControl2''"} must not leak. 
  \<^item> The @{term "''Watchdog''"} may access @{term "''MissionControl1''"}, 
    @{term "''MissionControl2''"}, and the @{term "''INET''"}. 
    While it may be acceptable that the watchdog which monitors the robots may also access the control devices, 
    it should raise a concern that the watchdog may freely send data to the Internet. 
    Indeed, the watchdog can access devices which have corporate trade secrets stored but it was 
    never specified that the watchdog should be treated confidentially. 
    Note that in the current setting, the trade secrets will never leave the robots. 
    This is because the policy only specifies a unidirectional information flow from the watchdog 
    to the robots; the robots will not leak any information back to the watchdog. 
    This also means that the watchdog cannot actually monitor the robots. 
    Later, when implementing the scenario, we will see that the simple, hand-waving argument 
    ``the watchdog connects to the robots and the robots send back their data over the established connection'' 
    will not work because of this possible information leak. 
  \<^item> The @{term "''AdminPc''"} is allowed to access the @{term "''Watchdog''"}, 
    @{term "''Robot1''"}, and the @{term "''INET''"}. 
    Since this machine is trusted anyway, the company does not see a problem with this. 
\<close>

text\<open>without @{const NonInterference_m}\<close>
lemma "all_security_requirements_fulfilled invariants (make_policy invariants (nodesL policy))" by eval




text\<open>Side note: what if we exclude subnets?\<close>
ML_val \<open>
visualize_edges @{context} @{term "edgesL (make_policy invariants (nodesL policy))"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term \<open>[e \<leftarrow> edgesL (make_policy [BLP_privacy_m, BLP_tradesecrets_m, BLP_employee_export_m,
                           ACL_bot2_m, Control_hierarchy_m,
                           PolEnforcePoint_m, SinkRobots_m, \<^cancel>\<open>Subnets_m,\<close> SubnetsInGW_m]  (nodesL policy)).
                e \<notin> set (edgesL (make_policy invariants (nodesL policy)))]\<close>})] ""; 
\<close>


subsection\<open>About NonInterference\<close>
text\<open>
The NonInterference template was deliberately selected for our scenario as one of the 
`problematic' and rather theoretical invariants. 
Our framework allows to specify almost arbitrary invariant templates. 
We concluded that all non-ENF-structured invariants which may produce an exponential 
number of offending flows are problematic for practical use. 
This includes ``Comm. With'' (@{file \<open>../Security_Invariants/SINVAR_ACLcommunicateWith.thy\<close>}), 
``Not Comm. With'' (@{file \<open>../Security_Invariants/SINVAR_ACLnotCommunicateWith.thy\<close>}), 
Dependability (@{file \<open>../Security_Invariants/SINVAR_Dependability.thy\<close>}), 
and NonInterference (@{file \<open>../Security_Invariants/SINVAR_NonInterference.thy\<close>}).
In this section, we discuss the consequences of the NonInterference invariant for automated policy construction. 
We will conclude that, though we can solve all technical challenges, said invariants are 
---due to their inherent ambiguity--- not very well suited for automated policy construction.\<close>


text\<open>
The computed maximum policy does not fulfill invariant 10 (NonInterference). 
This is because the fire sensor and the administrator's PC may be indirectly connected over the Internet. 
\<close>
lemma "\<not> all_security_requirements_fulfilled (NonInterference_m#invariants) (make_policy invariants (nodesL policy))" by eval


text\<open>
Since the NonInterference template may produce an exponential number of offending flows, 
it is infeasible to try our automated policy construction algorithm with it. 
We have tried to do so on a machine with 128GB of memory but after a few minutes, the computation ran out of memory. 
On said machine, we were unable to run our policy construction algorithm with the NonInterference invariant for more that five hosts. 

Algorithm @{const make_policy_efficient} improves the policy construction algorithm. 
The new algorithm instantly returns a solution for this scenario with a very small memory footprint. 
\<close>

text\<open>The more efficient algorithm does not need to construct the complete set of offending flows\<close>
value[code] "make_policy_efficient (invariants@[NonInterference_m]) (nodesL policy)"
value[code] "make_policy_efficient (NonInterference_m#invariants) (nodesL policy)"

(* only try this if you have more than 128GB ram. Let me know if you can finish the computation ;-)
   I could not do more than 5 nodes on a 128gb machine.
value[code] "make_policy (NonInterference_m#invariants) (nodesL policy)"
   NonInterference_m produces exponentially many offending flows
*)

lemma "make_policy_efficient (invariants@[NonInterference_m]) (nodesL policy) = 
       make_policy_efficient (NonInterference_m#invariants) (nodesL policy)" by eval

text\<open>But @{const NonInterference_m} insists on removing something, which would not be necessary.\<close>
lemma "make_policy invariants (nodesL policy) \<noteq> make_policy_efficient (NonInterference_m#invariants) (nodesL policy)" by eval

lemma "set (edgesL (make_policy_efficient (NonInterference_m#invariants) (nodesL policy)))
       \<subseteq>
       set (edgesL (make_policy invariants (nodesL policy)))" by eval

text\<open>This is what it wants to be gone.\<close> (*may take some minutes*)
lemma "[e \<leftarrow> edgesL (make_policy invariants (nodesL policy)).
                e \<notin> set (edgesL (make_policy_efficient (NonInterference_m#invariants) (nodesL policy)))] =
       [(''AdminPc'', ''MissionControl1''), (''AdminPc'', ''MissionControl2''),
        (''AdminPc'', ''Watchdog''), (''AdminPc'', ''Robot1''), (''AdminPc'', ''INET'')]"
  by eval

lemma "[e \<leftarrow> edgesL (make_policy invariants (nodesL policy)).
               e \<notin> set (edgesL (make_policy_efficient (NonInterference_m#invariants) (nodesL policy)))] =
       [e \<leftarrow> edgesL (make_policy invariants (nodesL policy)). fst e = ''AdminPc'' \<and> snd e \<noteq> ''AdminPc'']"
  by eval
ML_val\<open>
visualize_edges @{context} @{term "edgesL policy"}
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term "[e \<leftarrow> edgesL (make_policy invariants (nodesL policy)).
                e \<notin> set (edgesL (make_policy_efficient (NonInterference_m#invariants) (nodesL policy)))]"})] ""; 
\<close>

text\<open>
However, it is an inherent property of the NonInterferance template (and similar templates), 
that the set of offending flows is not uniquely defined. 
Consequently, since several solutions are possible, even our new algorithm may not be able to compute one maximum solution. 
It would be possible to construct some maximal solution, however, this would require to 
enumerate all offending flows, which is infeasible. 
Therefore, our algorithm can only return some (valid but probably not maximal) solution for non-END-structured invariants. 

As a human, we know the scenario and the intention behind the policy. 
Probably, the best solution for policy construction with the NonInterferance property would be to 
restrict outgoing edges from the fire sensor. 
If we consider the policy above which was constructed without NonInterference, if we cut off 
the fire sensor from the Internet, we get a valid policy for the NonInterference property. 
Unfortunately, an algorithm does not have the information of which flows we would like to cut first 
and the algorithm needs to make some choice. 
In this example, the algorithm decides to isolate the administrator's PC from the rest of the world. 
This is also a valid solution. 
We could change the order of the elements to tell the algorithm which edges we would rather sacrifice than others. 
This may help but requires some additional input. 
The author personally prefers to construct only maximum policies with $\Phi$-structured invariants 
and afterwards fix the policy manually for the remaining non-$\Phi$-structured invariants. 
Though our new algorithm gives better results and returns instantly, the very nature of invariant 
templates with an exponential number of offending flows tells that these invariants are problematic 
for automated policy construction. 
\<close>



subsection\<open>Stateful Implementation\<close>
text\<open>
In this section, we will implement the policy and deploy it in a network. 
As the scenario description stated, all devices in the production line should establish 
stateful connections which allows -- once the connection is established -- packets to travel in both directions. 
This is necessary for the watchdog, the mission control devices, and the administrator's PC to actually perform their task. 

We compute a stateful implementation. 
Below, the stateful implementation is visualized. 
It consists of the policy as visualized above. 
In addition, dotted edges visualize where answer packets are permitted. 
\<close>
definition "stateful_policy = generate_valid_stateful_policy_IFSACS policy invariants"
lemma "stateful_policy =
 \<lparr>hostsL = nodesL policy,
    flows_fixL = edgesL policy,
    flows_stateL =
      [(''Webcam'', ''SensorSink''),
       (''SensorSink'', ''Statistics'')]\<rparr>" by eval

ML_val\<open>
visualize_edges @{context} @{term "flows_fixL stateful_policy"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL stateful_policy"})] ""; 
\<close>

text\<open>As can be seen, only the flows @{term "(''Webcam'', ''SensorSink'')"} 
and @{term "(''SensorSink'', ''Statistics'')"} are allowed to be stateful. 
This setup cannot be practically deployed because the watchdog, the mission control devices, 
and the administrator's PC also need to set up stateful connections. 
Previous section's discussion already hinted at this problem. 
The reason why the desired stateful connections are not permitted is due to information leakage. 
In detail: @{const BLP_tradesecrets_m} and @{const SinkRobots_m} are responsible. 
Both invariants prevent that any data leaves the robots and the mission control devices. 
To verify this suspicion, the two invariants are removed and the stateful flows are computed again. 
The result visualized is below.\<close>

lemma "generate_valid_stateful_policy_IFSACS policy
      [BLP_privacy_m, BLP_employee_export_m,
       ACL_bot2_m, Control_hierarchy_m, 
       PolEnforcePoint_m,  Subnets_m, SubnetsInGW_m] =
 \<lparr>hostsL = nodesL policy,
    flows_fixL = edgesL policy,
    flows_stateL =
      [(''Webcam'', ''SensorSink''),
       (''SensorSink'', ''Statistics''),
       (''MissionControl1'', ''Robot1''),
       (''MissionControl1'', ''Robot2''),
       (''MissionControl2'', ''Robot2''),
       (''AdminPc'', ''MissionControl2''),
       (''AdminPc'', ''MissionControl1''),
       (''Watchdog'', ''Robot1''),
       (''Watchdog'', ''Robot2'')]\<rparr>" by eval

text\<open>This stateful policy could be transformed into a fully functional implementation. 
However, there would be no security invariants specified which protect the trade secrets. 
Without those two invariants, the invariant specification is too permissive. 
For example, if we recompute the maximum policy, we can see that the robots and mission control can leak any data to the Internet. 
Even without the maximum policy, in the stateful policy above, it can be seen that 
MissionControl1 can exfiltrate information from robot 2, once it establishes a stateful connection.\<close>


text\<open>Without the two invariants, the security goals are way too permissive!\<close>
lemma "set [e \<leftarrow> edgesL (make_policy [BLP_privacy_m, BLP_employee_export_m,
       ACL_bot2_m, Control_hierarchy_m, 
       PolEnforcePoint_m,  Subnets_m, SubnetsInGW_m] (nodesL policy)). e \<notin> set (edgesL policy)] =
        set [(v,v). v \<leftarrow> (nodesL policy)] \<union>
        set [(''SensorSink'', ''Webcam''),
             (''TempSensor'', ''INET''),
             (''FireSensor'', ''INET''),
             (''MissionControl1'', ''MissionControl2''),
             (''Watchdog'', ''MissionControl1''),
             (''Watchdog'', ''MissionControl2''),
             (''Watchdog'', ''INET''),
             (''AdminPc'', ''Watchdog''),
             (''AdminPc'', ''Robot1''),
             (''AdminPc'', ''INET'')] \<union>
        set [(''MissionControl1'', ''INET''),
             (''MissionControl2'', ''MissionControl1''),
             (''MissionControl2'', ''Robot1''),
             (''MissionControl2'', ''INET''),
             (''Robot1'', ''INET''),
             (''Robot2'', ''Robot1''),
             (''Robot2'', ''INET'')]" by eval


ML_val\<open>
visualize_edges @{context} @{term "flows_fixL (generate_valid_stateful_policy_IFSACS policy [BLP_privacy_m,  BLP_employee_export_m,
                          ACL_bot2_m, Control_hierarchy_m, 
                          PolEnforcePoint_m,  Subnets_m, SubnetsInGW_m])"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
      @{term "flows_stateL (generate_valid_stateful_policy_IFSACS policy [BLP_privacy_m,  BLP_employee_export_m,
                          ACL_bot2_m, Control_hierarchy_m, 
                          PolEnforcePoint_m,  Subnets_m, SubnetsInGW_m])"})] "";
\<close>



text\<open>
Therefore, the two invariants are not removed but repaired. 
The goal is to allow the watchdog, administrator's pc, and the mission control devices to set up stateful connections without leaking corporate trade secrets to the outside. 

First, we repair @{const BLP_tradesecrets_m}.
On the one hand, the watchdog should be able to send packets both @{term "''Robot1''"} and @{term "''Robot2''"}. 
@{term "''Robot1''"} has a security level of @{term "1::security_level"} and 
@{term "''Robot2''"} has a security level of @{term "2::security_level"}. 
Consequently, in order to be allowed to send packets to both, @{term "''Watchdog''"} must 
have a security level not higher than @{term "1::security_level"}. 
On the other hand, the @{term "''Watchdog''"} should be able to receive packets from both. 
By the same argument, it must have a security level of at least @{term "2::security_level"}. 
Consequently, it is impossible to express the desired meaning in the BLP basic template. 
There are only two solutions to the problem: Either the company installs one watchdog 
for each security level, or the watchdog must be trusted. 
We decide for the latter option and upgrade the template to the Bell LaPadula model with trust. 
We define the watchdog as trusted with a security level of @{term "1::security_level"}. 
This means, it can receive packets from and send packets to both robots but it cannot leak information to the outside world. 
We do the same for the @{term "''AdminPc''"}.

Then, we repair @{const SinkRobots_m}. 
We realize that the following set set of hosts forms one big pool of devices which must all 
somehow interact but where information must not leave the pool: 
The administrator's PC, the mission control devices, the robots, and the watchdog. 
Therefore, all those devices are configured to be in the same @{const SinkPool}. 
\<close>



definition "invariants_tuned \<equiv> [BLP_privacy_m, BLP_employee_export_m,
               ACL_bot2_m, Control_hierarchy_m, 
               PolEnforcePoint_m, Subnets_m, SubnetsInGW_m,
               new_configured_list_SecurityInvariant SINVAR_LIB_Sink
                 \<lparr> node_properties = [''MissionControl1'' \<mapsto> SinkPool,
                                      ''MissionControl2'' \<mapsto> SinkPool,
                                      ''Robot1'' \<mapsto> SinkPool,
                                      ''Robot2'' \<mapsto> SinkPool,
                                      ''Watchdog'' \<mapsto> SinkPool,
                                      ''AdminPc'' \<mapsto> SinkPool
                                      ] \<rparr>
                 ''non-leaking production units'',
               new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted
                 \<lparr> node_properties = [''MissionControl1'' \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
                                      ''MissionControl2'' \<mapsto> \<lparr> security_level = 2, trusted = False \<rparr>,
                                      ''Robot1'' \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
                                      ''Robot2'' \<mapsto> \<lparr> security_level = 2, trusted = False \<rparr>,
                                      ''Watchdog'' \<mapsto> \<lparr> security_level = 1, trusted = True \<rparr>,
                                        \<comment> \<open>trust because \<open>bot2\<close> must send to it. \<open>security_level\<close> 1 to interact with \<open>bot\<close> 1\<close>
                                      ''AdminPc'' \<mapsto> \<lparr> security_level = 1, trusted = True \<rparr>
                                      ] \<rparr>
                 ''trade secrets''
              ]"

lemma "all_security_requirements_fulfilled invariants_tuned policy" by eval


definition "stateful_policy_tuned = generate_valid_stateful_policy_IFSACS policy invariants_tuned"

text\<open>
The computed stateful policy is visualized below.
\<close>
lemma "stateful_policy_tuned
 =
 \<lparr>hostsL = nodesL policy,
    flows_fixL = edgesL policy,
    flows_stateL =
      [(''Webcam'', ''SensorSink''),
       (''SensorSink'', ''Statistics''),
       (''MissionControl1'', ''Robot1''),
       (''MissionControl2'', ''Robot2''),
       (''AdminPc'', ''MissionControl2''),
       (''AdminPc'', ''MissionControl1''),
       (''Watchdog'', ''Robot1''),
       (''Watchdog'', ''Robot2'')]\<rparr>" by eval

text\<open>We even get a better (i.e. stricter) maximum policy\<close>
lemma "set (edgesL (make_policy invariants_tuned (nodesL policy))) \<subset>
       set (edgesL (make_policy invariants (nodesL policy)))" by eval
lemma "set [e \<leftarrow> edgesL (make_policy invariants_tuned (nodesL policy)). e \<notin> set (edgesL policy)] =
        set [(v,v). v \<leftarrow> (nodesL policy)] \<union>
        set [(''SensorSink'', ''Webcam''),
             (''TempSensor'', ''INET''),
             (''FireSensor'', ''INET''),
             (''MissionControl1'', ''MissionControl2''),
             (''Watchdog'', ''MissionControl1''),
             (''Watchdog'', ''MissionControl2''),
             (''AdminPc'', ''Watchdog''),
             (''AdminPc'', ''Robot1'')]" by eval

text\<open>
It can be seen that all connections which should be stateful are now indeed stateful. 
In addition, it can be seen that MissionControl1 cannot set up a stateful connection to Bot2. 
This is because MissionControl1 was never declared a trusted device and the confidential information 
in MissionControl2 and Robot2 must not leak. 

The improved invariant definition even produces a better (i.e. stricter) maximum policy.\<close>

subsection\<open>Iptables Implementation\<close>

text\<open>firewall -- classical use case\<close>
ML_val\<open>

(*header*)
writeln (*("echo 1 > /proc/sys/net/ipv4/ip_forward"^"\n"^
         "# flush all rules"^"\n"^
         "iptables -F"^"\n"^
         "#default policy for FORWARD chain:"^"\n"^
         "iptables -P FORWARD DROP");*)
         ("*filter\n"^
          ":INPUT ACCEPT [0:0]\n"^
          ":FORWARD ACCEPT [0:0]\n"^
          ":OUTPUT ACCEPT [0:0]");

iterate_edges_ML @{context}  @{term "flows_fixL stateful_policy_tuned"}
  (fn (v1,v2) => writeln ("-A FORWARD -i $"^v1^"_iface -s $"^v1^"_ipv4 -o $"^v2^"_iface -d $"^v2^"_ipv4 -j ACCEPT") )
                         (*("iptables -A FORWARD -i $\\$\\mathit{"^v1^"\\_iface}$ -s $\\$\\mathit{"^
                          v1^"\\_ipv4}$ -o $\\$\\mathit{"^v2^"\\_iface}$ -d $\\$\\mathit{"^v2^"\\_ipv4}$ -j ACCEPT") )*)
  (fn _ => () )
  (fn _ => () );

iterate_edges_ML @{context} @{term "flows_stateL stateful_policy_tuned"}
  (fn (v1,v2) => writeln ("-I FORWARD -m state --state ESTABLISHED -i $"^v2^"_iface -s $"^
                          v2^"_ipv4 -o $"^v1^"_iface -d $"^v1^"_ipv4 -j ACCEPT") )
                          (*("iptables -I FORWARD -m state --state ESTABLISHED -i $\\$\\mathit{"^
                           v2^"\\_iface}$ -s $\\$\\mathit{"^v2^"\\_ipv4}$ -o $\\$\\mathit{"^
                           v1^"\\_iface}$ -d $\\$\\mathit{"^v1^"_ipv4}$ -j ACCEPT # "^v2^" -> "^v1^" (answer)") )*)
  (fn _ => () )
  (fn _ => () );

writeln "COMMIT";
\<close>

text\<open>Using, @{url "https://github.com/diekmann/Iptables_Semantics"}, the iptables ruleset is indeed correct.\<close>

end


