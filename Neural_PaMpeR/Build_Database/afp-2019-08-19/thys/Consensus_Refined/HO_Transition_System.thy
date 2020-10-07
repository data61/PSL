(*<*)
theory HO_Transition_System
imports Heard_Of.HOModel Refinement
begin
(*>*)

subsection \<open>Transition system semantics for HO models\<close>

text \<open>The HO development already defines two trace semantics for algorithms in this model, the
coarse- and fine-grained ones. However, both of these are defined on infinite traces. Since the
semantics of our transition systems are defined on finite traces, we also provide such a semantics
for the HO model. Since we only use refinement for safety properties, the result also extend to
infinite traces (although we do not prove this in Isabelle).\<close>

definition CHO_trans where
"CHO_trans A HOs SHOs coord = 
  {((r, st), (r', st'))|r r' st st'.
      r' = Suc r
      \<and> CSHOnextConfig A r st (HOs r) (SHOs r) (coord r) st'
  }"

definition CHO_to_TS :: 
  "('proc, 'pst, 'msg) CHOAlgorithm 
  \<Rightarrow> (nat \<Rightarrow> 'proc HO)
  \<Rightarrow> (nat \<Rightarrow> 'proc HO)
  \<Rightarrow> (nat \<Rightarrow> 'proc coord) 
  \<Rightarrow> (nat \<times> ('proc \<Rightarrow> 'pst)) TS" 
where
  "CHO_to_TS A HOs SHOs coord \<equiv> \<lparr>
    init = {(0, st)|st. CHOinitConfig A st (coord 0)},
    trans = CHO_trans A HOs SHOs coord
  \<rparr>"


definition get_msgs ::
  "('proc \<Rightarrow> 'proc \<Rightarrow> 'pst \<Rightarrow> 'msg)
  \<Rightarrow> ('proc \<Rightarrow> 'pst)
  \<Rightarrow> 'proc HO
  \<Rightarrow> 'proc HO
  \<Rightarrow> 'proc \<Rightarrow> ('proc \<rightharpoonup> 'msg)set"
where
  "get_msgs snd_f cfg HO SHO \<equiv> \<lambda>p.
   {\<mu>. (\<forall>q. q \<in> HO p \<longleftrightarrow> \<mu> q \<noteq> None)
     \<and> (\<forall>q. q \<in> SHO p \<inter> HO p \<longrightarrow> \<mu> q = Some (snd_f q p (cfg q)))}"

definition CSHO_trans_alt
  :: 
  "(nat \<Rightarrow> 'proc \<Rightarrow> 'proc \<Rightarrow> 'pst \<Rightarrow> 'msg)
  \<Rightarrow> (nat \<Rightarrow> 'proc \<Rightarrow> 'pst \<Rightarrow> ('proc \<rightharpoonup> 'msg) \<Rightarrow> 'proc \<Rightarrow> 'pst \<Rightarrow> bool)
  \<Rightarrow> (nat \<Rightarrow> 'proc HO)
  \<Rightarrow> (nat \<Rightarrow> 'proc HO)
  \<Rightarrow> (nat \<Rightarrow> 'proc \<Rightarrow> 'proc)
  \<Rightarrow> ((nat \<times> ('proc \<Rightarrow> 'pst)) \<times> (nat \<times> ('proc \<Rightarrow> 'pst)))set"
where
  "CSHO_trans_alt snd_f nxt_st HOs SHOs coords \<equiv>
    \<Union>r \<mu>. {((r, cfg), (Suc r, cfg'))|cfg cfg'. \<forall>p.
      \<mu> p \<in> (get_msgs (snd_f r) cfg (HOs r) (SHOs r) p)
      \<and> (\<forall>p. nxt_st r p (cfg p) (\<mu> p) (coords r p) (cfg' p))
    }"

lemma CHO_trans_alt:
  "CHO_trans A HOs SHOs coords = CSHO_trans_alt (sendMsg A) (CnextState A) HOs SHOs coords"
  apply(rule equalityI)
   apply(force simp add: CHO_trans_def CSHO_trans_alt_def CSHOnextConfig_def SHOmsgVectors_def 
    get_msgs_def restrict_map_def map_add_def choice_iff)
  apply(force simp add: CHO_trans_def CSHO_trans_alt_def CSHOnextConfig_def SHOmsgVectors_def 
    get_msgs_def restrict_map_def map_add_def)
  done

definition K where
  "K y \<equiv> \<lambda>x. y"

lemma SHOmsgVectors_get_msgs:
  "SHOmsgVectors A r p cfg HOp SHOp = get_msgs (sendMsg A r) cfg (K HOp) (K SHOp) p"
  by(auto simp add: SHOmsgVectors_def get_msgs_def K_def)

lemma get_msgs_K:
  "get_msgs snd_f cfg (K (HOs r p)) (K (SHOs r p)) p
  = get_msgs snd_f cfg (HOs r) (SHOs r) p"
  by(auto simp add: get_msgs_def K_def)

lemma CSHORun_get_msgs:
  "CSHORun (A ::  ('proc, 'pst, 'msg) CHOAlgorithm) rho HOs SHOs coords = (
     CHOinitConfig A (rho 0) (coords 0)
   \<and> (\<forall>r. \<exists>\<mu>. 
    (\<forall>p.
      \<mu> p \<in> get_msgs (sendMsg A r) (rho r) (HOs r) (SHOs r) p
      \<and> CnextState A r p (rho r p) (\<mu> p) (coords (Suc r) p) (rho (Suc r) p))))"
   by(auto simp add: CSHORun_def CSHOnextConfig_def SHOmsgVectors_get_msgs nextState_def get_msgs_K
     Bex_def choice_iff)

lemmas CSHORun_step = CSHORun_get_msgs[THEN iffD1, THEN conjunct2]

lemma get_msgs_dom:
  "msgs \<in> get_msgs send s HOs SHOs p \<Longrightarrow> dom msgs = HOs p"
  by(auto simp add: get_msgs_def)

lemma get_msgs_benign:
  "get_msgs snd_f cfg HOs HOs p = { (Some o (\<lambda>q. (snd_f q p (cfg q)))) |` (HOs p)}"
  by(auto simp add: get_msgs_def restrict_map_def)

end
