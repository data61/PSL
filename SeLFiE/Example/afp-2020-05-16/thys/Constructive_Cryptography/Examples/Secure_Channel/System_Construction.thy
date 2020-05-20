section \<open>Examples\<close>

theory System_Construction imports
  "../../Constructive_Cryptography"
begin

subsection \<open>Random oracle resource\<close>

locale rorc =
  fixes range :: "'r set"
begin

fun rnd_oracle :: "('m \<Rightarrow> 'r option, 'm, 'r) oracle'" where
  "rnd_oracle f m = (case f m of
    (Some  r) \<Rightarrow> return_spmf (r, f)
  | None      \<Rightarrow> do { 
      r \<leftarrow> spmf_of_set (range); 
      return_spmf (r, f(m := Some r))})"

definition "res = RES (rnd_oracle \<oplus>\<^sub>O rnd_oracle) Map.empty"

end

subsection \<open>Key resource\<close>

locale key =
  fixes key_gen :: "'k spmf"
begin

fun key_oracle :: "('k option, unit, 'k) oracle'" where
  "key_oracle None     () =  do { k \<leftarrow> key_gen; return_spmf (k, Some k)}"
| "key_oracle (Some x) () =  return_spmf (x, Some x)"

definition "res = RES (key_oracle \<oplus>\<^sub>O key_oracle) None"

end


subsection \<open>Channel resource\<close>

datatype 'a cstate = Void | Fail | Store 'a | Collect 'a

datatype 'a aquery = Look | ForwardOrEdit (forward_or_edit: 'a) | Drop
type_synonym 'a insec_query = "'a option aquery"
type_synonym auth_query = "unit aquery"

consts Forward :: "'a aquery"
abbreviation Forward_auth :: auth_query where "Forward_auth \<equiv> ForwardOrEdit ()"
abbreviation Forward_insec :: "'a insec_query" where "Forward_insec \<equiv> ForwardOrEdit None"
abbreviation Edit :: "'a \<Rightarrow> 'a insec_query" where "Edit m \<equiv> ForwardOrEdit (Some m)"
adhoc_overloading Forward Forward_auth
adhoc_overloading Forward Forward_insec

translations
  (logic) "CONST Forward" <= (logic) "CONST ForwardOrEdit (CONST None)"
  (logic) "CONST Forward" <= (logic) "CONST ForwardOrEdit (CONST Product_Type.Unity)"
  (type) "auth_query" <= (type) "unit aquery"
  (type) "'a insec_query" <= (type) "'a option aquery"

subsubsection \<open>Generic channel\<close>

locale channel =
  fixes side_oracle :: "('m cstate, 'a, 'b option) oracle'"
begin

fun send_oracle :: "('m cstate, 'm, unit) oracle'" where
  "send_oracle Void m = return_spmf ((), Store m)"
| "send_oracle s    m = return_spmf ((), s)"

fun recv_oracle :: "('m cstate, unit, 'm option) oracle'" where
  "recv_oracle (Collect m) () = return_spmf (Some m, Fail)"
| "recv_oracle s           () = return_spmf (None, s)"

definition res :: "('a + 'm + unit, 'b option + unit + 'm option) resource" where
  "res \<equiv> RES (side_oracle \<oplus>\<^sub>O send_oracle \<oplus>\<^sub>O recv_oracle) Void"

end

subsubsection \<open>Insecure channel\<close>

locale insec_channel
begin

fun insec_oracle :: "('m cstate, 'm insec_query, 'm option) oracle'" where
  "insec_oracle Void      (Edit m') = return_spmf (None, Collect m')"
| "insec_oracle (Store m) (Edit m') = return_spmf (None, Collect m')"
| "insec_oracle (Store m) Forward   = return_spmf (None, Collect m)"
| "insec_oracle (Store m) Drop      = return_spmf (None, Fail)"
| "insec_oracle (Store m) Look      = return_spmf (Some m, Store m)"
| "insec_oracle s         _         = return_spmf (None, s)"

sublocale channel insec_oracle .

end

subsubsection \<open>Authenticated channel\<close>

locale auth_channel
begin

fun auth_oracle :: "('m cstate, auth_query, 'm option) oracle'" where
  "auth_oracle (Store m) Forward = return_spmf (None, Collect m)"
| "auth_oracle (Store m) Drop    = return_spmf (None, Fail)"
| "auth_oracle (Store m) Look    = return_spmf (Some m, Store m)"
| "auth_oracle s         _       = return_spmf (None, s)"

sublocale channel auth_oracle .

end

fun insec_query_of :: "auth_query \<Rightarrow> 'm insec_query" where
  "insec_query_of Forward = Forward"
| "insec_query_of Drop = Drop"
| "insec_query_of Look = Look"

abbreviation (input) auth_response_of :: "('mac \<times> 'm) option \<Rightarrow> 'm option" 
  where "auth_response_of \<equiv> map_option snd"

abbreviation insec_auth_wiring :: "(auth_query, 'm option, ('mac \<times> 'm) insec_query, ('mac \<times> 'm) option) wiring"
  where "insec_auth_wiring \<equiv> (insec_query_of, auth_response_of)"


subsubsection \<open>Secure channel\<close>

locale sec_channel
begin

fun sec_oracle :: "('a list cstate, auth_query, nat option) oracle'" where
  "sec_oracle (Store m) Forward = return_spmf (None, Collect m)"
| "sec_oracle (Store m) Drop    = return_spmf (None, Fail)"
| "sec_oracle (Store m) Look    = return_spmf (Some (length m), Store m)"
| "sec_oracle s         _       = return_spmf (None, s)"

sublocale channel sec_oracle .

end

abbreviation (input) auth_query_of :: "auth_query \<Rightarrow> auth_query"
  where "auth_query_of \<equiv> id"

abbreviation (input) sec_response_of :: "'a list option \<Rightarrow> nat option"
  where "sec_response_of \<equiv> map_option length"

abbreviation auth_sec_wiring :: "(auth_query, nat option, auth_query, 'a list option) wiring"
  where "auth_sec_wiring \<equiv> (auth_query_of, sec_response_of)"

subsection \<open>Cipher converter\<close>

locale cipher =
  AUTH: auth_channel + KEY: key key_alg 
  for key_alg :: "'k spmf" +
  fixes enc_alg :: "'k \<Rightarrow> 'm \<Rightarrow> 'c spmf"
    and dec_alg :: "'k \<Rightarrow> 'c \<Rightarrow> 'm option"
begin

definition enc :: "('m, unit, unit + 'c, 'k + unit) converter" where
  "enc \<equiv> CNV (stateless_callee (\<lambda>m. do {
    k \<leftarrow> Pause (Inl ()) Done;
    c \<leftarrow> lift_spmf (enc_alg (projl k) m);
    (_ :: 'k + unit) \<leftarrow> Pause (Inr c) Done;
    Done (()) 
  })) ()"

definition dec :: "(unit, 'm option, unit + unit, 'k + 'c option) converter" where
  "dec \<equiv> CNV (stateless_callee (\<lambda>_. Pause (Inr ()) (\<lambda>c'. 
    case c' of Inr (Some c) \<Rightarrow> (do {
      k \<leftarrow> Pause (Inl ()) Done;
      Done (dec_alg (projl k) c) })
    | _ \<Rightarrow> Done None)
  )) ()"

definition \<pi>E :: "(auth_query, 'c option, auth_query, 'c option) converter" ("\<pi>\<^sup>E") where
  "\<pi>\<^sup>E \<equiv> 1\<^sub>C"

definition "routing \<equiv> (1\<^sub>C |\<^sub>= lassocr\<^sub>C) \<odot> swap_lassocr \<odot> (1\<^sub>C |\<^sub>= (1\<^sub>C |\<^sub>= swap_lassocr) \<odot> swap_lassocr) \<odot> rassocl\<^sub>C"

definition "res = (1\<^sub>C |\<^sub>= enc |\<^sub>= dec) \<rhd> (1\<^sub>C |\<^sub>= parallel_wiring) \<rhd> parallel_resource1_wiring \<rhd> (KEY.res \<parallel> AUTH.res)"

lemma res_alt_def: "res = ((1\<^sub>C |\<^sub>= enc |\<^sub>= dec) \<odot> (1\<^sub>C |\<^sub>= parallel_wiring)) \<rhd> parallel_resource1_wiring \<rhd> (KEY.res \<parallel> AUTH.res)"
  by(simp add: res_def attach_compose)

end

subsection \<open>Message authentication converter\<close>

locale macode = 
  INSEC: insec_channel + RO: rorc range 
  for   range :: "'r set" +
  fixes mac_alg :: "'r \<Rightarrow> 'm \<Rightarrow> 'a spmf"
begin

definition enm :: "('m, unit, 'm + ('a \<times> 'm), 'r + unit) converter" where
  "enm \<equiv> CNV (\<lambda>bs m. if bs 
    then Done ((), True)
    else do {
      r \<leftarrow> Pause (Inl m) Done;
      a \<leftarrow> lift_spmf (mac_alg (projl r) m);
      (_ :: 'r + unit) \<leftarrow> Pause (Inr (a, m)) Done;
      Done ((), True)
    }) False"

definition dem :: "(unit, 'm option, 'm + unit, 'r + ('a \<times> 'm) option) converter" where
  "dem \<equiv> CNV (stateless_callee (\<lambda>_. Pause (Inr ()) (\<lambda>am'. 
    case am' of Inr (Some (a, m)) \<Rightarrow> (do {
      r \<leftarrow> Pause (Inl m) Done;
      a' \<leftarrow> lift_spmf (mac_alg (projl r) m);    
      Done (if a' = a then Some m else None) })
    | _ \<Rightarrow> Done None)
  )) ()"

definition \<pi>E :: "(('a \<times> 'm) insec_query, ('a \<times> 'm) option, ('a \<times> 'm) insec_query, ('a \<times> 'm) option) converter" ("\<pi>\<^sup>E") where
  "\<pi>\<^sup>E \<equiv> 1\<^sub>C"

definition "routing \<equiv> (1\<^sub>C |\<^sub>= lassocr\<^sub>C) \<odot> swap_lassocr \<odot> (1\<^sub>C |\<^sub>= (1\<^sub>C |\<^sub>= swap_lassocr) \<odot> swap_lassocr) \<odot> rassocl\<^sub>C"

definition "res = (1\<^sub>C |\<^sub>= enm |\<^sub>= dem) \<rhd> (1\<^sub>C |\<^sub>= parallel_wiring) \<rhd> parallel_resource1_wiring \<rhd> (RO.res \<parallel> INSEC.res)"

end


lemma interface_wiring:
  "(cnv_advr |\<^sub>= cnv_send |\<^sub>= cnv_recv) \<rhd> (1\<^sub>C |\<^sub>= parallel_wiring) \<rhd> parallel_resource1_wiring \<rhd> 
  (RES (res2_send \<oplus>\<^sub>O res2_recv) res2_s \<parallel> RES (res1_advr \<oplus>\<^sub>O res1_send \<oplus>\<^sub>O res1_recv) res1_s)
  =
  cnv_advr |\<^sub>= cnv_send |\<^sub>= cnv_recv \<rhd>
  RES (\<dagger>res1_advr \<oplus>\<^sub>O (res2_send\<dagger> \<oplus>\<^sub>O \<dagger>res1_send) \<oplus>\<^sub>O res2_recv\<dagger> \<oplus>\<^sub>O \<dagger>res1_recv) (res2_s, res1_s)"
  (is "_ \<rhd> ?L1 \<rhd> ?L2 \<rhd> ?L3 = _ \<rhd> ?R")
proof -
  let ?wiring = "(id, id) |\<^sub>w  (lassocr\<^sub>w \<circ>\<^sub>w ((id, id) |\<^sub>w (rassocl\<^sub>w \<circ>\<^sub>w (swap\<^sub>w |\<^sub>w (id, id) \<circ>\<^sub>w lassocr\<^sub>w)) 
    \<circ>\<^sub>w rassocl\<^sub>w)) \<circ>\<^sub>w (rassocl\<^sub>w \<circ>\<^sub>w (swap\<^sub>w |\<^sub>w (id, id) \<circ>\<^sub>w lassocr\<^sub>w))"

  have "?L1 \<rhd> ?L2 \<rhd> ?L3 = ?L1 \<odot> ?L2 \<rhd>
    RES ((res2_send\<dagger> \<oplus>\<^sub>O res2_recv\<dagger>) \<oplus>\<^sub>O \<dagger>res1_advr \<oplus>\<^sub>O \<dagger>res1_send \<oplus>\<^sub>O \<dagger>res1_recv) (res2_s, res1_s)" (is "_ = _ \<rhd> RES(?O) ?S") 
    unfolding attach_compose[symmetric] resource_of_parallel_oracle[symmetric]
    by (simp only: parallel_oracle_conv_plus_oracle extend_state_oracle_plus_oracle extend_state_oracle2_plus_oracle)
  also have "\<dots> = RES(apply_wiring ?wiring ?O) ?S"
    by (rule attach_wiring_resource_of_oracle, simp only: parallel_wiring_def parallel_resource1_wiring_def swap_lassocr_def)
      ((rule wiring_intro WT_resource_of_oracle WT_plus_oracleI WT_callee_full)+, simp_all)
  also have "\<dots> = ?R" by simp
  finally show ?thesis by (rule arg_cong2[where f="attach", OF refl]) 
qed


(* prevent the simplifier from rewriting id and restructuring the equations *)
definition id' where "id' = id"

end
