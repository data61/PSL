chapter \<open>Top-level functional semantics\<close>

theory Semantics
imports
  "generated/CakeML/Tokens"
  "generated/CakeML/TypeSystem"
  "generated/CakeML/Evaluate"
  "HOL-Library.Finite_Map"
begin

hide_const (open) type_env.t
hide_const (open) Lem_string.concat

type_synonym num = nat

\<comment>\<open>From HOL4 locationScript.sml\<close>

consts unknown_loc :: locs

definition merge_locs :: "locs \<Rightarrow> locs \<Rightarrow> locs" where
"merge_locs l1 l2 = (fst l1, snd l2)"

fun merge_list_locs :: "locs list \<Rightarrow> locs" where
"merge_list_locs [] = unknown_loc" |
"merge_list_locs [h] = h" |
"merge_list_locs [h1, h2] = merge_locs h1 h2" |
"merge_list_locs (h1 # h2 # t) = merge_list_locs (h1 # t)"

\<comment>\<open>From HOL4 grammarScript.sml\<close>

type_synonym 'a inf = "'a + num"

datatype ('a, 'b) symbol =
  TOK 'a |
  NT "'b inf"

datatype_record ('a, 'b) grammar =
  start :: "'b inf"
  rules :: "('b inf, ('a, 'b) symbol list set) fmap"

datatype ('a, 'b, 'locs) parsetree =
  Lf "(('a, 'b) symbol \<times> 'locs)" |
  Nd "('b inf * 'locs)" "(('a, 'b, 'locs) parsetree list)"

definition ptree_loc :: "('a,'b,'locs) parsetree \<Rightarrow> 'locs" where
"ptree_loc pt = (case pt of (Lf (_, l)) \<Rightarrow> l
                          | (Nd (_, l) _) \<Rightarrow> l)"

definition ptree_head :: "('a, 'b, 'locs) parsetree \<Rightarrow> ('a, 'b) symbol" where
"ptree_head pt = (case pt of (Lf (tok, _)) \<Rightarrow> tok
                           | (Nd (nt, _) _) \<Rightarrow> NT nt)"

fun valid_ptree :: "('a, 'b) grammar \<Rightarrow> ('a, 'b, 'locs) parsetree \<Rightarrow> bool" where
"valid_ptree G (Lf _) \<longleftrightarrow> True" |
"valid_ptree G (Nd (nt, l) children) \<longleftrightarrow>
  nt |\<in>| fmdom (rules G) \<and>
  (case fmlookup (rules G) nt of
     Some s \<Rightarrow> map ptree_head children \<in> s
   | None \<Rightarrow> False) \<and>
  (\<forall>pt. pt \<in> set children \<longrightarrow> valid_ptree G pt)"

fun ptree_fringe :: "('a, 'b, 'locs) parsetree \<Rightarrow> ('a, 'b) symbol list" where
"ptree_fringe (Lf (tk,_)) = [tk]" |
"ptree_fringe (Nd _ children) = concat (map ptree_fringe children)"

type_synonym ('a,'b) lfptree = "('a, 'b, unit) parsetree"

fun real_fringe :: "('a, 'b, 'locs) parsetree \<Rightarrow> (('a, 'b) symbol, 'locs) alist" where
"real_fringe (Lf tk) = [tk]" |
"real_fringe (Nd n ptl) = concat (map real_fringe ptl)"

fun valid_locs :: "('a, 'b, locs) parsetree \<Rightarrow> bool" where
"valid_locs (Lf _) \<longleftrightarrow> True" |
"valid_locs (Nd (_, l) children) \<longleftrightarrow>
  (l = merge_list_locs (map ptree_loc children) \<and>
  (\<forall>pt. pt \<in> set children \<longrightarrow> valid_locs pt))"

definition valid_lptree :: "('a, 'b) grammar \<Rightarrow> ('a, 'b, locs) parsetree \<Rightarrow> bool" where
"valid_lptree G pt \<longleftrightarrow> valid_locs pt \<and> valid_ptree G pt"

\<comment>\<open>From gramScript.sml\<close>

typedecl MMLnonT
type_synonym NT = "MMLnonT inf"
consts cmlG :: "(token, MMLnonT) grammar"
consts mkNT :: "MMLnonT \<Rightarrow> NT"
consts TK :: "token \<Rightarrow> (token, MMLnonT) symbol"
consts nTopLevelDecs :: "MMLnonT"
consts NN :: "MMLnonT \<Rightarrow> ('a,MMLnonT) symbol"
type_synonym mlptree = "(token, MMLnonT, locs) parsetree"

\<comment>\<open>From file cmlPtreeConversionScript.sml\<close>

consts ptree_TopLevelDecs :: "mlptree \<Rightarrow> prog option"

\<comment>\<open>From file semanticsScript.sml\<close>

definition some :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option" where
"some P = (if (\<exists>x. P x) then Some (SOME x. P x) else None)"

definition parse :: "(token, locs) alist \<Rightarrow> prog option" where
"parse toks = (case some (\<lambda>pt.
                 valid_lptree cmlG pt \<and>
                 ptree_head pt = NT (mkNT nTopLevelDecs) \<and>
                 real_fringe pt = (map (map_prod TOK id) toks))
               of Some pt \<Rightarrow> ptree_TopLevelDecs pt | None \<Rightarrow> None)"

datatype_record 'ffi state =
  tdecs :: "decls"
  tenv :: "type_env"
  sem_st :: "'ffi SemanticPrimitives.state"
  sem_env :: "v sem_env"

definition can_type_prog :: "'a state \<Rightarrow> prog \<Rightarrow> bool" where
"can_type_prog state prog \<longleftrightarrow>
  (\<exists>tdecs' new_tenv. type_prog True (tdecs state) (tenv state) prog tdecs' new_tenv)"

definition evaluate_prog_with_clock :: "'a SemanticPrimitives.state \<Rightarrow> v sem_env \<Rightarrow> num \<Rightarrow> prog \<Rightarrow> 'a ffi_state \<times> (v sem_env, v) result" where
"evaluate_prog_with_clock st env k prog =
  (case fun_evaluate_prog (st \<lparr> clock := k \<rparr>) env prog of (st',r) \<Rightarrow> ((ffi st',r)))"

definition lprefix_lub :: "'a llist set \<Rightarrow> 'a llist \<Rightarrow> bool" where
"lprefix_lub ls lub = ((\<forall>ll \<in> ls. lprefix ll lub) \<and> (\<forall>ub. (\<forall>ll \<in> ls. lprefix ll ub) \<longrightarrow> lprefix lub ub))"

definition semantics_prog :: "'a SemanticPrimitives.state \<Rightarrow> v sem_env \<Rightarrow> prog \<Rightarrow> behaviour \<Rightarrow> bool" where
"semantics_prog st env prog bhv =
  (case bhv of
    Terminate outcome io_list \<Rightarrow>
      (\<exists>k ffi r. evaluate_prog_with_clock st env k prog = (ffi,r) \<and>
                 (case (final_event ffi) of None \<Rightarrow> (r \<noteq> Rerr (Rabort Rtimeout_error)) \<and> outcome = Success
                                          | Some e \<Rightarrow> outcome = FFI_outcome e) \<and>
                 io_list = (io_events ffi)) \<and>
      (\<forall>k ffi. evaluate_prog_with_clock st env k prog \<noteq> (ffi, Rerr (Rabort Rtype_error)))
  | Diverge io_trace \<Rightarrow>
      (\<exists>k. \<forall>ffi. (evaluate_prog_with_clock st env k prog = (ffi, Rerr (Rabort Rtimeout_error))) \<and>
                 (final_event ffi) = None \<and>
                 (lprefix_lub {llist_of (io_events (fst (evaluate_prog_with_clock st env k prog)))| k. True} io_trace))
  | Fail \<Rightarrow>
      (\<exists>k. snd (evaluate_prog_with_clock st env k prog) = Rerr (Rabort Rtype_error)))"

datatype semantics = CannotParse | IllTyped | Execute "behaviour \<Rightarrow> bool"

consts lexer_fun :: "tvarN \<Rightarrow> (token, locs) alist"

definition semantics :: "'a state \<Rightarrow> prog \<Rightarrow> tvarN \<Rightarrow> semantics" where
"semantics state prelude input =
  (case parse (lexer_fun input) of
    None \<Rightarrow> CannotParse
  | Some prog \<Rightarrow>
      (if can_type_prog state (prelude @ prog)
       then Execute (semantics_prog (sem_st state) (sem_env state) (prelude @ prog))
       else IllTyped))"

end