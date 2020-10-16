section \<open>Code Generation from Locales\<close>
theory Locale_Code
  imports ICF_Tools Ord_Code_Preproc
begin

text \<open>
  Provides a simple mechanism to prepare code equations for
  constants stemming from locale interpretations.

  The usage pattern is as follows:
    \<open>setup Locale_Code.checkpoint\<close> is called before a series of
      interpretations, and afterwards, \<open>setup Locale_Code.prepare\<close>
      is called. Afterwards, the code generator will correctly recognize 
      expressions involving terms from the locale interpretation.

\<close>

text \<open>Tag to indicate pattern deletion\<close>
definition LC_DEL :: "'a \<Rightarrow> unit" where "LC_DEL a \<equiv> ()"

ML \<open>
signature LOCALE_CODE = sig
  type pat_eq = cterm * thm list

  val open_block: theory -> theory
  val close_block: theory -> theory

  val del_pat: cterm -> theory -> theory
  val add_pat_eq: cterm -> thm list -> theory -> theory

  val lc_decl_eq: thm list -> local_theory -> local_theory
  val lc_decl_del: term -> local_theory -> local_theory

  val setup: theory -> theory

  val get_unf_ss: theory -> simpset

  val tracing_enabled: bool Unsynchronized.ref

end

structure Locale_Code :LOCALE_CODE = struct
  open ICF_Tools

  val tracing_enabled = Unsynchronized.ref false;

  type pat_eq = cterm * thm list

  type block_data = {idx:int, del_pats: cterm list, add_pateqs: pat_eq list}
  val closed_block = {idx = ~1, del_pats=[], add_pateqs=[]};
  fun init_block idx = {idx = idx, del_pats=[], add_pateqs=[]};
  fun is_open ({idx,...}:block_data) = idx <> ~1;

  fun assert_open bd 
  = if is_open bd then () else error "Locale_Code: No open block";

  fun assert_closed bd 
  = if is_open bd then error "Locale_Code: Block already open" else ();


  fun merge_bd (bd1,bd2) = (
    if is_open bd1 orelse is_open bd2 then 
      error "Locale_Code: Merge with open block"  
    else ();
    closed_block
  );

  fun bd_add_del_pats ps {idx,del_pats,add_pateqs} 
    = {idx = idx, del_pats = ps@del_pats, add_pateqs = add_pateqs};
  fun bd_add_add_pateqs pes {idx,del_pats,add_pateqs} 
    = {idx = idx, del_pats = del_pats, add_pateqs = pes@add_pateqs};

  structure BlockData = Theory_Data (
    type T = block_data
    val empty = (closed_block)
    val extend = I
    val merge = merge_bd
  );

  structure FoldSSData = Oc_Simpset (
    val prio = 5;
    val name = "Locale_Code";
  );

  fun add_unf_thms thms thy = let
    val ctxt = Proof_Context.init_global thy
    val thms = map Thm.symmetric thms
  in 
    FoldSSData.map (fn ss => 
         put_simpset ss ctxt 
      |> sss_add thms
      |> simpset_of
    ) thy
  end
  
  val get_unf_ss = FoldSSData.get;


  (* First order match with fixed head *)
  fun match_fixed_head (pat,obj) = let
    (* Match heads *)
    val inst = Thm.first_order_match (chead_of pat, chead_of obj);
    val pat = Thm.instantiate_cterm inst pat;
    (* Now match whole pattern *)
    val inst = Thm.first_order_match (pat, obj);
  in inst end;

  val matches_fixed_head = can match_fixed_head; 

  (* First order match of heads only *)
  fun match_heads (pat,obj) = Thm.first_order_match (chead_of pat, chead_of obj);

  val matches_heads = can match_heads; 

  val pat_nargs = Thm.term_of #> strip_comb #> #2 #> length;

  (* Adjust a theorem to exactly match pattern *)
  fun norm_thm_pat (thm,pat) = let
    val thm = norm_def_thm thm;
    val na_pat = pat_nargs pat;
    val lhs = Thm.lhs_of thm;
    val na_lhs = pat_nargs lhs;
    val lhs' = if na_lhs > na_pat then funpow (na_lhs - na_pat) Thm.dest_fun lhs
      else lhs;
    val inst = Thm.first_order_match (lhs',pat);
  in Thm.instantiate inst thm end;

  fun del_pat_matches cpat (epat,_) = if pat_nargs cpat = 0 then
    matches_heads (cpat,epat)
  else
    matches_fixed_head (cpat,epat);

  (* Pattern-Eqs from specification *)
  local
    datatype action = ADD of (cterm * thm list) 
    | DEL of cterm

    fun filter_pat_eq thy thms pat = let
      val cpat = Thm.global_cterm_of thy pat;
    in 
      if (pat_nargs cpat = 0) then NONE
      else let 
        val thms' = fold 
          (fn thm => fn acc => case try norm_thm_pat (thm, cpat) of
            NONE => acc | SOME thm => thm::acc
          ) thms [];
      in case thms' of [] => NONE | _ => SOME (ADD (cpat,thms')) end 
    end;

    fun process_actions acc [] = acc
    | process_actions acc (ADD peq::acts) = process_actions (peq::acc) acts
    | process_actions acc (DEL cpat::acts) = let
      val acc' = filter (not o curry renames_cterm cpat o fst) acc;
      val _ = if length acc = length acc' then
          warning ("Locale_Code: LC_DEL without effect: "
            ^ @{make_string} cpat) 
        else ();
    in process_actions acc' acts end;

    fun pat_eqs_of_spec thy
          {rough_classification = Spec_Rules.Equational _, terms = pats, rules = thms, ...} =
        map_filter (filter_pat_eq thy thms) pats
    | pat_eqs_of_spec thy
          {rough_classification = Spec_Rules.Unknown, terms = [Const (@{const_name LC_DEL},_)$pat], ...} =
        [(DEL (Thm.global_cterm_of thy pat))]
    | pat_eqs_of_spec _ _ = [];
  in

    fun pat_eqs_of_specs thy specs = map (pat_eqs_of_spec thy) specs 
      |> flat |> rev |> process_actions [];
  
  end;

  
  fun is_proper_pat cpat = let
    val pat = Thm.term_of cpat;
    val (f,args) = strip_comb pat;
  in 
    is_Const f 
    andalso args <> [] 
    andalso not (is_Var (hd (rev args)))
  end;

  (* Instantiating pattern-eq *)
  local
    (* Get constant name for instantiation pattern *)
    fun inst_name lthy pat = let
      val (fname,params) = case strip_comb pat of
        ((Const (fname,_)),params) => (fname,params)
      | _ => raise TERM ("inst_name: Expected pattern",[pat]);

      fun pname (Const (n,_)) = Long_Name.base_name n
        | pname (s$t) = pname s ^ "_" ^ pname t
        | pname _ = Name.uu;
    in  
      space_implode "_" (Long_Name.base_name fname::map pname params)
      |> gen_variant (can (Proof_Context.read_const {proper = true, strict = false} lthy))
    end;
  in
    fun inst_pat_eq (cpat,thms) = 
    wrap_lthy_result_global
      (fn lthy => let
        val ((inst,thms),lthy) = Variable.import true thms lthy;
        val cpat = Thm.instantiate_cterm inst cpat;
        val pat = Thm.term_of cpat;
        val name = inst_name lthy pat;
        val ((_,(_,def_thm)),lthy) 
          = Local_Theory.define ((Binding.name name,NoSyn),
             ((Binding.name (Thm.def_name name),[]),pat)) lthy;
        val thms' = map (Local_Defs.fold lthy [def_thm]) thms;
      in ((def_thm,thms'),lthy) end)
      (fn m => fn (def_thm,thms') => 
        (Morphism.thm m def_thm, map (Morphism.thm m) thms'))
    #> (fn ((def_thm,thms'),thy) => let
      val thy = thy 
        |> add_unf_thms [def_thm]
        |> Code.declare_default_eqns_global (map (rpair true) thms');
    in thy end)
  end

  (* Bookkeeping *)
  fun new_specs thy = let
    val bd = BlockData.get thy;
    val _ = assert_open bd;
    val ctxt = Proof_Context.init_global thy;
    val srules = Spec_Rules.get ctxt;
    val res = take (length srules - #idx bd) srules;
  in res end

  fun open_block thy = let
    val bd = BlockData.get thy;
    val _ = assert_closed bd;
    val ctxt = Proof_Context.init_global thy;
    val idx = length (Spec_Rules.get ctxt);
    val thy = BlockData.map (K (init_block idx)) thy;
  in thy end;

  fun process_block bd thy = let
    fun filter_del_pats cpat peqs = let
      val peqs' = filter (not o del_pat_matches cpat) peqs
      val _ = if length peqs = length peqs' then
          warning ("Locale_Code: No pattern-eqs matching filter: " ^ 
            @{make_string} cpat) 
        else ();
    in peqs' end;

    fun filter_add_pats (orig_pat,_) = forall (fn (add_pat,_) => 
        not (renames_cterm (orig_pat,add_pat))) 
      (#add_pateqs bd);

    val specs = new_specs thy;
    val peqs = pat_eqs_of_specs thy specs
      |> fold filter_del_pats (#del_pats bd)
      |> filter filter_add_pats;
    val peqs = peqs @ #add_pateqs bd;

    val peqs = rev peqs; (* Important: Process equations in the order in that
      they have been added! *)

    val _ = if !tracing_enabled then
      map (fn peq => (tracing (@{make_string} peq); ())) peqs
    else [];

    val thy = thy |> fold inst_pat_eq peqs;

  in thy end;

  fun close_block thy = let
    val bd = BlockData.get thy;
    val _ = assert_open bd;
    val thy = process_block bd thy
      |> BlockData.map (K closed_block);
  in thy end;
    

  fun del_pat cpat thy = let
    val bd = BlockData.get thy;
    val _ = assert_open bd;
    val bd = bd_add_del_pats [cpat] bd;
    val thy = BlockData.map (K bd) thy;
  in thy end;

  fun add_pat_eq cpat thms thy = let
    val _ = is_proper_pat cpat 
      orelse raise CTERM ("add_pat_eq: Not a proper pattern",[cpat]);
  
    fun ntp thm = case try norm_thm_pat (thm,cpat) of
      NONE => raise THM ("add_pat_eq: Theorem does not match pattern",~1,[thm])
    | SOME thm => thm;
  
    val thms = map ntp thms;
    val thy = BlockData.map (bd_add_add_pateqs [(cpat,thms)]) thy;
  in thy end;

  local
    fun cpat_of_thm thm = let
      fun strip ct = case Thm.term_of ct of
        (_$Var _) => strip (Thm.dest_fun ct)
      | _ => ct;
    in
      strip (Thm.lhs_of thm)
    end;

    fun adjust_length (cpat1,cpat2) = let
      val n1 = cpat1 |> Thm.term_of |> strip_comb |> #2 |> length;
      val n2 = cpat2 |> Thm.term_of |> strip_comb |> #2 |> length;
    in 
      if n1>n2 then
        (funpow (n1-n2) Thm.dest_fun cpat1, cpat2)
      else
        (cpat1, funpow (n2-n1) Thm.dest_fun cpat2)

    end

    fun find_match cpat cpat' = SOME (cpat,rename_cterm (cpat',cpat))
      handle Pattern.MATCH => (case Thm.term_of cpat' of 
          _$_ => find_match (Thm.dest_fun cpat) (Thm.dest_fun cpat')
        | _ => NONE
      );

    (* Common head of definitional theorems *)
    fun comp_head thms = case map norm_def_thm thms of
      [] => NONE
    | thm::thms => let
        fun ch [] r = SOME r
        | ch (thm::thms) (cpat,acc) = let
            val cpat' = cpat_of_thm thm;
            val (cpat,cpat') = adjust_length (cpat,cpat')
          in case find_match cpat cpat' of NONE => NONE
            | SOME (cpat,inst) => 
              ch thms (cpat, Drule.instantiate_normalize inst thm :: acc)
          end;
      in ch thms (cpat_of_thm thm,[thm]) end;

  in
    fun lc_decl_eq thms lthy = case comp_head thms of
      SOME (cpat,thms) => let
        val _ = if !tracing_enabled then 
          tracing ("decl_eq: " ^ @{make_string} cpat ^ ": "
                 ^ @{make_string} thms)
        else ();

        fun decl m = let
          val cpat'::thms' = Morphism.fact m (Drule.mk_term cpat :: thms);
          val cpat' = Drule.dest_term cpat';
        in 
          Context.mapping 
            (BlockData.map (bd_add_add_pateqs [(cpat',thms')])) I 
        end
      in 
        lthy |> Local_Theory.declaration {syntax = false, pervasive = false} decl
      end
    | NONE => raise THM ("Locale_Code.lc_decl_eq: No common pattern",~1,thms);

  end;

  fun lc_decl_del pat = let
    val ty = fastype_of pat;
    val dpat = Const (@{const_name LC_DEL},ty --> @{typ unit})$pat;
  in 
    Spec_Rules.add Binding.empty Spec_Rules.Unknown [dpat] []
  end


  (* Package setup *)
  val setup = FoldSSData.setup;

end

\<close>

setup Locale_Code.setup

attribute_setup lc_delete = \<open>
  Parse.and_list1' ICF_Tools.parse_cpat >> 
    (fn cpats => Thm.declaration_attribute (K 
      (Context.mapping (fold Locale_Code.del_pat cpats) I)))
\<close> "Locale_Code: Delete patterns for current block"

attribute_setup lc_add = \<open>
  Parse.and_list1' (ICF_Tools.parse_cpat -- Attrib.thms) >> 
    (fn peqs => Thm.declaration_attribute (K 
      (Context.mapping (fold (uncurry Locale_Code.add_pat_eq) peqs) I)))
\<close> "Locale_Code: Add pattern-eqs for current block"

end
