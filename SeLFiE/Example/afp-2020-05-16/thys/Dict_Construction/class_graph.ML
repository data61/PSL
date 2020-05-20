signature CLASS_GRAPH =
sig
  type selector = typ -> term

  type node =
    {class: string,
     qname: string,
     selectors: selector Symtab.table,
     make: typ -> term,
     data_thms: thm list,
     cert: typ -> term,
     cert_thms: thm * thm * thm list}

  val dict_typ: node -> typ -> typ

  type edge =
    {super_selector: selector,
     subclass: thm}

  type path = edge list

  type ev

  val class_of: ev -> class
  val node_of: ev -> node
  val parents_of: ev -> (edge * ev) Symtab.table

  val find_path': ev -> (ev -> 'a option) -> (path * 'a) option
  val find_path: ev -> class -> path option
  val fold_path: path -> typ -> term -> term

  val ensure_class: class -> local_theory -> (ev * local_theory)

  val edges: local_theory -> class -> edge Symtab.table option
  val node: local_theory -> class -> node option
  val all_edges: local_theory -> edge Symreltab.table
  val all_nodes: local_theory -> node Symtab.table

  val pretty_ev: Proof.context -> ev -> Pretty.T

  (* utilities *)
  val mangle: string -> string
  val param_sorts: string -> class -> theory -> class list list
  val super_classes: class -> theory -> string list
end

structure Class_Graph: CLASS_GRAPH =
struct

open Dict_Construction_Util

val mangle =
  translate_string (fn x =>
    if x = "." then
      "_"
    else if x = "_" then
      "__"
    else
      x)

fun param_sorts tyco class thy =
  let val algebra = Sign.classes_of thy in
    Sorts.mg_domain algebra tyco [class] |> map (filter (Class.is_class thy))
  end

fun super_classes class thy =
  let val algebra = Sign.classes_of thy in
    Sorts.super_classes algebra class |>
      Sorts.minimize_sort algebra |>
      filter (Class.is_class thy) |>
      sort fast_string_ord
  end

type selector = typ -> term

type node =
  {class: string,
   qname: string,
   selectors: selector Symtab.table,
   make: typ -> term,
   data_thms: thm list,
   cert: typ -> term,
   cert_thms: thm * thm * thm list}

type edge =
  {super_selector: selector,
   subclass: thm}

type path = edge list

abstype ev = Evidence of class * node * (edge * ev) Symtab.table
with

fun class_of (Evidence (class, _, _)) = class
fun node_of (Evidence (_, node, _)) = node
fun parents_of (Evidence (_, _, tab)) = tab

fun mk_evidence class node tab = Evidence (class, node, tab)

fun find_path' ev is_goal =
  case is_goal ev of
    SOME a =>
      SOME ([], a)
  | NONE =>
    let
      fun f (_, (edge, ev)) = Option.map (apfst (cons edge)) (find_path' ev is_goal)
    in Symtab.get_first f (parents_of ev) end

fun find_path ev goal =
  find_path' ev (fn ev => if class_of ev = goal then SOME () else NONE) |> Option.map fst

fun pretty_ev ctxt (Evidence (class, {qname, ...}, tab)) =
  let
    val typ = @{typ 'a}
    fun mk_super ({super_selector, ...}, super_ev) = Pretty.block
      [Pretty.str "selector:",
       Pretty.brk 1,
       Syntax.pretty_term ctxt (super_selector typ),
       Pretty.fbrk,
       pretty_ev ctxt super_ev]
    val supers = Symtab.dest tab
      |> map (fn (_, super) => mk_super super)
      |> Pretty.big_list "super classes"
  in
    Pretty.block
      [Pretty.str "Evidence for ",
       Syntax.pretty_sort ctxt [class],
       Pretty.str ": ",
       Syntax.pretty_typ ctxt (Type (qname, [typ])),
       Pretty.str (" (qname = " ^ qname ^ ")"),
       Pretty.fbrk,
       supers]
  end

end

structure Classes = Generic_Data
(
  type T = (edge Symtab.table * node) Symtab.table
  val empty = Symtab.empty
  fun merge (t1, t2) =
    if Symtab.is_empty t1 andalso Symtab.is_empty t2 then
      Symtab.empty
    else
      error "merging not supported"
  val extend = I
)

fun node lthy class =
  Symtab.lookup (Classes.get (Context.Proof lthy)) class |> Option.map snd

fun edges lthy class =
  Symtab.lookup (Classes.get (Context.Proof lthy)) class |> Option.map fst

val all_nodes =
  Context.Proof #> Classes.get #> Symtab.map (K snd)

val all_edges =
  Context.Proof #> Classes.get #> Symtab.map (K fst) #> symreltab_of_symtab

fun dict_typ {qname, ...} typ =
  Type (qname, [typ])

fun fold_path path typ =
  fold (fn {super_selector = s, ...} => fn acc => s typ $ acc) path

fun mk_super_selector' qualified qname super_ev typ =
  let
    val {class = super_class, qname = super_qname, ...} = node_of super_ev
    val raw_name = mangle super_class ^ "__super"
    val name = if qualified then Long_Name.append qname raw_name else raw_name
  in (name, Type (qname, [typ]) --> Type (super_qname, [typ])) end

fun mk_node class info super_evs lthy =
  let
    fun print_info ctxt =
      Pretty.block [Pretty.str "Defining record for class ", Syntax.pretty_sort ctxt [class]]
      |> Pretty.writeln

    val name = mangle class ^ "__dict"
    val qname = Local_Theory.full_name lthy (Binding.name name)
    val tvar = @{typ 'a}
    val typ = Type (qname, [tvar])

    fun mk_field name ftyp = (Binding.name name, ftyp)

    val params = #params info
      |> map (fn (name', ftyp) =>
        let
          val ftyp' = typ_subst_atomic [(TFree ("'a", [class]), @{typ 'a})] ftyp
          val field_name = mangle name' ^ "__field"
          val field = mk_field field_name ftyp'
          fun sel tvar' =
            Const (Long_Name.append qname field_name,
                   typ_subst_atomic [(tvar, tvar')] (typ --> ftyp'))
        in (field, (name', sel)) end)
    val (fields, selectors) = split_list params

    val super_params = Symtab.dest super_evs |>
      map (fn (_, super_ev) =>
        let
          val {cert = raw_super_cert, qname = super_qname, ...} = node_of super_ev
          val (field_name, _) = mk_super_selector' false qname super_ev tvar
          val field = mk_field field_name (Type (super_qname, [tvar]))
          fun sel typ = Const (mk_super_selector' true qname super_ev typ)
          fun super_cert dict = raw_super_cert tvar $ (sel tvar $ dict)
          val raw_edge = (class_of super_ev, sel)
        in (field, raw_edge, super_cert) end)
    val (super_fields, raw_edges, super_certs) = split_list3 super_params

    val all_fields = super_fields @ fields

    fun make typ' =
      Const (Long_Name.append qname "Dict",
        typ_subst_atomic [(tvar, typ')] (map #2 all_fields ---> typ))

    val cert_name = name ^ "__cert"
    val cert_binding = Binding.name cert_name
    val cert_body =
      let
        fun local_param_eq ((_, typ), (name, sel)) dict =
          HOLogic.mk_eq (sel tvar $ dict, Const (name, typ))
      in
        map local_param_eq params @ super_certs
      end
    val cert_var_name = "dict"
    val cert_term =
      Abs (cert_var_name, typ,
        List.foldr HOLogic.mk_conj @{term True} (map (fn x => x (Bound 0)) cert_body))

    fun prove_thms (cert, cert_def) lthy =
      let
        val var = Free (cert_var_name, typ)
        fun tac ctxt = Local_Defs.unfold_tac ctxt [cert_def] THEN blast_tac ctxt 1
        fun prove prop =
          Goal.prove_future lthy [cert_var_name] [] prop (fn {context, ...} => tac context)

        fun mk_dest_props raw_prop =
          HOLogic.mk_Trueprop (cert $ var) ==> HOLogic.mk_Trueprop (raw_prop var)
        fun mk_intro_cond raw_prop =
          HOLogic.mk_Trueprop (raw_prop var)

        val dests =
          map (fn raw_prop => prove (mk_dest_props raw_prop)) cert_body
        val intro =
          prove (map mk_intro_cond cert_body ===> HOLogic.mk_Trueprop (cert $ var))

        val (dests', (intro', lthy')) =
          note_thms Binding.empty dests lthy ||> note_thm Binding.empty intro

        val (param_dests, super_dests) = chop (length params) dests'

        fun pre_edges phi =
          let
            fun mk_edge thm (sc, sel) =
              (sc, {super_selector = sel, subclass = Morphism.thm phi thm})
          in Symtab.make (map2 mk_edge super_dests raw_edges) end
      in
        ((param_dests, pre_edges, intro'), lthy')
      end

    val constructor =
      (((Binding.empty, Binding.name "Dict"), all_fields), NoSyn)
    val datatyp =
      (([(NONE, (@{typ 'a}, @{sort type}))], Binding.name name), NoSyn)

    val dtspec =
      (Ctr_Sugar.default_ctr_options,
       [(((datatyp, [constructor]), (Binding.empty, Binding.empty, Binding.empty)), [])])

    val (((raw_cert, raw_cert_def), (param_dests, pre_edges, intro)), (lthy', lthy)) = lthy
      |> tap print_info
      |> BNF_FP_Def_Sugar.co_datatypes BNF_Util.Least_FP BNF_LFP.construct_lfp dtspec
      (* FIXME ideally BNF would return a fp_sugar value right here so that I can avoid constructing
         long names by hand above *)
      |> Local_Theory.open_target |> snd
      |> Local_Theory.define ((cert_binding, NoSyn), ((Thm.def_binding cert_binding, []), cert_term))
      |>> apsnd snd
      |> (fn (raw_cert, lthy) => prove_thms raw_cert lthy |>> pair raw_cert)
      ||> `Local_Theory.close_target

    val phi = Proof_Context.export_morphism lthy lthy'
    fun cert typ = subst_TVars [(("'a", 0), typ)] (Morphism.term phi raw_cert)
    val cert_def = Morphism.thm phi raw_cert_def
    val edges = pre_edges phi
    val param_dests' = map (Morphism.thm phi) param_dests
    val intro' = Morphism.thm phi intro

    val data_thms =
      BNF_FP_Def_Sugar.fp_sugar_of lthy' qname
      |> the |> #fp_ctr_sugar |> #ctr_sugar |> #sel_thmss |> flat
      |> map safe_mk_meta_eq

    val node =
      {class = class,
       qname = qname,
       selectors = Symtab.make selectors,
       make = make,
       data_thms = data_thms,
       cert = cert,
       cert_thms = (cert_def, intro', param_dests')}
  in (node, edges, lthy') end

fun ensure_class class lthy =
  if not (Class.is_class (Proof_Context.theory_of lthy) class) then
    error ("not a proper class: " ^ class)
  else
    let
      val thy = Proof_Context.theory_of lthy
      val super_classes = super_classes class thy
      fun collect_super mk_node =
        let
          val (super_evs, lthy') = fold_map ensure_class super_classes lthy
          val raw_tab = Symtab.make (super_classes ~~ super_evs)
          val (node, edges, lthy'') = mk_node raw_tab lthy'
          val tab = zip_symtabs pair edges raw_tab
          val ev = mk_evidence class node tab
        in (ev, edges, lthy'') end
    in
      case Symtab.lookup (Classes.get (Context.Proof lthy)) class of
        SOME (edge_tab, node) =>
          if super_classes = Symtab.keys edge_tab then
            let val (ev, _, lthy') = collect_super (fn _ => fn lthy => (node, edge_tab, lthy)) in
              (ev, lthy')
            end
          else
            (* This happens when a new subclass relationship is established which subsumes or
               augments previous superclasses. *)
            error "class with different super classes"
      | NONE =>
          let
            val ax_info = Axclass.get_info thy class
            val (ev, edges, lthy') = collect_super (mk_node class ax_info)
            val upd = Symtab.update_new (class, (edges, node_of ev))
          in
            (ev, Local_Theory.declaration {pervasive = false, syntax = false} (K (Classes.map upd)) lthy')
          end
    end

end
