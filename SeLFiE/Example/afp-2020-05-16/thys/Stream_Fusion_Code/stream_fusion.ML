(* Title: stream_fusion.ML
  Author: Alexandra Maximova, ETH Zurich,
          Andreas Lochbihler, ETH Zurich 

Implementation of the stream fusion transformation as a simproc for the preprocessor of the
code generator
*)

signature STREAM_FUSION =
sig
  val get_rules: Proof.context -> thm list
  val get_conspats: Proof.context -> (term * thm) list
  val match_consumer: Proof.context -> term -> bool
  val add_fusion_rule: thm -> Context.generic -> Context.generic
  val del_fusion_rule: thm -> Context.generic -> Context.generic
  val add_unstream: string -> Context.generic -> Context.generic
  val del_unstream: string -> Context.generic -> Context.generic
  val get_unstream: Proof.context -> string list
  val fusion_add: attribute
  val fusion_del: attribute
  val fusion_conv: Proof.context -> conv
  val fusion_simproc: Proof.context -> cterm -> thm option
  val trace: bool Config.T
end;

structure Stream_Fusion : STREAM_FUSION = 
struct

type fusion_rules = 
  { rules : thm Item_Net.T,
    conspats : (term * thm) Item_Net.T,
    unstream : string list
  }

fun map_fusion_rules f1 f2 f3
  {rules, conspats, unstream}
  =
  {rules = f1 rules,
   conspats = f2 conspats,
   unstream = f3 unstream};

fun map_rules f = map_fusion_rules f I I;
fun map_conspats f = map_fusion_rules I f I;
fun map_unstream f = map_fusion_rules I I f;


(* producers: theorems about producers, have 'unstream' only on the lhs *)
(* consumers: theorems about consumers, have 'unstream' only on the rhs *)
(* transformers: theorems about transformers, have 'unstream' on both sides *)
(* conspats: patterns of consumers that have matching theorems in consumers *)
structure Fusion_Rules = Generic_Data
(
  type T = fusion_rules;
  val empty = {rules = Thm.full_rules,
               conspats = Item_Net.init (Thm.eq_thm_prop o apply2 snd) (single o fst),
               unstream = []};
  val extend = I;
  fun merge 
    ({rules = r, conspats = cp, unstream = u},
     {rules = r', conspats = cp', unstream = u'}) =
    {rules = Item_Net.merge (r, r'),
     conspats = Item_Net.merge (cp, cp'),
     unstream = Library.merge (op =) (u, u')}
);


val get_rules = Item_Net.content o #rules o Fusion_Rules.get o Context.Proof;
val get_conspats = Item_Net.content o #conspats o Fusion_Rules.get o Context.Proof;
val get_unstream = #unstream o Fusion_Rules.get o Context.Proof;

fun match_consumer ctxt t = 
  Context.Proof ctxt
  |> Fusion_Rules.get
  |> #conspats
  |> (fn net => Item_Net.retrieve_matching net t)
  |> not o null

datatype classification = ProducerTransformer | Consumer of term

(* used to find out if a 'unstream' is present in a term *)
fun occur_in ts ((Const (c, _)) $ t) =
    member (op =) ts c orelse occur_in ts t
  | occur_in ts (op $ (u, t)) = occur_in ts u orelse occur_in ts t
  | occur_in ts (Abs (_, _, t)) = occur_in ts t
  | occur_in _ _ = false;

fun first_depth (t1 $ _) = let val (f,d) = first_depth t1 in (f,d+1) end |
    first_depth t1 = (t1,0)

fun mk_conspat rhs ctxt =
  let
    val (f,d) = first_depth rhs
    val types = binder_types (fastype_of f)
    val (vfixes, ctxt1) = Variable.variant_fixes (replicate d "x") ctxt 
  in
    (hd o Variable.export_terms ctxt1 ctxt o single) (list_comb (f, map Free (vfixes ~~ types)))
  end

fun classify ctxt thm = case Thm.full_prop_of thm
  of (@{const Trueprop} $ (Const (@{const_name "HOL.eq"}, _) $ lhs $ rhs)) =>
    let val unstream = get_unstream ctxt in
      if occur_in unstream lhs then SOME ProducerTransformer
      else if occur_in unstream rhs then SOME (Consumer (mk_conspat rhs ctxt))
      else NONE
    end
  | _ => NONE;

fun sym thm = thm RS @{thm sym}

fun format_error ctxt thm =
  warning (Pretty.string_of (Pretty.block [
    Pretty.str "Wrong format for fusion rule: ",
    Pretty.brk 2,
    Syntax.pretty_term (Context.proof_of ctxt) (Thm.prop_of thm)]))

fun register thm NONE = (fn ctxt =>
  let
    val _ = format_error ctxt thm
  in
    ctxt
  end)
| register thm (SOME ProducerTransformer) = Fusion_Rules.map (
    map_rules (Item_Net.update (sym thm)))
| register thm (SOME (Consumer cp)) = Fusion_Rules.map (
    map_rules (Item_Net.update (sym thm)) o map_conspats (Item_Net.update (cp, thm)));

fun unregister thm NONE = (fn ctxt =>
  let
    val _ = format_error ctxt thm
  in
    ctxt
  end)
| unregister thm (SOME ProducerTransformer) = Fusion_Rules.map (
    map_rules (Item_Net.remove (sym thm)))
| unregister thm (SOME (Consumer cp)) = Fusion_Rules.map (
    map_rules (Item_Net.remove (sym thm)) o map_conspats (Item_Net.remove (cp, thm)));

fun add_fusion_rule thm ctxt = register thm (classify (Context.proof_of ctxt) thm) ctxt
fun del_fusion_rule thm ctxt = unregister thm (classify (Context.proof_of ctxt) thm) ctxt

fun add_unstream c = Fusion_Rules.map (map_unstream (insert (op =) c))
fun del_unstream c = Fusion_Rules.map (map_unstream (remove (op =) c))

(* attributes and setup *)
val fusion_add = Thm.declaration_attribute add_fusion_rule;
val fusion_del = Thm.declaration_attribute del_fusion_rule;

val _ =
  Theory.setup
   (Attrib.setup @{binding "stream_fusion"} (Attrib.add_del fusion_add fusion_del)
      "declaration of a rule for stream fusion" #>
    Global_Theory.add_thms_dynamic
      (@{binding "stream_fusion"}, Item_Net.content o #rules o Fusion_Rules.get));

val trace = Attrib.setup_config_bool @{binding "stream_fusion_trace"} (K false)

fun tracing ctxt msg = if Config.get ctxt trace then Output.tracing (msg ()) else ()

fun fusion_conv ctxt = Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps get_rules ctxt)

fun fusion_simproc ctxt ct =
  let
    val matches = match_consumer ctxt (Thm.term_of ct)
  in
    if matches then 
      let
        val _ = tracing ctxt (fn _ => Pretty.string_of (Pretty.block 
          [Pretty.str "Trying stream fusion on ",
           Pretty.brk 2,
           Syntax.pretty_term ctxt (Thm.term_of ct)]))
        val thm = fusion_conv ctxt ct
        val failed = Thm.is_reflexive thm orelse occur_in (get_unstream ctxt) (Thm.term_of (Thm.rhs_of thm))
        val _ = tracing ctxt (fn _ => Pretty.string_of (Pretty.block 
          [Pretty.str (if failed then "FAILED: " else "SUCCEEDED: "),
           Pretty.brk 2,
           Syntax.pretty_term ctxt (Thm.prop_of thm)]))
      in
        if failed then NONE else SOME thm
      end
    else NONE
  end

end;

