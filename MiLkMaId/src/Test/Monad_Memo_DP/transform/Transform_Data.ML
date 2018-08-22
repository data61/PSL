structure Transform_Data = struct

type dp_info = {
  old_head: term,
  new_head': term,
  new_headT: term,

  old_defs: thm list,
  new_defT: thm,
  new_def': thm list
}

type cmd_info = {
  scope: binding,
  head: term,
  locale: string option,
  dp_info: dp_info option
}

fun map_cmd_info f0 f1 f2 f3 {scope, head, locale, dp_info} =
  {scope = f0 scope, head = f1 head, locale = f2 locale, dp_info = f3 dp_info}

fun map_cmd_dp_info f = map_cmd_info I I I f

structure Data = Generic_Data (
  type T = {
    monadified_terms: (string * cmd_info Item_Net.T) list,
    last_cmd_info: cmd_info option
  }

  val empty = {
    monadified_terms =
      ["state", "heap"]
      ~~ replicate 2 (Item_Net.init (op aconv o apply2 #head) (single o #head)),
    last_cmd_info = NONE
  }

  val extend = I

  fun merge (
    {monadified_terms = m0, ...},
    {monadified_terms = m1, ...}
  ) =
    let
      val keys0 = map fst m0
      val keys1 = map fst m1
      val _ = @{assert} (keys0 = keys1)
      val vals = map Item_Net.merge (map snd m0 ~~ map snd m1)
      val ms = keys0 ~~ vals
    in
      {monadified_terms = ms, last_cmd_info = NONE}
    end
)

fun transform_dp_info phi {old_head, new_head', new_headT, old_defs, new_defT, new_def'} =
  {
    old_head = Morphism.term phi old_head,
    new_head' = Morphism.term phi new_head',
    new_headT = Morphism.term phi new_headT,
  
    old_defs = Morphism.fact phi old_defs,
    new_def' = Morphism.fact phi new_def',
    new_defT = Morphism.thm phi new_defT
  }

fun get_monadified_terms_generic monad_name ctxt =
  Data.get ctxt
  |> #monadified_terms
  |> (fn l => AList.lookup op= l monad_name)
  |> the

fun get_monadified_terms monad_name lthy =
  get_monadified_terms_generic monad_name (Context.Proof lthy)

fun map_data f0 f1 = Data.map (fn {monadified_terms, last_cmd_info} =>
  {monadified_terms = f0 monadified_terms, last_cmd_info = f1 last_cmd_info})

fun map_monadified_terms f = map_data f I
fun map_last_cmd_info f    = map_data I f

fun put_monadified_terms_generic monad_name new_terms ctxt =
  ctxt |> map_monadified_terms (AList.update op= (monad_name, new_terms))

fun map_monadified_terms_generic monad_name f ctxt =
  ctxt |> map_monadified_terms (AList.map_entry op= monad_name f)

fun put_last_cmd_info cmd_info_opt ctxt =
  map_last_cmd_info (K cmd_info_opt) ctxt

fun get_cmd_info monad_name lthy tm =
  get_monadified_terms monad_name lthy
  |> (fn net => Item_Net.retrieve net tm)

fun get_dp_info monad_name lthy tm =
  get_cmd_info monad_name lthy tm
  |> (fn result => case result of
      {dp_info = SOME dp_info', ...} :: _ => SOME dp_info'
    | _ => NONE)

fun get_last_cmd_info_generic ctxt =
  Data.get ctxt
  |> #last_cmd_info
  |> the

fun get_last_cmd_info lthy =
  get_last_cmd_info_generic (Context.Proof lthy)

fun commit_dp_info monad_name dp_info =
  Local_Theory.declaration
    {pervasive = false, syntax = false}
    (fn phi => fn ctxt =>
      let
        val old_cmd_info = get_last_cmd_info_generic ctxt
        val new_dp_info = transform_dp_info phi dp_info
        val new_cmd_info = old_cmd_info |> map_cmd_dp_info (K (SOME new_dp_info))
      in
        ctxt
        |> map_monadified_terms_generic monad_name (Item_Net.update new_cmd_info)
         |> put_last_cmd_info (SOME new_cmd_info)
      end)

fun add_tmp_cmd_info (scope, head, locale_opt) =
  Local_Theory.declaration
    {pervasive = false, syntax = false}
    (fn phi => fn ctxt =>
      let
        val new_cmd_info = {
          scope = Morphism.binding phi scope,
          head = Morphism.term phi head,
          locale = locale_opt,
          dp_info = NONE
        }
      in
        ctxt |> put_last_cmd_info (SOME new_cmd_info)
      end )

fun get_or_last_cmd_info lthy monad_name_tm_opt =
  case monad_name_tm_opt of
    NONE => get_last_cmd_info lthy
  | SOME (monad_name, tm) => get_cmd_info monad_name lthy tm |> the_single

end