(*  Title:      monad_rules.ML
    Author:     Manuel Eberl, TU München
    Author:     Joshua Schneider, ETH Zurich
    Author:     Andreas Lochbihler, ETH Zurich

Monad laws and distributivity of bind over control operators (if, case_x ...).
*)

signature MONAD_RULES = sig
  type info = {
    bind_assoc: thm option,
    bind_commute: thm option,
    return_bind: thm option,
    bind_return: thm option
  }

  val get_monad: Proof.context -> string -> info option
  val get_monad_rules: Context.generic -> thm list
  val get_distrib_rule: Proof.context -> string -> thm option
  val get_distrib_rules: Context.generic -> thm list
end;

structure Monad_Rules : MONAD_RULES = struct

fun same_const (Const (c,_), Const (c',_)) = (c = c')
  | same_const _ = false;

fun analyze_bind_assoc thm =
  let
    val (lhs, rhs) = Thm.prop_of thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
  in
    case (lhs, rhs) of
      (c1 $ (c2 $ Var x $ Var y) $ Var z,
       c3 $ Var x' $ Abs (_, _, c4 $ (Var y' $ Bound 0) $ Var z')) =>
        if forall same_const ([c1,c2,c3] ~~ [c2,c3,c4]) andalso
            forall (op =) ([x,y,z] ~~ [x',y',z']) then
          c1
        else
          raise THM ("analyze_bind_assoc", 1, [thm])
    | _ => raise THM ("analyze_bind_assoc", 1, [thm])
  end;

fun analyze_return_bind thm =
  let
    val (lhs, rhs) = Thm.prop_of thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
  in
    case (lhs, rhs) of
      (Const (c_bind,T) $ _ $ Var x, Var x' $ Var _) =>
        if x = x' then
          Const (c_bind, T)
        else
          raise THM ("analyze_return_bind", 1, [thm])
    | _ => raise THM ("analyze_return_bind", 1, [thm])
  end;

fun analyze_bind_return thm =
  let
    val (lhs, rhs) = Thm.prop_of thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
  in
    case (lhs, rhs) of
      (Const (c_bind,T) $ Var x $ ret, Var x') =>
        if x = x' then
          (Const (c_bind, T), ret)
        else
          raise THM ("analyze_bind_return", 1, [thm])
    | _ => raise THM ("analyze_bind_return", 1, [thm])
  end;

fun analyze_bind_commute thm =
  let
    val (lhs,rhs) = Thm.prop_of thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
  in
    case (lhs,rhs) of
      (c1 $ Var x $ Abs (_,_, c2 $ Var y $ (Var z $ Bound 0)),
       c3 $ Var y' $ Abs (_,_, c4 $ Var x' $ Abs (_, _, Var z' $ Bound 0 $ Bound 1))) =>
         if forall same_const ([c1,c2,c3] ~~ [c2,c3,c4]) andalso
              forall op= ([x,y,z] ~~ [x',y',z']) then
           c1
         else
           raise THM ("analyze_bind_commute", 1, [thm])
    | _ => raise THM ("analyze_bind_commute", 1, [thm])
  end;

fun analyze_bind_distrib thm =
  let
    val (lhs, rhs) = Thm.prop_of thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
  in
    case lhs of
      Var _ $ Var x $ Abs (_, _, y) =>
        if member (op =) (Term.add_vars y []) x then
          raise THM ("analyze_bind_distrib", 1, [thm])
        else
          let val (c, c') = apply2 head_of (y, rhs)
          in
            if same_const (c, c') then c
            else raise THM ("analyze_bind_distrib", 1, [thm])
          end
    | _ => raise THM ("analyze_bind_distrib", 1, [thm])
  end;

type info = {
  bind_assoc: thm option,
  bind_commute: thm option,
  return_bind: thm option,
  bind_return: thm option
};

fun make_info bind_assoc bind_commute return_bind bind_return =
 {bind_assoc = bind_assoc, bind_commute = bind_commute, return_bind = return_bind,
  bind_return = bind_return};

val empty_info = make_info NONE NONE NONE NONE;

fun map_info f1 f2 f3 f4 {bind_assoc, bind_commute, return_bind, bind_return} =
 {bind_assoc = f1 bind_assoc, bind_commute = f2 bind_commute, return_bind = f3 return_bind,
  bind_return = f4 bind_return};

fun map_info_thms f = let val g = Option.map f in map_info g g g g end;

fun merge_info (i1, i2) =
  if pointer_eq (i1, i2) then raise Symtab.SAME
  else
    let
      val {bind_assoc = ba1, bind_commute = bc1, return_bind = rb1, bind_return = br1} = i1;
      val {bind_assoc = ba2, bind_commute = bc2, return_bind = rb2, bind_return = br2} = i2;
      val ba = merge_options (ba1, ba2);
      val bc = merge_options (bc1, bc2);
      val rb = merge_options (rb1, rb2);
      val br = merge_options (br1, br2);
    in make_info ba bc rb br end;

fun pretty_info ctxt bindc {bind_assoc, bind_commute, return_bind, bind_return} = 
  let
    fun pretty_law (_, NONE) = NONE
      | pretty_law (name, SOME thm) = SOME (Pretty.block [Pretty.str name, Pretty.brk 1, Thm.pretty_thm ctxt thm])
    val list = 
      [("return-bind:", return_bind), 
       ("bind-return:", bind_return), 
       ("bind-assoc:", bind_assoc), 
       ("bind-commute:", bind_commute)]

  in
    map_filter pretty_law list 
    |> cons (Syntax.pretty_term (Config.put Adhoc_Overloading.show_variants true ctxt) (Const (bindc, dummyT)))
    |> Pretty.fbreaks
    |> Pretty.block 
  end

structure Data = Generic_Data(
  type T = {
    monads: info Symtab.table,
    distribs: thm Symtab.table
  };
  val empty = {monads = Symtab.empty, distribs = Symtab.empty};
  val extend = I;
  fun merge ({monads = m1, distribs = d1}, {monads = m2, distribs = d2}) =
   {monads = Symtab.join (K merge_info) (m1, m2),
    distribs = Symtab.merge (K true) (d1, d2)};
);

fun map_data f1 f2 {monads, distribs} = {monads = f1 monads, distribs = f2 distribs};

fun get_monad_rules context =
  let
    fun add_simps {bind_assoc, return_bind, bind_return, ...} =
      map_filter I [bind_assoc, return_bind, bind_return];
    val {monads, ...} = Data.get context;
  in Symtab.fold (fn (_, info) => append (add_simps info)) monads [] end;

fun get_monad ctxt bindc =
  let
    val {monads, ...} = Data.get (Context.Proof ctxt);
  in Option.map (map_info_thms (Thm.transfer' ctxt)) (Symtab.lookup monads bindc) end;

fun get_distrib_rule ctxt controlc =
  let
    val {distribs, ...} = Data.get (Context.Proof ctxt);
  in Option.map (Thm.transfer' ctxt) (Symtab.lookup distribs controlc) end;

fun get_distrib_rules context =
  let
    val {distribs, ...} = Data.get context
  in Symtab.dest distribs |> map snd end;

fun add_monad_rule thm context =
  let
    fun add_rule (analyze, map_info') =
      let val (bindc, _) = dest_Const (analyze thm)
      in map_data (Symtab.map_default (bindc, empty_info) map_info') I end;
    fun put_thm _ = SOME thm;
    val add_rule' = case get_first (try add_rule)
        [(analyze_bind_assoc, map_info put_thm I I I),
         (analyze_bind_commute, map_info I put_thm I I),
         (analyze_return_bind, map_info I I put_thm I),
         (analyze_bind_return #> fst, map_info I I I put_thm)] of
      SOME f => f
    | NONE => error "Bad monad rule";
  in Data.map add_rule' context end;

fun add_distrib_rule thm context =
  let
    val (controlc, _) = dest_Const (analyze_bind_distrib thm)
      handle THM _ => error "Bad distributivity rule";
  in Data.map (map_data I (Symtab.update (controlc, thm))) context end;

fun pretty_monad_rules ctxt =
  let
    val info = Data.get (Context.Proof ctxt)
    val monads = 
      #monads info 
      |> Symtab.dest
      |> map (uncurry (pretty_info ctxt))
      |> Pretty.big_list "Monad laws"
    fun pretty_distrib (name, thm) = Pretty.block [
      Syntax.pretty_term ctxt (Const (name, dummyT)), Pretty.str ": ", Pretty.brk 0, 
      Thm.pretty_thm ctxt thm]
    val distribs =
      #distribs info
      |> Symtab.dest
      |> map pretty_distrib
      |> Pretty.big_list "Distributivity laws"
  in
    Pretty.blk (0, [monads, Pretty.fbrk, Pretty.fbrk, distribs])
  end

val add_monad_rules_simp =
  Context.map_proof (fn ctxt => ctxt addsimps (get_monad_rules (Context.Proof ctxt)))

val _ = Theory.setup
 (Attrib.setup @{binding monad_rule} (Scan.succeed (Thm.declaration_attribute add_monad_rule))
    "declaration of monad rule" #>
  Attrib.setup @{binding monad_distrib} (Scan.succeed (Thm.declaration_attribute add_distrib_rule))
    "declaration of distributive rule for monadic bind" #>
  Attrib.setup @{binding monad_rule_internal} 
    (Scan.succeed (Thm.declaration_attribute (K add_monad_rules_simp)))
    "dynamic declaration of monad rules as [simp]" #>
  Global_Theory.add_thms_dynamic (@{binding monad_rule}, get_monad_rules) #>
  Global_Theory.add_thms_dynamic (@{binding monad_distrib}, get_distrib_rules));


val _ =
  Outer_Syntax.command @{command_keyword print_monad_rules} "print monad rules"
    (Scan.succeed (Toplevel.keep (Pretty.writeln o pretty_monad_rules o Toplevel.context_of)));

end;
