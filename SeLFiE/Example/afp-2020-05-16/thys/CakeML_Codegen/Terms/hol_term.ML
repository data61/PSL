val mk_string = HOLogic.mk_string o Class_Graph.mangle
fun mk_name n = @{const Name} $ mk_string n

fun fsetT typ = Type (@{type_name fset}, [typ])
fun fmapT keyT valueT = Type (@{type_name fmap}, [keyT, valueT])

fun mk_fset typ xs =
  let
    fun f x xs = Const (@{const_name finsert}, typ --> fsetT typ --> fsetT typ) $ x $ xs
    val init = Const (@{const_name bot}, fsetT typ)
  in fold f xs init end

fun mk_fmap (keyT, valueT) xs =
  let
    val fmapT = fmapT keyT valueT
    fun f (k, v) xs = Const (@{const_name fmupd}, keyT --> valueT --> fmapT --> fmapT) $ k $ v $ xs
    val init = Const (@{const_name fmempty}, fmapT)
  in fold f xs init end

signature HOL_TERM = sig
  val mk_term: bool -> term -> term
  val mk_eq: term -> term

  val list_comb: term * term list -> term
  val strip_comb: term -> term * term list
end

structure HOL_Term : HOL_TERM = struct

fun list_comb (f, xs) =
  fold (fn x => fn t => @{const App} $ t $ x) xs f

fun strip_comb t =
  let
    fun go (@{const App} $ f $ x) = apsnd (cons f) (go x)
      | go t = (t, [])
  in apsnd rev (go t) end

fun mk_term schematic t =
  let
    fun aux (Const (n, _)) = @{const Const} $ mk_name n
      | aux (Free (n, _)) =
          if schematic then
            error "free variables are not supported"
          else
            @{const Free} $ mk_name n
      | aux (Bound i) = @{const Bound} $ HOLogic.mk_number @{typ nat} i
      | aux (t $ u) = @{const App} $ aux t $ aux u
      | aux (Abs (_, _, t)) = @{const Abs} $ aux t
      | aux (Var ((n, i), _)) =
          if schematic then
            @{const Free} $ mk_name (n ^ "." ^ Value.print_int i)
          else
            error "schematic variables are not supported"
  in aux t end

val mk_eq =
  HOLogic.mk_prod o @{apply 2} (mk_term true) o Logic.dest_equals

end