theory Benchmark
imports Regex_Equivalence Spec_Check.Spec_Check
begin

definition bool_checkers :: "(string * (bool rexp \<Rightarrow> bool rexp \<Rightarrow> bool)) list" where
  "bool_checkers = [
    (''D '', check_eqv_brz),
    \<^cancel>\<open>(''DQ'', check_eqv_brzq),\<close>
    (''N '', check_eqv_n),
    (''P '', check_eqv_p),
    (''PN'', check_eqv_pn),
    (''B '', check_eqv_b),
    (''B2'', check_eqv_b2),
    (''A '', check_eqv_a),
    (''A2'', check_eqv_a2)
    ]"

definition bool_matchers :: "(string * (bool rexp \<Rightarrow> bool list \<Rightarrow> bool)) list" where
  "bool_matchers = [
    (''D '', match_brz),
    \<^cancel>\<open>(''DQ'', match_brzq),\<close>
    (''N '', match_n),
    (''P '', match_p),
    (''PN'', match_pn),
    (''B '', match_b),
    (''B2'', match_b2),
    (''A '', match_a),
    (''A2'', match_a2)
    ]"

ML \<open>
structure Rexp =
struct
  val Zero = @{code Zero};
  val One = @{code One};
  val Atom = @{code Atom};
  val Plus = @{code Plus};
  val Times = @{code Times};
  val Star = @{code Star};
  val bool_checkers = @{code bool_checkers};
  val bool_matchers = @{code bool_matchers};
end
\<close>

ML \<open>

val timeout = Time.fromSeconds 10;
datatype res = Res of bool * Time.time | TO

fun sum [] = Time.fromSeconds 0
  | sum (TO :: xs) = timeout + sum xs
  | sum (Res (_, t) :: xs) = t + sum xs

fun average xs = Time.fromReal (Time.toReal (sum xs) / real (length xs));

fun time f x =
  let
    val timer = Timer.startRealTimer ();
    val res = Timeout.apply timeout (fn () => uncurry f x) ();
    val time = Timer.checkRealTimer timer;
  in
    Res (res, time)
  end handle Timeout.TIMEOUT _ => TO;
\<close>

ML \<open>
  fun list_n 0 _ r = ([], r)
    | list_n n g r =
      let
        val (x,r) = g r
        val (xs,r) = list_n (n - 1) g r
      in (x::xs, r) end;
  fun join g r =
    let val (g', r') = g r;
    in g' r' end;

  fun regex 0 = Generator.map Rexp.Atom Generator.flip
    | regex n =
    let
      val m = Generator.selectL (0 upto n - 1);
      val plus = join (Generator.map (fn m =>
        Generator.map2 Rexp.Plus (regex m, regex (n - 1 - m))) m);
      val times = join (Generator.map (fn m =>
        Generator.map2 Rexp.Times (regex m, regex (n - 1 - m))) m);
      val star = join (Generator.map (Generator.map Rexp.Star o regex) (Generator.lift (n - 1)));
    in
      Generator.chooseL [plus, times, star]
    end;
\<close>

(*
ML {*
val checkers = drop 2 Rexp.bool_checkers
val sizes = [50,100,150,200,250];
val regexes = fst (fold_map (fn f => fn r => f r) (map (list_n 100 o regex) sizes)
  (Generator.new ()));
*}

declare [[ML_print_depth 100000]]
ML {*
fun alph Rexp.Zero = 0
  | alph Rexp.One = 0
  | alph (Rexp.Atom _) = 1
  | alph (Rexp.Plus (r, s)) = alph r + alph s
  | alph (Rexp.Times (r, s)) = alph r + alph s
  | alph (Rexp.Star r) = alph r;
map (map alph) regexes
*}
declare [[ML_print_depth 10]]
*)

ML \<open>

fun header checkers =
  warning ("n     " ^  space_implode "    " (map (String.implode o fst) checkers))
fun pad i = if i < 10 then 4
       else if i < 100 then 3
       else if i < 1000 then 2
       else if i < 10000 then 1
       else 0;
fun round n ts =
  warning (string_of_int n ^ implode (replicate (1 + pad n) " ") ^
    space_implode " " (map Time.toString ts))

fun run checkers sizes =
  let
    val regexes = fst (fold_map (fn f => fn r => f r) (map (list_n 100 o regex) sizes)
      (Generator.new ()));
    val _ = header checkers;
    val _ = map_index (fn (i, rs) =>
      let
        val n = nth sizes i;
        val ts = map (fn (_, ch) => average (map (fn r => time ch (r, r)) rs)) checkers
      in
        round n ts
      end) regexes;
  in
    ()
  end;

fun run_re mk_eq checkers sizes =
  let
    val _ = header checkers;
    val _ = map (fn n =>
      let
        val eq = mk_eq n;
        val ts = map (fn (_, ch) => case time ch eq of Res (_, t) => t | TO => timeout) checkers;
      in
        round n ts
      end) sizes;
  in
    ()
  end;
\<close>

(*
ML {* run Rexp.bool_checkers [10,20,30,40,50,100] *}
n     D     N     P     PN    B     B2    A     A2 
10    0.070 0.000 0.000 0.000 0.000 0.000 0.000 0.000 
20    1.401 0.000 0.001 0.000 0.000 0.000 0.000 0.000 
30    4.235 0.005 0.002 0.002 0.000 0.000 0.000 0.000 
40    5.080 0.089 0.005 0.004 0.000 0.000 0.000 0.000 
50    6.916 0.222 0.012 0.010 0.001 0.000 0.001 0.001 
100   9.587 2.593 0.137 0.116 0.002 0.002 0.003 0.002
*)

(*
ML {* run (drop 2 Rexp.bool_checkers) [50,100,150,200,250] *}
n     P     PN    B     B2    A     A2 
50    0.011 0.009 0.001 0.000 0.001 0.001 
100   0.136 0.112 0.002 0.002 0.004 0.003 
150   0.635 0.499 0.009 0.008 0.013 0.010 
200   2.029 1.744 0.016 0.013 0.025 0.019 
250   4.490 3.719 0.028 0.024 0.040 0.030 
*)

(*
ML {* run (drop 4 Rexp.bool_checkers) [100,200,300,400,500,600,700,800,900,1000]
n     B     B2    A     A2 
100   0.003 0.002 0.005 0.003 
200   0.023 0.019 0.033 0.025 
300   0.090 0.078 0.119 0.094 
400   0.215 0.213 0.278 0.222 
500   0.443 0.450 0.555 0.477
600   0.710 0.806 0.948 0.776
700   1.304 1.382 1.575 1.335
800   1.696 1.902 2.151 1.848 
900   2.388 2.643 2.878 2.567 
1000  2.985 3.280 3.498 3.137
*)

text \<open>Asperti's example\<close>

ML \<open>
fun pow 0 = Rexp.One
  | pow 1 = Rexp.Atom true
  | pow n = Rexp.Times (Rexp.Atom true, pow (n - 1));

fun powl 0 = Rexp.One
  | powl 1 = Rexp.Atom true
  | powl n = Rexp.Times (powl (n - 1), Rexp.Atom true);

fun sum f 0 = f 0
  | sum f n = Rexp.Plus (f n, sum f (n - 1));

fun b n = (Rexp.Times (sum pow (n - 1), Rexp.Star (pow n)), Rexp.Star (Rexp.Atom true));
fun bl n = (Rexp.Times (sum powl (n - 1), Rexp.Star (powl n)), Rexp.Star (Rexp.Atom true));

\<close>

(*
ML {* run_re b Rexp.bool_checkers [30,40,50,70,100,200] *}
ML {* run_re bl Rexp.bool_checkers [30,40,50,70,100,200] *}
ML {* run_re b (drop 1 Rexp.bool_checkers) [100,200,300,400,500] *}
ML {* run_re bl (drop 1 Rexp.bool_checkers) [100,200,300,400,500] *}
ML {* run_re b (take 3 (drop 1 Rexp.bool_checkers)) [500,600,700,800] *}
ML {* run_re bl (take 3 (drop 1 Rexp.bool_checkers)) [500,600,700,800] *}
*)
text \<open>Fischer's example (matching)\<close>

ML \<open>
fun seq n = Library.foldr1 Rexp.Times o replicate n;
fun seql n = Library.foldr1 (Rexp.Times o swap) o replicate n;
fun re n = (Rexp.Times (seq n (Rexp.Plus (Rexp.Atom true, Rexp.One)), seq n (Rexp.Atom true)),
  replicate n true);
fun rel n = (Rexp.Times (seql n (Rexp.Plus (Rexp.Atom true, Rexp.One)), seql n (Rexp.Atom true)),
  replicate n true);

\<close>

(*
ML {* run_re re Rexp.bool_matchers [30,40,50,70,100] *}
ML {* run_re rel Rexp.bool_matchers [30,40,50,70,100] *}
ML {* run_re re (drop 4 Rexp.bool_matchers) [100,300,500,700,1000,1300,1600,2000,2500,3000,4000,5000] *}
ML {* run_re rel (drop 4 Rexp.bool_matchers) [100,300,500,700,1000,1300,1600,2000,2500,3000,4000,5000] *}
*)
ML \<open>
val monster =
curry Rexp.Plus (curry Rexp.Plus (curry Rexp.Times (curry Rexp.Times (curry
Rexp.Times Rexp.One (curry Rexp.Plus (Rexp.Atom false) (Rexp.Star (curry
Rexp.Times Rexp.Zero (Rexp.Star (curry Rexp.Plus (curry Rexp.Plus (Rexp.Star
Rexp.Zero) (curry Rexp.Plus Rexp.Zero (Rexp.Star (curry Rexp.Plus Rexp.Zero
(Rexp.Atom false))))) (curry Rexp.Plus Rexp.One (Rexp.Star (curry Rexp.Times
(curry Rexp.Times (Rexp.Atom false) Rexp.Zero) (Rexp.Star Rexp.Zero))))))))))
(curry Rexp.Times (curry Rexp.Times (curry Rexp.Times (curry Rexp.Plus (curry
Rexp.Times (curry Rexp.Times (curry Rexp.Times (Rexp.Atom false) Rexp.One)
Rexp.One) (Rexp.Star (Rexp.Star (curry Rexp.Times Rexp.One Rexp.One))))
Rexp.Zero) (curry Rexp.Times (Rexp.Star (curry Rexp.Times Rexp.One (Rexp.Star
(curry Rexp.Times Rexp.One (Rexp.Star (Rexp.Atom true)))))) (curry Rexp.Times
(Rexp.Star (curry Rexp.Times (curry Rexp.Times Rexp.Zero Rexp.One) Rexp.Zero))
(curry Rexp.Times (curry Rexp.Plus (Rexp.Star (curry Rexp.Plus (curry Rexp.Plus
Rexp.Zero Rexp.Zero) (Rexp.Atom false))) (curry Rexp.Times (curry Rexp.Plus
(curry Rexp.Times (Rexp.Atom false) (Rexp.Atom true)) (Rexp.Star Rexp.Zero))
(curry Rexp.Plus (curry Rexp.Times (Rexp.Atom true) Rexp.One) Rexp.Zero)))
(Rexp.Star (curry Rexp.Plus (Rexp.Star Rexp.One) (curry Rexp.Plus (curry
Rexp.Plus (Rexp.Atom true) Rexp.Zero) (Rexp.Atom true)))))))) (curry Rexp.Plus
(curry Rexp.Times (curry Rexp.Times (curry Rexp.Plus Rexp.One (curry Rexp.Times
(curry Rexp.Times (curry Rexp.Times Rexp.One (Rexp.Atom false)) Rexp.One) (curry
Rexp.Plus (curry Rexp.Plus Rexp.One (curry Rexp.Plus Rexp.Zero Rexp.Zero))
(curry Rexp.Times (Rexp.Star Rexp.Zero) (curry Rexp.Times (Rexp.Atom false)
Rexp.Zero))))) (curry Rexp.Plus (Rexp.Star Rexp.Zero) (curry Rexp.Plus Rexp.One
(curry Rexp.Times (Rexp.Atom true) (curry Rexp.Plus Rexp.Zero Rexp.One)))))
(Rexp.Star (curry Rexp.Plus (curry Rexp.Plus (curry Rexp.Times (Rexp.Star
Rexp.Zero) (curry Rexp.Times (curry Rexp.Times Rexp.Zero Rexp.One) Rexp.One))
(Rexp.Atom false)) (curry Rexp.Times (Rexp.Star (curry Rexp.Plus (curry
Rexp.Times Rexp.Zero Rexp.One) Rexp.Zero)) (Rexp.Star (Rexp.Atom false))))))
(Rexp.Star (curry Rexp.Times (curry Rexp.Plus Rexp.One (Rexp.Atom true)) (curry
Rexp.Times (curry Rexp.Plus (curry Rexp.Plus (Rexp.Star (Rexp.Atom true))
(Rexp.Star (Rexp.Star (Rexp.Atom true)))) (curry Rexp.Times Rexp.One (curry
Rexp.Plus Rexp.Zero Rexp.Zero))) Rexp.One))))) (curry Rexp.Plus (Rexp.Star
(curry Rexp.Plus (Rexp.Star (curry Rexp.Plus (curry Rexp.Times (Rexp.Star
(Rexp.Star Rexp.Zero)) (curry Rexp.Plus (curry Rexp.Times (curry Rexp.Times
(Rexp.Atom false) (Rexp.Atom true)) Rexp.One) (Rexp.Star (Rexp.Atom false))))
(curry Rexp.Plus (curry Rexp.Plus Rexp.One (curry Rexp.Plus (curry Rexp.Times
(Rexp.Atom false) Rexp.One) (Rexp.Atom false))) (curry Rexp.Plus (curry
Rexp.Plus (Rexp.Star Rexp.Zero) (Rexp.Atom false)) (Rexp.Star (Rexp.Atom
true)))))) (curry Rexp.Times (Rexp.Star (Rexp.Star (Rexp.Atom true))) (Rexp.Star
(curry Rexp.Plus (Rexp.Star (curry Rexp.Times (Rexp.Atom true) (Rexp.Atom
false))) (curry Rexp.Times (Rexp.Star (Rexp.Star (Rexp.Atom false))) (Rexp.Atom
false))))))) (curry Rexp.Times (curry Rexp.Times (curry Rexp.Plus (Rexp.Star
(Rexp.Star (Rexp.Star (curry Rexp.Plus (curry Rexp.Plus (Rexp.Atom false)
(Rexp.Atom false)) Rexp.Zero)))) Rexp.One) (Rexp.Star (curry Rexp.Times
(Rexp.Star (curry Rexp.Plus Rexp.One (Rexp.Star (Rexp.Star Rexp.One)))) (curry
Rexp.Times (curry Rexp.Plus (curry Rexp.Plus (curry Rexp.Plus Rexp.Zero
(Rexp.Atom true)) (Rexp.Atom true)) (Rexp.Atom true)) Rexp.Zero)))) Rexp.One))))
(Rexp.Star (curry Rexp.Plus (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Plus
(Rexp.Star (curry Rexp.Times (curry Rexp.Plus (Rexp.Star Rexp.One) (Rexp.Atom
true)) (curry Rexp.Times (Rexp.Star Rexp.One) (curry Rexp.Plus (curry Rexp.Times
Rexp.One Rexp.One) (curry Rexp.Plus (curry Rexp.Plus Rexp.One (Rexp.Atom true))
(Rexp.Star (Rexp.Atom true))))))) (curry Rexp.Plus (curry Rexp.Plus (curry
Rexp.Times Rexp.One (Rexp.Star (curry Rexp.Times (curry Rexp.Times (Rexp.Atom
true) Rexp.One) (curry Rexp.Plus Rexp.One Rexp.Zero)))) (curry Rexp.Times (curry
Rexp.Times (Rexp.Atom false) (Rexp.Star Rexp.One)) (curry Rexp.Plus Rexp.One
(curry Rexp.Times (curry Rexp.Times Rexp.One Rexp.One) (curry Rexp.Times
Rexp.Zero Rexp.Zero))))) (curry Rexp.Plus (Rexp.Star (Rexp.Star (Rexp.Atom
false))) (Rexp.Star (Rexp.Star (Rexp.Star (Rexp.Atom false))))))) (curry
Rexp.Plus (curry Rexp.Times (Rexp.Star (Rexp.Star (curry Rexp.Times (curry
Rexp.Plus (curry Rexp.Times (Rexp.Atom true) Rexp.Zero) (Rexp.Star (Rexp.Atom
true))) (curry Rexp.Plus (Rexp.Atom false) (curry Rexp.Plus (Rexp.Atom true)
Rexp.One))))) (curry Rexp.Times (curry Rexp.Plus (Rexp.Star Rexp.One) (curry
Rexp.Plus (curry Rexp.Plus Rexp.One Rexp.Zero) (curry Rexp.Times Rexp.One (curry
Rexp.Plus (Rexp.Atom false) Rexp.One)))) (curry Rexp.Times (curry Rexp.Plus
(curry Rexp.Plus (curry Rexp.Plus (Rexp.Atom false) Rexp.One) (curry Rexp.Plus
(Rexp.Atom true) (Rexp.Atom false))) Rexp.Zero) (curry Rexp.Plus (curry
Rexp.Times Rexp.Zero (curry Rexp.Times Rexp.One (Rexp.Atom true))) (curry
Rexp.Plus (Rexp.Star Rexp.Zero) (curry Rexp.Plus (Rexp.Atom false)
Rexp.Zero)))))) (curry Rexp.Plus (Rexp.Star (curry Rexp.Times (curry Rexp.Times
(Rexp.Star (Rexp.Star Rexp.Zero)) (curry Rexp.Times (curry Rexp.Plus Rexp.Zero
(Rexp.Atom false)) (curry Rexp.Times Rexp.Zero Rexp.Zero))) (curry Rexp.Times
(curry Rexp.Plus (Rexp.Star Rexp.Zero) (Rexp.Atom false)) (curry Rexp.Plus
(curry Rexp.Plus Rexp.One Rexp.Zero) Rexp.One)))) (curry Rexp.Plus Rexp.One
(curry Rexp.Plus (curry Rexp.Times (Rexp.Star (curry Rexp.Times Rexp.One
Rexp.Zero)) (Rexp.Atom true)) (curry Rexp.Plus (Rexp.Star (Rexp.Atom true))
(curry Rexp.Plus Rexp.Zero (curry Rexp.Times Rexp.One Rexp.One)))))))) (curry
Rexp.Plus (curry Rexp.Plus (curry Rexp.Times (curry Rexp.Plus (Rexp.Star
(Rexp.Star (curry Rexp.Plus (curry Rexp.Times Rexp.Zero (Rexp.Atom true))
(Rexp.Star (Rexp.Atom false))))) (curry Rexp.Plus Rexp.One (curry Rexp.Plus
(Rexp.Star Rexp.One) (Rexp.Atom true)))) (curry Rexp.Times (curry Rexp.Times
(Rexp.Star (Rexp.Star (Rexp.Atom true))) (Rexp.Atom false)) (Rexp.Star (curry
Rexp.Times (curry Rexp.Plus Rexp.One Rexp.One) (curry Rexp.Times (Rexp.Star
Rexp.One) (Rexp.Star Rexp.One)))))) (curry Rexp.Times (Rexp.Star Rexp.Zero)
Rexp.One)) (curry Rexp.Times (Rexp.Star (curry Rexp.Times (Rexp.Star (Rexp.Star
(Rexp.Star (curry Rexp.Times Rexp.One Rexp.One)))) (Rexp.Star (Rexp.Star
Rexp.One)))) (curry Rexp.Times (curry Rexp.Plus (Rexp.Star (Rexp.Atom false))
(curry Rexp.Plus (curry Rexp.Times (curry Rexp.Times (curry Rexp.Plus Rexp.One
(Rexp.Atom false)) Rexp.Zero) Rexp.Zero) Rexp.One)) (Rexp.Star (Rexp.Star (curry
Rexp.Plus (Rexp.Star (curry Rexp.Times (Rexp.Atom true) Rexp.One)) (Rexp.Star
(Rexp.Atom true))))))))) (curry Rexp.Plus (Rexp.Star (Rexp.Star (curry
Rexp.Times (curry Rexp.Plus (Rexp.Star (Rexp.Star Rexp.One)) (Rexp.Star
(Rexp.Star (Rexp.Star Rexp.Zero)))) (Rexp.Atom true)))) (Rexp.Atom false)))))
(Rexp.Star (curry Rexp.Times (curry Rexp.Plus (Rexp.Star (curry Rexp.Times
(curry Rexp.Times (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Times
(Rexp.Star (curry Rexp.Times (Rexp.Star Rexp.Zero) (curry Rexp.Times Rexp.Zero
Rexp.Zero))) (curry Rexp.Plus (curry Rexp.Times Rexp.Zero Rexp.Zero) (Rexp.Star
Rexp.Zero))) Rexp.One) (Rexp.Star (Rexp.Star (Rexp.Atom true)))) Rexp.Zero)
(curry Rexp.Times (Rexp.Star (curry Rexp.Times Rexp.Zero (Rexp.Star (Rexp.Star
(curry Rexp.Plus Rexp.One (Rexp.Star Rexp.Zero)))))) (curry Rexp.Times (curry
Rexp.Plus (curry Rexp.Times Rexp.One Rexp.One) (Rexp.Star Rexp.One)) (curry
Rexp.Plus Rexp.One (curry Rexp.Times (Rexp.Atom true) (Rexp.Atom false)))))))
(curry Rexp.Times (Rexp.Star (Rexp.Star (Rexp.Star (curry Rexp.Plus (curry
Rexp.Plus (curry Rexp.Plus Rexp.One (Rexp.Star (Rexp.Atom true))) (curry
Rexp.Plus (curry Rexp.Times Rexp.Zero Rexp.Zero) (Rexp.Star Rexp.Zero))) (curry
Rexp.Plus (curry Rexp.Times (curry Rexp.Times Rexp.Zero Rexp.One) (curry
Rexp.Plus Rexp.One (Rexp.Atom false))) (Rexp.Star Rexp.One)))))) (Rexp.Star
(curry Rexp.Plus (curry Rexp.Times (curry Rexp.Plus (Rexp.Star (Rexp.Star
(Rexp.Atom true))) (curry Rexp.Plus (curry Rexp.Plus Rexp.Zero (curry Rexp.Plus
Rexp.Zero Rexp.One)) (curry Rexp.Times (Rexp.Atom true) Rexp.One))) (Rexp.Star
(curry Rexp.Plus Rexp.One (curry Rexp.Times (Rexp.Atom true) (curry Rexp.Plus
Rexp.One (Rexp.Star Rexp.Zero)))))) (curry Rexp.Times Rexp.Zero (Rexp.Star
(Rexp.Star (curry Rexp.Times Rexp.Zero (curry Rexp.Times (Rexp.Atom false)
(curry Rexp.Times (Rexp.Atom true) (Rexp.Atom true))))))))))) (curry Rexp.Times
(curry Rexp.Plus Rexp.Zero (Rexp.Star (Rexp.Star (curry Rexp.Times (Rexp.Atom
false) (curry Rexp.Plus (curry Rexp.Plus (Rexp.Star (Rexp.Atom true)) (Rexp.Star
(curry Rexp.Times (curry Rexp.Times Rexp.Zero Rexp.One) (Rexp.Atom false))))
(Rexp.Star (curry Rexp.Plus (Rexp.Atom true) (curry Rexp.Times (curry Rexp.Times
Rexp.Zero Rexp.Zero) (Rexp.Star (Rexp.Atom false)))))))))) (curry Rexp.Times
(curry Rexp.Times (Rexp.Star (curry Rexp.Plus (curry Rexp.Times (curry
Rexp.Times (curry Rexp.Plus (curry Rexp.Times Rexp.Zero (Rexp.Star Rexp.One))
(curry Rexp.Plus Rexp.One Rexp.Zero)) (curry Rexp.Plus (curry Rexp.Plus (curry
Rexp.Plus Rexp.One (Rexp.Atom false)) (curry Rexp.Plus Rexp.Zero Rexp.Zero))
Rexp.One)) Rexp.One) (Rexp.Star (curry Rexp.Times (Rexp.Star Rexp.Zero)
(Rexp.Star (curry Rexp.Plus (Rexp.Atom true) Rexp.Zero)))))) (curry Rexp.Plus
(curry Rexp.Times (curry Rexp.Times (Rexp.Atom false) (Rexp.Star (Rexp.Star
(Rexp.Star Rexp.Zero)))) (curry Rexp.Plus (Rexp.Star (curry Rexp.Plus Rexp.Zero
Rexp.Zero)) (curry Rexp.Plus (Rexp.Atom false) (curry Rexp.Plus (Rexp.Star
(curry Rexp.Plus Rexp.One (Rexp.Atom true))) (curry Rexp.Plus (curry Rexp.Times
(Rexp.Atom true) Rexp.Zero) Rexp.One))))) (curry Rexp.Times (curry Rexp.Plus
(curry Rexp.Plus Rexp.Zero (Rexp.Star (curry Rexp.Times (Rexp.Atom false) (curry
Rexp.Plus Rexp.Zero Rexp.One)))) (curry Rexp.Times (curry Rexp.Times (curry
Rexp.Plus (Rexp.Star Rexp.Zero) (curry Rexp.Times Rexp.Zero (Rexp.Atom false)))
(curry Rexp.Plus Rexp.Zero Rexp.One)) Rexp.Zero)) (curry Rexp.Plus (Rexp.Star
(curry Rexp.Times Rexp.Zero (curry Rexp.Plus Rexp.Zero Rexp.Zero))) (Rexp.Star
Rexp.One))))) (curry Rexp.Times (Rexp.Star (curry Rexp.Plus (Rexp.Star Rexp.One)
(curry Rexp.Plus (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Times (curry
Rexp.Times (Rexp.Atom false) (Rexp.Atom false)) (Rexp.Atom true)) (curry
Rexp.Times (Rexp.Atom true) (curry Rexp.Times Rexp.Zero (Rexp.Atom true))))
Rexp.One) (curry Rexp.Times (curry Rexp.Times (Rexp.Atom true) (Rexp.Star
Rexp.Zero)) Rexp.Zero)))) (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Times
(Rexp.Star (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Times (Rexp.Atom
false) Rexp.Zero) Rexp.Zero) (Rexp.Star (Rexp.Star Rexp.One)))) (curry Rexp.Plus
(curry Rexp.Plus (Rexp.Star Rexp.Zero) Rexp.One) Rexp.One)) (Rexp.Star (curry
Rexp.Plus (curry Rexp.Plus (Rexp.Atom false) (curry Rexp.Plus Rexp.Zero (curry
Rexp.Plus Rexp.One (Rexp.Atom false)))) (curry Rexp.Plus (curry Rexp.Times
(curry Rexp.Plus Rexp.Zero (Rexp.Atom true)) (curry Rexp.Times (Rexp.Atom true)
Rexp.One)) (curry Rexp.Plus (curry Rexp.Plus Rexp.One Rexp.One) (Rexp.Atom
true)))))) (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Plus (Rexp.Atom false)
(Rexp.Star (Rexp.Star (curry Rexp.Times Rexp.Zero Rexp.One)))) Rexp.Zero)
Rexp.Zero)))))))) (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Plus (Rexp.Atom
false) (curry Rexp.Plus (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Plus
(curry Rexp.Times (curry Rexp.Plus (Rexp.Star Rexp.One) (Rexp.Star Rexp.Zero))
(curry Rexp.Times Rexp.Zero (Rexp.Atom false))) (curry Rexp.Times (Rexp.Star
(Rexp.Star (Rexp.Atom false))) Rexp.One)) Rexp.One) (curry Rexp.Plus (Rexp.Star
(curry Rexp.Times (curry Rexp.Plus (curry Rexp.Plus Rexp.One (curry Rexp.Plus
Rexp.One (Rexp.Atom false))) Rexp.One) (curry Rexp.Times (curry Rexp.Plus
Rexp.One Rexp.One) (Rexp.Star (curry Rexp.Times (curry Rexp.Plus (Rexp.Star
Rexp.Zero) (curry Rexp.Times (Rexp.Atom true) (Rexp.Atom true))) Rexp.Zero)))))
(curry Rexp.Plus Rexp.One (curry Rexp.Times (curry Rexp.Times (curry Rexp.Plus
(Rexp.Star (curry Rexp.Times (curry Rexp.Plus Rexp.One (Rexp.Atom true))
Rexp.One)) (Rexp.Star (Rexp.Star Rexp.Zero))) Rexp.Zero) (Rexp.Star (curry
Rexp.Plus Rexp.Zero (Rexp.Star (curry Rexp.Times (curry Rexp.Times (Rexp.Atom
false) Rexp.Zero) (curry Rexp.Times Rexp.Zero Rexp.Zero))))))))) (curry
Rexp.Times (curry Rexp.Times (curry Rexp.Times (curry Rexp.Times Rexp.One
(Rexp.Star (curry Rexp.Plus (curry Rexp.Times (Rexp.Star (curry Rexp.Plus
(Rexp.Atom false) Rexp.Zero)) Rexp.One) (curry Rexp.Times (curry Rexp.Plus
(Rexp.Atom true) (curry Rexp.Times (Rexp.Atom true) Rexp.One)) (Rexp.Atom
false))))) (curry Rexp.Times (Rexp.Star (Rexp.Star (curry Rexp.Plus (curry
Rexp.Plus (Rexp.Star (Rexp.Atom false)) Rexp.Zero) Rexp.One))) (Rexp.Star (curry
Rexp.Plus (curry Rexp.Plus Rexp.One (curry Rexp.Times (curry Rexp.Plus
(Rexp.Atom true) (Rexp.Atom true)) (curry Rexp.Times Rexp.One (Rexp.Atom
true)))) (curry Rexp.Plus (Rexp.Atom true) (curry Rexp.Times Rexp.One (curry
Rexp.Plus (Rexp.Atom true) Rexp.One))))))) (curry Rexp.Times (curry Rexp.Plus
(curry Rexp.Times (curry Rexp.Plus (Rexp.Star (Rexp.Star (Rexp.Atom false)))
(Rexp.Star (curry Rexp.Times Rexp.One (Rexp.Star (Rexp.Atom true))))) (Rexp.Star
(Rexp.Atom true))) (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Plus (curry
Rexp.Plus Rexp.One (curry Rexp.Times Rexp.One Rexp.One)) (Rexp.Atom false))
(Rexp.Atom false)) (curry Rexp.Times (Rexp.Star (Rexp.Star Rexp.One)) (Rexp.Star
(curry Rexp.Times (Rexp.Star Rexp.One) Rexp.One))))) (curry Rexp.Times
(Rexp.Atom false) (Rexp.Atom false)))) (Rexp.Star (curry Rexp.Plus (curry
Rexp.Times (curry Rexp.Plus (curry Rexp.Plus (curry Rexp.Times Rexp.One (curry
Rexp.Times Rexp.Zero (Rexp.Atom false))) (Rexp.Star (Rexp.Star (Rexp.Atom
true)))) (Rexp.Star (curry Rexp.Times (curry Rexp.Plus (Rexp.Star (Rexp.Atom
true)) (curry Rexp.Plus Rexp.One Rexp.Zero)) Rexp.Zero))) (Rexp.Star (curry
Rexp.Plus Rexp.Zero (Rexp.Atom false)))) (curry Rexp.Times (curry Rexp.Times
(Rexp.Star (Rexp.Star (Rexp.Atom false))) (Rexp.Star Rexp.Zero)) (curry
Rexp.Plus (curry Rexp.Plus (Rexp.Star (Rexp.Star Rexp.One)) Rexp.One) (Rexp.Star
(curry Rexp.Plus (curry Rexp.Plus (Rexp.Atom false) Rexp.One) (curry Rexp.Plus
(Rexp.Star (Rexp.Atom true)) (curry Rexp.Plus Rexp.One Rexp.Zero)))))))))))
(Rexp.Star (curry Rexp.Times (Rexp.Atom false) (Rexp.Star (curry Rexp.Plus
(Rexp.Star (curry Rexp.Times Rexp.Zero (curry Rexp.Times (Rexp.Star (curry
Rexp.Plus (curry Rexp.Plus (curry Rexp.Times Rexp.One Rexp.Zero) (curry
Rexp.Plus Rexp.Zero Rexp.One)) (curry Rexp.Times (curry Rexp.Plus Rexp.One
Rexp.Zero) (curry Rexp.Plus Rexp.Zero Rexp.Zero)))) (Rexp.Star (curry Rexp.Times
(curry Rexp.Plus (curry Rexp.Plus Rexp.Zero Rexp.Zero) (curry Rexp.Times
(Rexp.Atom true) (Rexp.Atom true))) (curry Rexp.Times (curry Rexp.Plus
(Rexp.Atom true) Rexp.One) Rexp.Zero)))))) (curry Rexp.Times Rexp.One (curry
Rexp.Plus (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Times Rexp.One (curry
Rexp.Times (Rexp.Atom true) (Rexp.Atom true))) (Rexp.Star Rexp.One)) (curry
Rexp.Times Rexp.One (Rexp.Star (curry Rexp.Plus (curry Rexp.Plus Rexp.Zero
Rexp.One) (Rexp.Star Rexp.Zero))))) (curry Rexp.Times (curry Rexp.Times
Rexp.Zero (curry Rexp.Times Rexp.One (curry Rexp.Plus (curry Rexp.Times
(Rexp.Atom true) (Rexp.Atom false)) (Rexp.Atom false)))) (curry Rexp.Times
(Rexp.Star (curry Rexp.Times (curry Rexp.Times (Rexp.Atom true) (Rexp.Atom
false)) (curry Rexp.Times (Rexp.Atom true) Rexp.Zero))) (curry Rexp.Times
Rexp.Zero Rexp.One)))))))))) (curry Rexp.Plus (curry Rexp.Plus (curry Rexp.Plus
Rexp.Zero (curry Rexp.Times (Rexp.Star Rexp.One) (curry Rexp.Times (Rexp.Star
(curry Rexp.Times (Rexp.Star Rexp.Zero) (Rexp.Atom true))) (Rexp.Star (curry
Rexp.Plus (Rexp.Atom true) (curry Rexp.Times (Rexp.Atom true) (curry Rexp.Plus
(curry Rexp.Times (curry Rexp.Plus (Rexp.Atom false) Rexp.Zero) (curry
Rexp.Times Rexp.One (Rexp.Atom true))) (Rexp.Star (curry Rexp.Times (curry
Rexp.Times (Rexp.Atom false) (Rexp.Atom false)) Rexp.Zero))))))))) (curry
Rexp.Times (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Times (Rexp.Star
(curry Rexp.Plus (Rexp.Star (Rexp.Star (curry Rexp.Plus (Rexp.Atom false)
(Rexp.Star Rexp.One)))) (curry Rexp.Plus (Rexp.Atom true) (curry Rexp.Times
(Rexp.Star Rexp.Zero) (Rexp.Atom false))))) (Rexp.Atom true)) (curry Rexp.Times
(curry Rexp.Plus (curry Rexp.Plus Rexp.One (Rexp.Star (Rexp.Star Rexp.One)))
(curry Rexp.Plus (Rexp.Star (curry Rexp.Times (curry Rexp.Times (curry
Rexp.Times Rexp.One Rexp.One) (Rexp.Atom false)) (Rexp.Star (Rexp.Atom true))))
(Rexp.Atom false))) Rexp.One)) (curry Rexp.Times (curry Rexp.Times (curry
Rexp.Plus (curry Rexp.Plus (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Times
Rexp.One (curry Rexp.Times (Rexp.Atom false) (Rexp.Atom false))) (Rexp.Star
(Rexp.Star Rexp.Zero))) (Rexp.Star (curry Rexp.Times (Rexp.Atom true)
Rexp.Zero))) (curry Rexp.Plus (Rexp.Star Rexp.Zero) (curry Rexp.Times (Rexp.Star
Rexp.Zero) Rexp.Zero))) (Rexp.Star (curry Rexp.Plus Rexp.One (curry Rexp.Times
Rexp.One (curry Rexp.Plus (Rexp.Atom true) (Rexp.Atom true)))))) (curry
Rexp.Plus (Rexp.Star (curry Rexp.Plus (curry Rexp.Times (curry Rexp.Times (curry
Rexp.Plus Rexp.Zero Rexp.Zero) (Rexp.Atom false)) Rexp.Zero) (Rexp.Atom false)))
(curry Rexp.Times (curry Rexp.Times Rexp.Zero (Rexp.Star (Rexp.Star (Rexp.Atom
true)))) (curry Rexp.Plus (curry Rexp.Times (curry Rexp.Times Rexp.One Rexp.One)
(Rexp.Star Rexp.Zero)) (Rexp.Star (curry Rexp.Plus (Rexp.Atom true)
Rexp.One)))))) (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Times (Rexp.Star
(curry Rexp.Plus (curry Rexp.Plus Rexp.Zero (Rexp.Atom true)) Rexp.Zero))
Rexp.Zero) (Rexp.Star (curry Rexp.Plus (Rexp.Star (curry Rexp.Times (curry
Rexp.Plus Rexp.Zero (Rexp.Atom true)) (Rexp.Star Rexp.One))) Rexp.One)))
Rexp.Zero))) (curry Rexp.Plus (curry Rexp.Plus (curry Rexp.Plus (Rexp.Star
(curry Rexp.Times (Rexp.Star (curry Rexp.Times (curry Rexp.Plus Rexp.Zero
Rexp.One) (curry Rexp.Times (curry Rexp.Plus Rexp.Zero Rexp.One) (Rexp.Atom
true)))) (curry Rexp.Times (Rexp.Star (curry Rexp.Plus (curry Rexp.Plus Rexp.One
(Rexp.Atom false)) (curry Rexp.Plus Rexp.Zero (Rexp.Atom true)))) (Rexp.Star
(Rexp.Star Rexp.Zero))))) (curry Rexp.Times Rexp.Zero (curry Rexp.Times Rexp.One
Rexp.Zero))) (curry Rexp.Times (curry Rexp.Times (curry Rexp.Times (Rexp.Star
(curry Rexp.Plus (curry Rexp.Plus (Rexp.Star Rexp.Zero) Rexp.Zero) (Rexp.Atom
true))) (curry Rexp.Times (Rexp.Star (Rexp.Atom true)) Rexp.One)) (curry
Rexp.Times (curry Rexp.Times (curry Rexp.Times (Rexp.Star (Rexp.Star (Rexp.Atom
false))) (curry Rexp.Times (curry Rexp.Times (Rexp.Atom true) (Rexp.Atom false))
(Rexp.Atom true))) (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Plus
(Rexp.Atom true) Rexp.One) Rexp.Zero) (curry Rexp.Times Rexp.One Rexp.Zero)))
(Rexp.Star Rexp.Zero))) (curry Rexp.Plus (Rexp.Star (Rexp.Atom false))
(Rexp.Star (curry Rexp.Times (curry Rexp.Plus (curry Rexp.Times Rexp.One (curry
Rexp.Plus (Rexp.Atom false) Rexp.Zero)) Rexp.Zero) (curry Rexp.Plus (curry
Rexp.Times Rexp.One (Rexp.Atom false)) (Rexp.Atom true))))))) (curry Rexp.Times
(Rexp.Star (Rexp.Atom false)) (Rexp.Star (curry Rexp.Times (Rexp.Star (Rexp.Atom
true)) (curry Rexp.Plus (Rexp.Star (curry Rexp.Plus (Rexp.Star (curry Rexp.Times
Rexp.One (Rexp.Atom false))) (curry Rexp.Plus Rexp.One (curry Rexp.Times
Rexp.One Rexp.Zero)))) (Rexp.Star (Rexp.Star (curry Rexp.Times (Rexp.Atom false)
(Rexp.Star Rexp.Zero))))))))))) (Rexp.Star (curry Rexp.Plus (curry Rexp.Plus
(curry Rexp.Times (curry Rexp.Plus (Rexp.Star (curry Rexp.Times (curry
Rexp.Times (Rexp.Atom false) (Rexp.Star (curry Rexp.Plus (Rexp.Star Rexp.Zero)
(curry Rexp.Times Rexp.Zero (Rexp.Atom false))))) (curry Rexp.Times (curry
Rexp.Times Rexp.One (curry Rexp.Plus (Rexp.Star Rexp.Zero) (curry Rexp.Plus
Rexp.Zero Rexp.One))) Rexp.One))) (Rexp.Atom true)) Rexp.Zero) (Rexp.Star (curry
Rexp.Plus (Rexp.Star (curry Rexp.Times (curry Rexp.Times (Rexp.Atom false)
(curry Rexp.Plus (Rexp.Star (curry Rexp.Times Rexp.Zero (Rexp.Atom false)))
Rexp.Zero)) (curry Rexp.Times (Rexp.Star Rexp.Zero) (curry Rexp.Times Rexp.Zero
(Rexp.Star (curry Rexp.Times (Rexp.Atom false) Rexp.One)))))) (curry Rexp.Plus
Rexp.One (curry Rexp.Times (curry Rexp.Plus (Rexp.Star (curry Rexp.Times (curry
Rexp.Times Rexp.One Rexp.Zero) (Rexp.Star Rexp.One))) (curry Rexp.Plus (curry
Rexp.Plus (Rexp.Atom true) (Rexp.Star Rexp.Zero)) Rexp.Zero)) (Rexp.Star (curry
Rexp.Plus Rexp.One (curry Rexp.Plus (curry Rexp.Times Rexp.Zero Rexp.One) (curry
Rexp.Plus (Rexp.Atom true) (Rexp.Atom false)))))))))) (Rexp.Star (Rexp.Star
(Rexp.Star (Rexp.Star (Rexp.Atom true)))))))));
\<close>

(*
ML {* run_re (K (monster, monster)) Rexp.bool_checkers [1] *}
*)

ML \<open>
fun runTO checker sizes =
  let
    val regexes = fst (fold_map (fn f => fn r => f r) (map (list_n 1000 o regex) sizes)
      (Generator.new ()));
    val _ = map (fn rs =>
      let
        fun print (TO, i) = (warning (@{make_string} (nth rs i)); TO)
          | print (t, i) = (warning (string_of_int i); t);
        val ts = map_index (fn (i, r) => print (time (snd checker) (r, r), i)) rs
        val _ = warning (String.implode (fst checker))
      in
        warning (Time.toString (average ts))
      end) regexes;
  in
    ()
  end;
\<close>

ML \<open>local open Rexp in

 val evil =

 Star (Star (Star (Times (Times (Star (Star (Atom false)), Plus (Star (Star (Plus (Times (Atom
 false, Plus (Atom false, Atom true)), Times (Times (Times (Atom false, Plus (Atom true, Atom
 false)), Times (Atom true, Atom false)), Times (Star (Times (Times (Atom true, Atom false), Atom
 true)), Atom false))))), Times (Times (Plus (Atom false, Plus (Atom true, Atom true)), Atom true),
 Star (Plus (Atom false, Atom true))))), Plus (Atom false, Star (Atom false))))))

end
\<close>
(*
ML {* snd (nth Rexp.bool_checkers 1) evil evil *}

ML {*
  runTO (nth Rexp.bool_checkers 1) [28]
*}
*)

end
