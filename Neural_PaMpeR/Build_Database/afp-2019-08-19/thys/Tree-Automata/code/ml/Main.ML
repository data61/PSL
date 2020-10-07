(*
  Performance check for tree automata stuff
*)
use "Unsynchronized.ML";
use "test_setup.ML";

use "pt_examples.ML";

fun doTest (a1,a2) = htai_is_empty_witness (htai_prod a1 a2);
fun doTestWR (a1,a2) = htai_is_empty_witness (htai_prodWR a1 a2);

val start = Time.now();
val res1 = (map doTest allTests);
val rt = Time.toMilliseconds (Time.now() - start);

val start = Time.now();
val res2 = (map doTestWR allTests);
val rtWR = Time.toMilliseconds (Time.now() - start);


print ("[SML/polyml]! Time: " ^ Int.toString rt ^ "\n");
print ("[SML/polyml]! Time (WR): " ^ Int.toString rtWR ^ "\n");
print (concpad("\n", map pretty_witness res1));
print (concpad("\n", map pretty_witness res2));
