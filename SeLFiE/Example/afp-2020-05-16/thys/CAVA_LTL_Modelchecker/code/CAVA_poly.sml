use "Unsynchronized.sml";
structure L = List;
use "CAVA_Export.sml";
structure List = L;
structure IsaArith = Arith;

structure CAVA_Support = struct
  val isMLton = false
  val objSize = PolyML.objSize
  val max_rss = fn () => 
    let 
      val size = #sizeHeap (PolyML.Statistics.getLocalStats ())
    in
      floor (real size / 1024.0)
    end
end;

(* Yes, this requires mlton *)
(* TODO: Fix this, or have a more generic way to handle it *)
use "/usr/lib/mlton/sml/mlyacc-lib/base.sig";
use "/usr/lib/mlton/sml/mlyacc-lib/join.sml";
use "/usr/lib/mlton/sml/mlyacc-lib/lrtable.sml";
use "/usr/lib/mlton/sml/mlyacc-lib/stream.sml";
use "/usr/lib/mlton/sml/mlyacc-lib/parser2.sml";

use "ltl/datatypes.sml";
use "ltl/ltl.yacc.sig";
use "ltl/ltl.yacc.sml";
use "ltl/ltl.lex.sml";
use "ltl/glue.sml";
use "ltl/compiler.sml";

use "Arith.sml";
use "CAVA.sml";

(* PolyML.export("CAVA_poly", main); *)
