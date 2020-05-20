(* Load mlyacc libraries *)

(* Yes, this requires mlton, since mlyacc is distributed with it *)
(* TODO: Fix this, or have a more generic way to handle it *)
use "/usr/lib/mlton/sml/mlyacc-lib/base.sig";
use "/usr/lib/mlton/sml/mlyacc-lib/join.sml";
use "/usr/lib/mlton/sml/mlyacc-lib/lrtable.sml";
use "/usr/lib/mlton/sml/mlyacc-lib/stream.sml";
use "/usr/lib/mlton/sml/mlyacc-lib/parser2.sml";

(* Load Unsynchronized interface *)
use "Unsynchronized.sml";

(* Load extracted code *)
use "LTL_to_DRA.ML";

(* Load LTL parser *)
use "../../LTL/parser/datatypes.sml";
use "../../LTL/parser/ltl.yacc.sig";
use "../../LTL/parser/ltl.yacc.sml";
use "../../LTL/parser/ltl.lex.sml";
use "../../LTL/parser/glue.sml";
use "../../LTL/parser/compiler.sml";

(* Load CLI Interface *)
use "hoa.sml";
use "ltl_to_dra_cli.sml";
