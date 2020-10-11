(* Load mlyacc libraries *)

(* Yes, this requires mlton, since mlyacc is distributed with it *)
(* TODO: Fix this, or have a more generic way to handle it *)
use "/usr/lib/mlton/sml/mlyacc-lib/base.sig";
use "/usr/lib/mlton/sml/mlyacc-lib/join.sml";
use "/usr/lib/mlton/sml/mlyacc-lib/lrtable.sml";
use "/usr/lib/mlton/sml/mlyacc-lib/stream.sml";
use "/usr/lib/mlton/sml/mlyacc-lib/parser2.sml";

(* Load extracted code *)
use "rewrite_example.ML";

(* Load LTL parser *)
use "../parser/datatypes.sml";
use "../parser/ltl.yacc.sig";
use "../parser/ltl.yacc.sml";
use "../parser/ltl.lex.sml";
use "../parser/glue.sml";
use "../parser/compiler.sml";

(* Load CLI Interface *)
use "rewrite_example_cli.sml";
