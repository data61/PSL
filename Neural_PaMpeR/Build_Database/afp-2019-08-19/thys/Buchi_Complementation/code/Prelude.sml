structure Unsynchronized =
struct

datatype ref = datatype ref;

end;

fun tracing msg = TextIO.output (TextIO.stdErr, msg ^ "\n");
