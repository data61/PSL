fun main () =
  case CommandLine.arguments () of
       [f] => Module.fileParsePrint f
     | _ => print "Filename expected\n"

val _ = main ()
