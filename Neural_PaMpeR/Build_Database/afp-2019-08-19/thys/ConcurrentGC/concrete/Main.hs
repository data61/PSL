{-
 - Copyright 2015, NICTA
 -
 - This software may be distributed and modified according to the terms of
 - the BSD 2-Clause license. Note that NO WARRANTY is provided.
 - See "LICENSE_BSD2.txt" for details.
 -
 - @TAG(NICTA_BSD)
 -}

import WriteDotFile
import WriteThyFile

main = do
    contents <- readFile "input_heap.txt"
    writeFile "heap.dot" $ write_dot_file contents
    writeFile "Concrete_heap.thy" $ write_thy_file contents
