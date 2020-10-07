(*  Title:       Data refinement of representation of a file
    Authors:     Karen Zee <kkz at mit.edu> and Viktor Kuncak <vkuncak at mit.edu>
    Maintainer:  Karen Zee <kkz at mit.edu>
    License:     LGPL
*)

section "Data refinement of representation of a file"
theory FileRefinement imports Complex_Main CArrays ResizableArrays begin

text \<open>
  We describe a file at
  two levels of abstraction: an abstract file, represented as a resizable array, and
  a concrete file, represented using data blocks.
  We consider the following operations:
\begin{verbatim}
makeAFS     :: AFile
afsRead     :: "AFile => nat \<rightharpoonup> byte"
afsWrite    :: "AFile => nat => byte \<rightharpoonup> AFile"
afsFileSize :: "AFile => nat"
\end{verbatim}
\<close>

typedecl
  \<comment> \<open>unit of file content\<close>
  byte
consts
  \<comment> \<open>value used for padding\<close>
  fillByte :: byte

axiomatization
  blockSize :: nat  \<comment> \<open>in bytes\<close> and
  numBlocks :: nat  \<comment> \<open>total number of blocks in the file system\<close>
where
  nonZeroBlockSize: "blockSize > 0" and
  nonZeroNumBlocks: "numBlocks > 0"

(* ------------------------------------------------------------ *)
subsection \<open>Abstract File\<close>

type_synonym AFile = "byte rArray" \<comment> \<open>abstract file is a resizable array of bytes\<close>

definition makeAF :: AFile
 where  \<comment> \<open>initial file has size 0\<close>
  "makeAF == (0, % index. fillByte)"

definition afSize :: "AFile => nat" where
  \<comment> \<open>file size is the length of the resizable array\<close>
  "afSize afile == fst afile"

definition afRead :: "AFile => nat \<rightharpoonup> byte" where
  \<comment> \<open>reading from a file looks up the byte, reporting @{term None} if the index is out of file bounds\<close>
  "afRead afile byteIndex == 
   if byteIndex < fst afile then Some ((snd afile) byteIndex) else None"

definition afWrite :: "AFile => nat => byte \<rightharpoonup> AFile" where
  \<comment> \<open>writing to a file updates the file content and extends the file if there is enough space\<close>
  "afWrite afile byteIndex value == 
   if byteIndex div blockSize < numBlocks then
     Some (raWrite afile byteIndex value fillByte)
   else None"

(* ------------------------------------------------------------ *)
subsection \<open>Concrete File\<close>

type_synonym Block = "byte cArray" \<comment> \<open>array of @{term blockSize} bytes\<close>

record CFile =
  fileSize      :: nat \<comment> \<open>in bytes\<close>
  nextFreeBlock :: nat \<comment> \<open>next block available for allocation\<close>
  data          :: "Block cArray" \<comment> \<open>array of up to @{term numBlocks} blocks\<close>

definition makeCF :: CFile
 where  \<comment> \<open>initial file has no allocated blocks\<close>
  "makeCF ==
   (| fileSize      = 0,
      nextFreeBlock = 0,
      data          = makeCArray numBlocks (makeCArray blockSize fillByte)
   |)"

definition cfSize :: "CFile => nat" where
  "cfSize cfile == fileSize cfile"


definition cfRead :: "CFile => nat \<rightharpoonup> byte" where
  \<comment> \<open>Looks up correct data block and reads its content,
        if byteIndex is within bounds, else returns None.\<close>
  "cfRead cfile byteIndex ==
   if byteIndex < fileSize cfile then 
     (let i = byteIndex div blockSize in 
       (let j = byteIndex mod blockSize in
         Some (readCArray (readCArray (data cfile) i) j)))
   else None"

subsubsection \<open>Writing File\<close>

text \<open>We first present some auxiliary operations.\<close>

definition cfWriteNoExtend :: "CFile => nat => byte => CFile" where
  \<comment> \<open>Writing to a file when
        @{term byteIndex} is within bounds.\<close>
  "cfWriteNoExtend cfile byteIndex value ==
   let i = byteIndex div blockSize in
     let j = byteIndex mod blockSize in
       let block = readCArray (data cfile) i in
         cfile(| data := 
                 writeCArray (data cfile) i (writeCArray block j value) |)"

definition cfExtendFile :: "CFile => nat => CFile" where
  \<comment> \<open>Writing to a file when
        @{term byteIndex} is out of bounds.  Involves
        allocating a new block.\<close>
  "cfExtendFile cfile byteIndex ==
     cfile(| fileSize := Suc byteIndex,
             nextFreeBlock := Suc (byteIndex div blockSize) |)"

text \<open>The main file write operation.\<close>

definition cfWrite :: "CFile => nat => byte \<rightharpoonup> CFile" where
  \<comment> \<open>Writes the file at byte location byteIndex, automatically extending
   the file to that byte location if byteIndex is not within bounds.\<close>
  "cfWrite cfile byteIndex value ==
     if byteIndex div blockSize < numBlocks then
       if byteIndex < fileSize cfile then
         Some (cfWriteNoExtend cfile byteIndex value)
       else
         Some (cfWriteNoExtend (cfExtendFile cfile byteIndex) byteIndex value)
     else None"

(* ---------------------------------------------------------------*)
subsection \<open>Reachability Invariants for Concrete File\<close>

definition nextFreeBlockInvariant :: "CFile => bool" where
  "nextFreeBlockInvariant state ==
   (fileSize state + blockSize - 1) div blockSize = nextFreeBlock state"

definition unallocatedBlocksInvariant :: "CFile => bool" where
  \<comment> \<open>This invariant of the implementation is needed to prove
   writeExtendCorrect. It says that any unallocated block contains
   fillByte's.\<close>
  "unallocatedBlocksInvariant state ==
   \<forall>blockNum i . 
     ~ blockNum < nextFreeBlock state & blockNum < numBlocks & i < blockSize 
     --> data state blockNum i = fillByte"

definition lastBlockInvariant :: "CFile => bool" where
  "lastBlockInvariant state ==
   \<forall>index .
     ~ index < fileSize state & nextFreeBlock state = index div blockSize + 1
     --> data state (index div blockSize) (index mod blockSize) = fillByte"

definition reachabilityInvariant :: "CFile => bool" where
  "reachabilityInvariant cfile == 
      nextFreeBlockInvariant cfile &
      unallocatedBlocksInvariant cfile &
      lastBlockInvariant cfile"

(* ---------------------------------------------------------------*)
subsection \<open>Initial File Satisfies Invariants\<close>

text \<open>We prove each invariant individually and then summarize.\<close>

lemma nextFreeBlockInvariant1:
  "nextFreeBlockInvariant makeCF"
apply (simp add: nextFreeBlockInvariant_def makeCF_def)
apply (simp add: nonZeroBlockSize)
done

lemma unallocatedBlocksInvariant1:
  "unallocatedBlocksInvariant makeCF"
apply (simp add: unallocatedBlocksInvariant_def makeCF_def)
apply (simp add: makeCArray_def)
done

lemma lastBlockInvariant1:
  "lastBlockInvariant makeCF"
by (simp add: lastBlockInvariant_def makeCF_def)

lemma makeCFpreserves: "reachabilityInvariant makeCF"
by (simp add: reachabilityInvariant_def
              nextFreeBlockInvariant1
              unallocatedBlocksInvariant1
              lastBlockInvariant1)

(* ---------------------------------------------------------------*)
subsection \<open>Properties of Concrete File Operations\<close>

lemma cfWriteNoExtendPreservesFileSize:
  "[| index < fileSize cfile1;
      cfWrite cfile1 index value = Some cfile2
   |] ==> 
   fileSize cfile2 = fileSize cfile1"
apply (simp add: cfWrite_def)
apply (case_tac "index div blockSize < numBlocks", simp_all)
apply (simp add: cfWriteNoExtend_def Let_def)
apply force
done

lemma cfWriteExtendFileSize:
  "[| ~ index < fileSize cfile1;
      cfWrite cfile1 index value = Some cfile2
   |] ==> fileSize cfile2 = Suc index"
apply (simp add: cfWrite_def)
apply (case_tac "index div blockSize < numBlocks", simp_all)
apply (simp add: cfWriteNoExtend_def cfExtendFile_def Let_def)
apply force
done

lemma fileSizeIncreases:
  "cfWrite cfile1 index value = Some cfile2
   ==> fileSize cfile1 <= fileSize cfile2"
apply (simp add: cfWrite_def)
apply (case_tac "index div blockSize < numBlocks", simp_all)
apply (case_tac "index < fileSize cfile1", simp_all)
apply (simp_all add: cfWriteNoExtend_def cfExtendFile_def Let_def)
apply force
apply force
done

lemma nextFreeBlockIncreases:
  "[| nextFreeBlockInvariant cfile1;
      cfWrite cfile1 index value = Some cfile2
   |] ==> nextFreeBlock cfile1 <= nextFreeBlock cfile2"
apply (simp add: cfWrite_def)
apply (case_tac "index div blockSize < numBlocks", simp_all)
apply (case_tac "index < fileSize cfile1", simp_all)
apply (simp_all add: cfWriteNoExtend_def cfExtendFile_def Let_def)
apply force
apply (simp add: nextFreeBlockInvariant_def)
apply auto
apply hypsubst_thin
apply (subgoal_tac "nextFreeBlock cfile1 = 
  (fileSize cfile1 + blockSize - Suc 0) div blockSize", simp_all)
apply (subgoal_tac "Suc (index div blockSize) = 
  (index + blockSize) div blockSize", simp)
apply (subgoal_tac "(fileSize cfile1 + blockSize - Suc 0) <= 
  (index + blockSize)", simp add: div_le_mono)
apply (subgoal_tac "(fileSize cfile1 + blockSize - Suc 0) < 
  (fileSize cfile1 + blockSize)", simp)
apply (simp_all add: nonZeroBlockSize)
done


(* ---------------------------------------------------------------*)
subsection \<open>Concrete File Operations Preserve Invariants\<close>

text \<open>There is only one top-level concrete operation: write, and we
show that it preserves all reachability invariants.\<close>

lemma cfWritePreservesNextFreeBlockInvariant:
   "[| reachabilityInvariant cfile1;
       cfWrite cfile1 byteIndex value = Some cfile2
    |] ==> nextFreeBlockInvariant cfile2"
apply (simp add: reachabilityInvariant_def
                 cfWrite_def
                 nextFreeBlockInvariant_def)
apply (case_tac "byteIndex div blockSize < numBlocks", simp_all)
apply (case_tac "byteIndex < fileSize cfile1", simp_all)
apply (simp_all add: cfWriteNoExtend_def cfExtendFile_def Let_def)
apply auto
apply (simp add: nonZeroBlockSize)
done

lemma modInequalityLemma:
  "(a::nat) ~= b & a mod c = b mod c ==> a div c ~= b div c"
apply auto
apply (insert div_mult_mod_eq [of "a" "c"])
apply (insert div_mult_mod_eq [of "b" "c"])
apply simp
done

lemma mod_round_lt:
  "[| 0 < (c::nat);
      a < b
   |] ==> a div c < (b + c - 1) div c"
apply (subgoal_tac "a <= b - 1")
apply (subgoal_tac "a div c <= (b - 1) div c")
apply (insert div_add_self2 [of c "b - 1"])
apply (simp)
apply (simp add: div_le_mono)
apply (insert less_Suc_eq_le [of a "b - 1"])
apply simp
done

lemma blockNumNELemma:
  "!!blockNum i.
       [| nextFreeBlockInvariant cfile1;
          cfile1
          (| data :=
               writeCArray (data cfile1) (byteIndex div blockSize)
                (writeCArray
                  (readCArray (data cfile1) (byteIndex div blockSize))
                  (byteIndex mod blockSize) value) |) =
          cfile2;
          ~ blockNum < nextFreeBlock cfile2; blockNum < numBlocks;
          i < blockSize; byteIndex div blockSize < numBlocks;
          byteIndex < fileSize cfile1 |]
       ==> blockNum ~= byteIndex div blockSize"
apply (simp add: nextFreeBlockInvariant_def)
apply (subgoal_tac "byteIndex div blockSize < nextFreeBlock cfile1")
apply force
apply (subgoal_tac "nextFreeBlock cfile1 = 
  (fileSize cfile1 + blockSize - Suc 0) div blockSize", simp_all)
apply (insert mod_round_lt)
apply force
done

lemma cfWritePreservesUnallocatedBlocksInvariant:
   "[| reachabilityInvariant cfile1;
       cfWrite cfile1 byteIndex value = Some cfile2
    |] ==> unallocatedBlocksInvariant cfile2"
apply (simp add: reachabilityInvariant_def)
apply (subgoal_tac "nextFreeBlock cfile1 <= nextFreeBlock cfile2")
apply (simp add: unallocatedBlocksInvariant_def cfWrite_def)
apply auto
apply (case_tac "byteIndex div blockSize < numBlocks", simp_all)
apply (case_tac "byteIndex < fileSize cfile1", simp_all)
apply (simp_all add: cfWriteNoExtend_def cfExtendFile_def Let_def)
apply (simp_all add: writeCArray_def readCArray_def)
apply (subgoal_tac "blockNum ~= byteIndex div blockSize")
apply force
apply (simp add: blockNumNELemma)
apply (subgoal_tac "~ blockNum < nextFreeBlock cfile1")
apply (subgoal_tac "blockNum ~= byteIndex div blockSize")
apply auto
apply (simp add: nextFreeBlockIncreases)
done

lemma cfWritePreservesLastBlockInvariant:
   "[| reachabilityInvariant cfile1;
       cfWrite cfile1 byteIndex value = Some cfile2 |] ==> 
    lastBlockInvariant cfile2"
apply (simp add: reachabilityInvariant_def)
apply (subgoal_tac "nextFreeBlock cfile1 <= nextFreeBlock cfile2")
apply (simp add: cfWrite_def)
apply (simp (no_asm) add: lastBlockInvariant_def)
apply auto
apply (case_tac "byteIndex div blockSize < numBlocks", simp_all)
apply (case_tac "byteIndex < fileSize cfile1", simp_all)
apply (simp_all add: cfWriteNoExtend_def Let_def cfExtendFile_def)
apply (simp_all add: writeCArray_def readCArray_def)
apply (simp add: lastBlockInvariant_def)
apply (subgoal_tac "index ~= byteIndex")
apply (case_tac "index div blockSize ~= byteIndex div blockSize")
apply force
apply (subgoal_tac "index mod blockSize ~= byteIndex mod blockSize")
apply force
apply (insert modInequalityLemma)
apply force
apply force
apply (subgoal_tac "index ~= byteIndex")
apply (case_tac "index div blockSize ~= byteIndex div blockSize", simp_all)
apply force
apply (subgoal_tac "index mod blockSize ~= byteIndex mod blockSize")
apply (case_tac "nextFreeBlock cfile1 = Suc (index div blockSize)")
apply (subgoal_tac "~ index < fileSize cfile1")
apply (simp add: lastBlockInvariant_def)
apply auto
apply (simp add: unallocatedBlocksInvariant_def)
apply (erule_tac x="index div blockSize" in allE)
apply (erule_tac x="index mod blockSize" in allE)
apply (simp add: nonZeroBlockSize)
apply (insert modInequalityLemma)
apply auto
apply (simp add: nextFreeBlockIncreases)
done

text \<open>Final statement that all invariants are preserved.\<close>
lemma cfWritePreserves: 
   "[| reachabilityInvariant cfile1;
       cfWrite cfile1 byteIndex value = Some cfile2 |] ==> 
    reachabilityInvariant cfile2"
apply (simp (no_asm) add: reachabilityInvariant_def)
apply (simp add: cfWritePreservesNextFreeBlockInvariant)
apply (simp add: cfWritePreservesUnallocatedBlocksInvariant)
apply (simp add: cfWritePreservesLastBlockInvariant)
done

(* ---------------------------------------------------------------*)
subsection \<open>Commuting Diagrams for Simulation Relation\<close>

text \<open>Here we show correctness of file system operations.\<close>

(* ---------------------------------------------------------------*)
subsubsection \<open>Abstraction Function\<close>

definition abstFn :: "CFile => AFile" where
  "abstFn cfile == (fileSize cfile, 
                    % index . case cfRead cfile index of
                                None       => fillByte
                              | Some value => value)"

primrec oAbstFn :: "CFile option => AFile option" where
  "oAbstFn None = None"
| "oAbstFn (Some s) = Some (abstFn s)"

(* ---------------------------------------------------------------*)
subsubsection \<open>Creating a File\<close>

lemma makeCFCorrect: "abstFn makeCF = makeAF"
by (simp add: makeCF_def makeAF_def abstFn_def cfRead_def
    split: bool.splits option.splits)

subsubsection \<open>File Size\<close>

lemma fileSizeCorrect:
  "cfSize cfile = afSize (abstFn cfile)"
by (simp add: cfSize_def afSize_def abstFn_def)

subsubsection \<open>Read Operation\<close>

lemma readCorrect:
  "cfRead cfile = afRead (abstFn cfile)"
apply (simp add: abstFn_def)
apply (rule ext)
apply (simp add: cfRead_def afRead_def Let_def)
done

subsubsection \<open>Write Operation\<close>

lemma writeNoExtendCorrect:
  "[| index < fileSize cfile1;
      Some cfile2 = cfWrite cfile1 index value
   |] ==> Some (abstFn cfile2) = afWrite (abstFn cfile1) index value"
apply (simp add: abstFn_def afWrite_def raWrite_def Let_def cfWrite_def)
apply (case_tac "index div blockSize < numBlocks", simp_all)
apply (simp_all add: cfWriteNoExtend_def Let_def)
apply (rule ext)
apply (simp add: cfRead_def writeCArray_def readCArray_def Let_def)
apply (case_tac "indexa < fileSize cfile1", simp_all)
apply (case_tac "indexa = index", simp_all)
apply (case_tac "indexa mod blockSize = index mod blockSize", simp_all)
apply (subgoal_tac "indexa div blockSize ~= index div blockSize", simp_all)
apply (simp_all add: modInequalityLemma)
done

lemma writeExtendCorrect:
  "[| nextFreeBlockInvariant cfile1;
      unallocatedBlocksInvariant cfile1;
      lastBlockInvariant cfile1;
      ~ index < fileSize cfile1;
      Some cfile2 = cfWrite cfile1 index value
   |] ==> Some (abstFn cfile2) = afWrite (abstFn cfile1) index value"
apply (insert nextFreeBlockIncreases [of cfile1 index "value" cfile2])
apply (simp add: abstFn_def afWrite_def raWrite_def Let_def)
apply (case_tac "~ index div blockSize < numBlocks",
  simp_all add: cfWrite_def cfWriteNoExtend_def cfExtendFile_def Let_def)
apply (rule ext)
apply (simp add: cfRead_def fillAndUpdate_def Let_def writeCArrayCorrect1)
apply (case_tac "indexa < fileSize cfile1", simp_all) (* 2 subgoals *)
apply (subgoal_tac "indexa ~= index", simp_all)
apply (case_tac "indexa div blockSize = index div blockSize") (* 3 subgoals *)
apply (case_tac "indexa mod blockSize = index mod blockSize",
  simp add: modInequalityLemma) (* 3 subgoals *)
apply (simp_all add: writeCArrayCorrect1 writeCArrayCorrect2) (* 1 subgoal *)
apply (case_tac "indexa < index", simp_all)
apply (case_tac "indexa div blockSize = index div blockSize") (* 2 subgoals *)
apply (case_tac "indexa mod blockSize = index mod blockSize",
  simp add: modInequalityLemma)
apply (simp_all add: readCArray_def writeCArray_def lastBlockInvariant_def)
apply (erule_tac x=indexa in allE, simp_all)
apply (case_tac "nextFreeBlock cfile1 = nextFreeBlock cfile2", simp_all)
apply (simp add: unallocatedBlocksInvariant_def)
apply (subgoal_tac "~ indexa div blockSize < nextFreeBlock cfile1", simp_all)
apply (subgoal_tac "indexa mod blockSize < blockSize", simp_all)
apply (insert nonZeroBlockSize)
apply force (* 1 subgoal *)
apply (simp add: unallocatedBlocksInvariant_def)
apply (case_tac "~ indexa div blockSize < nextFreeBlock cfile1", simp_all)
apply (subgoal_tac "indexa div blockSize < numBlocks", simp_all) 
  (* 2 subgoals *)
apply (subgoal_tac "indexa div blockSize <= index div blockSize", simp_all)
apply (simp add: div_le_mono) (* 1 subgoal *)
apply (subgoal_tac "nextFreeBlock cfile1 = Suc (indexa div blockSize)", simp)
apply (simp add: nextFreeBlockInvariant_def)
apply (subgoal_tac "nextFreeBlock cfile1 = 
  (fileSize cfile1 + blockSize - Suc 0) div blockSize", simp_all)
apply (subgoal_tac "(fileSize cfile1 + blockSize - Suc 0) div blockSize <=
  Suc (indexa div blockSize)", simp_all)
apply (subgoal_tac "Suc (indexa div blockSize) = 
  (indexa + blockSize) div blockSize")
apply (simp only:)
apply (rule div_le_mono)
apply (simp_all add: le_diff_conv)
done

lemma writeSucceedCorrect:
  "[| nextFreeBlockInvariant cfile1;
      unallocatedBlocksInvariant cfile1;
      lastBlockInvariant cfile1;
      Some cfile2 = cfWrite cfile1 index value
   |] ==> Some (abstFn cfile2) = afWrite (abstFn cfile1) index value"
apply (case_tac "index < fileSize cfile1")
apply (simp_all add: writeExtendCorrect writeNoExtendCorrect)
done

lemma writeFailCorrect:
  "cfWrite cfile1 index value = None ==> 
   afWrite (abstFn cfile1) index value = None"
apply (simp add: abstFn_def cfWrite_def afWrite_def)
apply (case_tac "index div blockSize < numBlocks", simp_all)
apply (case_tac "index < fileSize cfile1", simp_all)
done

lemma writeCorrect:
  "reachabilityInvariant cfile1 ==>
   oAbstFn (cfWrite cfile1 index value) = afWrite (abstFn cfile1) index value"
apply (simp add: reachabilityInvariant_def)
apply (case_tac "cfWrite cfile1 index value")
apply (simp add: writeFailCorrect)
apply (simp add: writeSucceedCorrect)
done

end
