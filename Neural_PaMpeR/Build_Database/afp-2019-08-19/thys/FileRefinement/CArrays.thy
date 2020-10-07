section "Arrays without bounds"
theory CArrays imports Main begin

text \<open>For these arrays there is no
        built-in protection against reading or writing out-of-bounds.\<close>

type_synonym 'a cArray = "nat => 'a"

definition makeCArray :: "nat => 'a => 'a cArray" where
  "makeCArray arraySize fillValue index == 
   if index < arraySize then fillValue else undefined"

definition readCArray :: "'a cArray => nat => 'a" where
  "readCArray array index == array index"

definition writeCArray :: "'a cArray => nat => 'a => 'a cArray" where
  "writeCArray array index value == array(index := value)"

(* ---------------------------------------------------------------*)

lemma makeCArrayCorrect:
  "index < arraySize ==>
   readCArray (makeCArray arraySize fillValue) index = fillValue"
by (simp add: readCArray_def makeCArray_def)

lemma writeCArrayCorrect1:
  "readCArray (writeCArray array index value) index = value"
by (simp add: readCArray_def writeCArray_def)

lemma writeCArrayCorrect2:
  "index1 ~= index2 ==>
   readCArray (writeCArray array index1 value) index2 = 
   readCArray array index2"
by (simp add: readCArray_def writeCArray_def)

end
