(*  Title:       Jive Data and Store Model
    Author:      Norbert Schirmer <schirmer at informatik.tu-muenchen.de>, 2003
    Maintainer:  Nicole Rauch <rauch at informatik.uni-kl.de>
    License:     LGPL
*)

section \<open>Location\<close>

theory Location
imports AttributesIndep "../Isabelle/Value"
begin 

text \<open>A storage location can be a field of an object, a static field,
 the length of an array, or the contents of an array.  
\<close>

datatype Location = objLoc    CAttId ObjectId     \<comment> \<open>field in object\<close> 
                  | staticLoc AttId               \<comment> \<open>static field in concrete class\<close>
                  | arrLenLoc Arraytype ObjectId   \<comment> \<open>length of an array\<close>
                  | arrLoc    Arraytype ObjectId nat \<comment> \<open>contents of an array\<close>

text \<open>We only directly support one-dimensional arrays. Multidimensional
arrays can be simulated by arrays of references to arrays.
\<close>

text \<open>The function \<open>ltype\<close> yields the content type of a location.\<close>
definition ltype:: "Location \<Rightarrow> Javatype" where
"ltype l = (case l of
              objLoc cf a  \<Rightarrow> rtype (att cf)
            | staticLoc f     \<Rightarrow> rtype f
            | arrLenLoc T a   \<Rightarrow> IntgT
            | arrLoc T a i \<Rightarrow> at2jt T)" 

lemma ltype_simps [simp]:
"ltype (objLoc cf a)  = rtype (att cf)"
"ltype (staticLoc f)     = rtype f"
"ltype (arrLenLoc T a)   = IntgT"
"ltype (arrLoc T a i) = at2jt T" 
  by (simp_all add: ltype_def)

text \<open>Discriminator functions to test whether a location denotes an array length
or whether it denotes a static object. Currently, the discriminator functions for
object and array locations are not specified. They can be added if they are needed.
\<close>

definition isArrLenLoc:: "Location \<Rightarrow> bool" where
"isArrLenLoc l = (case l of
                 objLoc cf a  \<Rightarrow> False 
               | staticLoc f     \<Rightarrow> False
               | arrLenLoc T a   \<Rightarrow> True
               | arrLoc T a i \<Rightarrow> False)"

lemma isArrLenLoc_simps [simp]:
"isArrLenLoc (objLoc cf a) = False" 
"isArrLenLoc (staticLoc f) = False"
"isArrLenLoc (arrLenLoc T a) = True"
"isArrLenLoc (arrLoc T a i) = False"
  by (simp_all add: isArrLenLoc_def)

definition isStaticLoc:: "Location \<Rightarrow> bool" where
"isStaticLoc l = (case l of
                 objLoc cff a \<Rightarrow> False
               | staticLoc f     \<Rightarrow> True
               | arrLenLoc T a   \<Rightarrow> False
               | arrLoc T a i \<Rightarrow> False)"
lemma isStaticLoc_simps [simp]:
"isStaticLoc (objLoc cf a) = False"
"isStaticLoc (staticLoc f)     = True"
"isStaticLoc (arrLenLoc T a)   = False"
"isStaticLoc (arrLoc T a i) = False"
  by (simp_all add: isStaticLoc_def)

text \<open>The function \<open>ref\<close> yields the
object or array containing the location that is passed
as argument (see the function \<open>obj\<close> in 
\cite[p. 43 f.]{Poetzsch-Heffter97specification}).
Note that for static locations
the result is \<open>nullV\<close> since static locations 
are not associated to any object.
\label{ref_def}
\<close>
definition ref:: "Location \<Rightarrow> Value" where
"ref l = (case l of
            objLoc cf a  \<Rightarrow> objV (cls cf) a
          | staticLoc f     \<Rightarrow> nullV
          | arrLenLoc T a   \<Rightarrow> arrV T a
          | arrLoc T a i \<Rightarrow> arrV T a)"

lemma ref_simps [simp]:
"ref (objLoc cf a)  = objV (cls cf) a"
"ref (staticLoc f)     = nullV"
"ref (arrLenLoc T a)   = arrV T a"
"ref (arrLoc T a i) = arrV T a"
  by (simp_all add: ref_def)

text \<open>The function \<open>loc\<close> denotes the subscription of an object 
reference with an attribute.\<close>
primrec loc:: "Value \<Rightarrow> AttId \<Rightarrow> Location"  ("_.._" [80,80] 80)
where "loc (objV c a) f = objLoc (catt c f) a"
text \<open>Note that we only define subscription properly for object references.
For all other values we do not provide any defining equation, so they will 
internally be mapped to \<open>arbitrary\<close>.
\<close>

text \<open>The length of an array can be selected with the function \<open>arr_len\<close>.\<close>
primrec arr_len:: "Value \<Rightarrow> Location"
where "arr_len (arrV T a) = arrLenLoc T a"

text \<open>Arrays can be indexed by the function \<open>arr_loc\<close>.\<close>
primrec arr_loc:: "Value \<Rightarrow> nat \<Rightarrow> Location" ("_.[_]" [80,80] 80)
where "arr_loc (arrV T a) i = arrLoc T a i" 

text \<open>The functions @{term "loc"}, @{term "arr_len"} and @{term "arr_loc"}
define the interface between the basic store model (based on locations) and
the programming language Java. Instance field access {\tt obj.x} is modelled as 
@{term "obj..x"} or \<open>loc obj x\<close> (without the syntactic sugar), 
array length {\tt a.length} with @{term "arr_len a"},
array indexing {\tt a[i]} with @{term "a.[i]"} or \<open>arr_loc a i\<close>. 
The accessing of a static field 
{\tt C.f} can be expressed by the location itself \<open>staticLoc C'f\<close>.
Of course one can build more infrastructure to make access to instance fields
and static fields more uniform. We could for example define a 
function \<open>static\<close> which indicates whether a field is static or not and
based on that create an @{term "objLoc"} location or a @{term "staticLoc"} location. But 
this will only complicate the actual proofs and we can already easily 
perform the distinction whether a field is static or not in the \jive-frontend and 
therefore keep the verification simpler.
\<close> 

lemma ref_loc [simp]: "\<lbrakk>isObjV r; typeof r \<le> dtype f\<rbrakk> \<Longrightarrow> ref (r..f) = r"
  apply (case_tac r)
  apply (case_tac [!] f)
  apply (simp_all)
  done

lemma obj_arr_loc [simp]: "isArrV r \<Longrightarrow> ref (r.[i]) = r"
  by (cases r) simp_all

lemma obj_arr_len [simp]: "isArrV r \<Longrightarrow> ref (arr_len r) = r"
  by (cases r) simp_all

end
