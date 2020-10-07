section\<open>End Results in Locale-Free Form\<close>
theory Encodings
imports G T E
begin

text\<open>This section contains the outcome of our type-encoding results,
presented in a locale-free fashion. It is not very useful
from an Isabelle development point of view, where the locale theorems are fine.

Rather, this is aimed as a quasi-self-contained formal documentation of
the overall results for the non-Isabelle-experts.\<close>


subsection \<open>Soundness\<close>

text\<open>In the soundness theorems below, we employ the following Isabelle types:
\\- type variables (parameters):
\\--- \<open>'tp\<close>, of types
\\--- \<open>'fsym\<close>, of function symbols
\\--- \<open>'psym\<close>, of predicate symbols
%
\\- a fixed countable universe \<open>univ\<close> for the carrier of the models
%
\\
and various operators on these types:

(1) the constitutive parts of FOL signatures:
\\---- the boolean predicates
\<open>wtFsym\<close> and \<open>wtPsym\<close>, indicating the ``well-typed'' function and predicate
symbols; these are just means to select only subsets of these symbols
for consideration in the signature
\\---- the operators arOf and resOf, giving the arity and the result type
of function symbols
\\---- the operator parOf, giving the arity of predicate symbols

(2) the problem, \<open>\<Phi>\<close>, which is a set of clauses over the considered signature

(3) a partition of the types in:
\\--- \<open>tpD\<close>, the types that should be decorated in any case
\\--- \<open>tpFD\<close>, the types that should be decorated in a featherweight fashion
\\--- for guards only, a further refinement of \<open>tpD\<close>, indicating, as \<open>tpCD\<close>,
the types that should be classically (i.e., traditionally) decorated
(these partitionings are meant to provide a uniform treatment of the
three styles of encodings:
traditional, lightweight and featherweight)

(4) the constitutive parts of a structure over the considered signature:
\\---- \<open>intT\<close>, the interpretation of each type as a unary predicate (essentially, a set)
over an arbitrary type 'univ
\\---- \<open>intF\<close> and \<open>intP\<close>, the interpretations of the function and predicate symbols
as actual functions and predicates over \<open>univ\<close>.


\<close>


text\<open>\ \\ \bf Soundness of the tag encodings: \ \\\<close>

text\<open>The assumptions of the tag soundness theorems are the following:

(a)  \<open>ProblemIkTpart wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD\<close>,
stating that:
\\--- \<open>(wtFsym, wtPsym, arOf, resOf, parOf)\<close> form a countable signature
\\--- \<open>\<Phi>\<close> is a well-typed problem over this signature
\\--- \<open>infTp\<close> is an indication of the types that the problem guarantees as infinite
in all models
\\--- \<open>tpD\<close> and \<open>tpFD\<close> are disjoint and all types that are not
 marked as \<open>tpD\<close> or \<open>tpFD\<close>
are deemed safe by the monotonicity calculus from \<open>Mcalc\<close>

(b) \<open>CM.Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP\<close>
says that \<open>(intT, intF, intP)\<close> is a model for \<open>\<Phi>\<close> (hence \<open>\<Phi>\<close> is satisfiable)

The conclusion says that we obtain a model of the untyped version of the problem
(after suitable tags and axioms have been added):\<close>


text\<open>Because of the assumptions on tpD and tpFD, we have the following particular cases
of our parameterized tag encoding:
\\-- if \<open>tpD\<close> is taked to be everywhere true (hence \<open>tpFD\<close> becomes everywhere false), we
obtain the traditional tag encoding
\\-- if \<open>tpD\<close> is taken to be true precisely when the monotonicity calculus fails,
we obtain the lightweight tag encoding
\\-- if \<open>tpFD\<close> is taken to be true precisely when the monotonicity calculus fails,
we obtain the featherweight tag encoding
\<close>

theorem tags_soundness:
fixes wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list" and resOf :: "'fsym \<Rightarrow> 'tp" and parOf :: "'psym \<Rightarrow> 'tp list"
and \<Phi> :: "('fsym, 'psym) prob" and infTp :: "'tp \<Rightarrow> bool"
and tpD :: "'tp \<Rightarrow> bool" and tpFD :: "'tp \<Rightarrow> bool"
and intT :: "'tp \<Rightarrow> univ \<Rightarrow> bool"
and intF :: "'fsym \<Rightarrow> univ list \<Rightarrow> univ" and intP :: "'psym \<Rightarrow> univ list \<Rightarrow> bool"
\<comment> \<open>The problem translation:\<close>
\<comment> \<open>First the addition of tags (``TE'' stands for ``tag encoding''):\<close>
defines "TE_wtFsym \<equiv> ProblemIkTpart.TE_wtFsym wtFsym resOf"
and "TE_arOf \<equiv> ProblemIkTpart.TE_arOf arOf"
and "TE_resOf \<equiv> ProblemIkTpart.TE_resOf resOf"
defines "TE_\<Phi> \<equiv> ProblemIkTpart.tPB wtFsym arOf resOf \<Phi> tpD tpFD"
\<comment> \<open>Then the deletion of types (``U'' stands for ``untyped''):\<close>
and "U_arOf \<equiv> length \<circ> TE_arOf"
and "U_parOf \<equiv> length \<circ> parOf"
defines "U_\<Phi> \<equiv> TE_\<Phi>"
\<comment> \<open>The forward model translation:\<close>
\<comment> \<open>First, using monotonicity, we build an infinite model of @{text"\<Phi>"}
  (``I'' stands for ``infinite''):\<close>
defines "intTI \<equiv> MonotProblem.intTI TE_wtFsym wtPsym TE_arOf TE_resOf parOf TE_\<Phi>"
and "intFI \<equiv> MonotProblem.intFI TE_wtFsym wtPsym TE_arOf TE_resOf parOf TE_\<Phi>"
and "intPI \<equiv> MonotProblem.intPI TE_wtFsym wtPsym TE_arOf TE_resOf parOf TE_\<Phi>"
\<comment> \<open>Then, by isomorphic transfer of the lattter model, we build a model of @{text"\<Phi>"}
 that has all types interpeted as @{text "univ"} (``F'' stands for ``full"):\<close>
defines "intFF \<equiv> InfModel.intFF TE_arOf TE_resOf intTI intFI"
and "intPF \<equiv> InfModel.intPF parOf intTI intPI"
\<comment> \<open>Then we build a model of @{text "U_\<Phi>"}:\<close>
defines "U_intT \<equiv> InfModel.intTF (any::'tp)"

\<comment> \<open>Assumptions of the theorem:\<close>
assumes
P: "ProblemIkTpart wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD"
and M: "CM.Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP"

\<comment> \<open>Conclusion of the theorem:\<close>
shows "CU.Model TE_wtFsym wtPsym U_arOf U_parOf U_\<Phi> U_intT intFF intPF"

unfolding U_arOf_def U_parOf_def U_\<Phi>_def
unfolding U_intT_def intTI_def intFI_def intPI_def intFF_def intPF_def
apply(rule M_MonotModel.M_U_soundness)
unfolding M_MonotModel_def MonotModel_def apply safe
  unfolding TE_wtFsym_def TE_arOf_def TE_resOf_def TE_\<Phi>_def
  apply(rule ProblemIkTpart.T_monotonic)
   apply(rule P)
   apply(rule ModelIkTpart.T_soundness) unfolding ModelIkTpart_def apply safe
     apply(rule P)
     apply(rule M)
done


text\<open>\ \\ \bf Soundness of the guard encodings: \ \\\<close>

text\<open>Here the assumptions and conclusion have a similar shapes as those
for the tag encodings. The difference is in the first assumption,
\<open>ProblemIkTpartG wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD tpCD\<close>,
which consists of \<open>ProblemIkTpart wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD\<close> together
with the following assumptions about \<open>tpCD\<close>:
\\-- \<open>tpCD\<close> is included in \<open>tpD\<close>
\\-- if a result type of an operation symbol is in \<open>tpD\<close>, then so are all the types in its arity
\<close>

text\<open>We have the following particular cases of our parameterized guard encoding:
\\-- if \<open>tpD\<close> and \<open>tpCD\<close> are taked to be everywhere true
(hence \<open>tpFD\<close> becomes everywhere false),
we obtain the traditional guard encoding
\\-- if \<open>tpCD\<close> is taken to be false and \<open>tpD\<close> is taken to be true precisely when the
monotonicity calculus fails,
we obtain the lightweight tag encoding
\\-- if \<open>tpFD\<close> is taken to be true precisely when the monotonicity calculus fails,
we obtain the featherweight tag encoding
\<close>

theorem guards_soundness:
fixes wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list" and resOf :: "'fsym \<Rightarrow> 'tp" and parOf :: "'psym \<Rightarrow> 'tp list"
and \<Phi> :: "('fsym, 'psym) prob" and infTp :: "'tp \<Rightarrow> bool"
and tpD :: "'tp \<Rightarrow> bool" and tpFD :: "'tp \<Rightarrow> bool" and tpCD :: "'tp \<Rightarrow> bool"
and intT :: "'tp \<Rightarrow> univ \<Rightarrow> bool"
and intF :: "'fsym \<Rightarrow> univ list \<Rightarrow> univ"
and intP :: "'psym \<Rightarrow> univ list \<Rightarrow> bool"
\<comment> \<open>The problem translation:\<close>
defines "GE_wtFsym \<equiv> ProblemIkTpartG.GE_wtFsym wtFsym resOf tpCD"
and "GE_wtPsym \<equiv> ProblemIkTpartG.GE_wtPsym wtPsym tpD tpFD"
and "GE_arOf \<equiv> ProblemIkTpartG.GE_arOf arOf"
and "GE_resOf \<equiv> ProblemIkTpartG.GE_resOf resOf"
and "GE_parOf \<equiv> ProblemIkTpartG.GE_parOf parOf"

defines "GE_\<Phi> \<equiv> ProblemIkTpartG.gPB wtFsym arOf resOf \<Phi> tpD tpFD tpCD"
and "U_arOf \<equiv> length \<circ> GE_arOf"
and "U_parOf \<equiv> length \<circ> GE_parOf"

defines "U_\<Phi> \<equiv> GE_\<Phi>"

\<comment> \<open>The model forward translation:\<close>
defines "intTI \<equiv> MonotProblem.intTI GE_wtFsym GE_wtPsym GE_arOf GE_resOf GE_parOf GE_\<Phi>"
and "intFI \<equiv> MonotProblem.intFI GE_wtFsym GE_wtPsym GE_arOf GE_resOf GE_parOf GE_\<Phi>"
and "intPI \<equiv> MonotProblem.intPI GE_wtFsym GE_wtPsym GE_arOf GE_resOf GE_parOf GE_\<Phi>"

defines "intFF \<equiv> InfModel.intFF GE_arOf GE_resOf intTI intFI"
and "intPF \<equiv> InfModel.intPF GE_parOf intTI intPI"

defines "U_intT \<equiv> InfModel.intTF (any::'tp)"

assumes
P: "ProblemIkTpartG wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD tpCD"
and M: "CM.Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP"

shows "CU.Model GE_wtFsym GE_wtPsym U_arOf U_parOf U_\<Phi> U_intT intFF intPF"

unfolding U_arOf_def U_parOf_def U_\<Phi>_def
unfolding U_intT_def intTI_def intFI_def intPI_def intFF_def intPF_def
apply(rule M_MonotModel.M_U_soundness)
unfolding M_MonotModel_def MonotModel_def apply safe
  unfolding GE_wtFsym_def GE_wtPsym_def GE_arOf_def GE_resOf_def GE_parOf_def GE_\<Phi>_def
  apply(rule ProblemIkTpartG.G_monotonic)
   apply(rule P)
   apply(rule ModelIkTpartG.G_soundness)
   unfolding ModelIkTpartG_def ModelIkTpart_def apply safe
     apply(rule P)
     using P unfolding ProblemIkTpartG_def apply fastforce
     apply(rule M)
done


subsection \<open>Completeness\<close>

text\<open>The setting is similar to the one for completeness, except for the following point:

(3) The constitutive parts of a structure over the untyped signature
resulted from the addition of the tags or guards followed by
the deletion of the types: \<open>(D, eintF, eintP)\<close>
\<close>


text\<open>\ \\ \bf Completeness of the tag encodings \ \\\<close>


theorem tags_completeness:
fixes wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list" and resOf :: "'fsym \<Rightarrow> 'tp" and parOf :: "'psym \<Rightarrow> 'tp list"
and \<Phi> :: "('fsym, 'psym) prob" and infTp :: "'tp \<Rightarrow> bool"
and tpD :: "'tp \<Rightarrow> bool" and tpFD :: "'tp \<Rightarrow> bool"

and D :: "univ \<Rightarrow> bool"
and eintF :: "('fsym,'tp) T.efsym \<Rightarrow> univ list \<Rightarrow> univ"
and eintP :: "'psym \<Rightarrow> univ list \<Rightarrow> bool"

\<comment> \<open>The problem translation (the same as in the case of soundness):\<close>
defines "TE_wtFsym \<equiv> ProblemIkTpart.TE_wtFsym wtFsym resOf"
and "TE_arOf \<equiv> ProblemIkTpart.TE_arOf arOf"
and "TE_resOf \<equiv> ProblemIkTpart.TE_resOf resOf"
defines "TE_\<Phi> \<equiv> ProblemIkTpart.tPB wtFsym arOf resOf \<Phi> tpD tpFD"
and "U_arOf \<equiv> length \<circ> TE_arOf"
and "U_parOf \<equiv> length \<circ> parOf"
defines "U_\<Phi> \<equiv> TE_\<Phi>"

\<comment> \<open>The backward model translation:\<close>
defines "intT \<equiv> ProblemIkTpart_TEModel.intT tpD tpFD (\<lambda>\<sigma>::'tp. D) eintF"
and "intF \<equiv> ProblemIkTpart_TEModel.intF arOf resOf tpD tpFD (\<lambda>\<sigma>::'tp. D) eintF"
and "intP \<equiv> ProblemIkTpart_TEModel.intP parOf tpD tpFD (\<lambda>\<sigma>::'tp. D) eintF eintP"

assumes
P: "ProblemIkTpart wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD" and
M: "CU.Model TE_wtFsym wtPsym (length o TE_arOf)
            (length o parOf) TE_\<Phi> D eintF eintP"

shows "CM.Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP"
proof-
  have UM: "UM_Model TE_wtFsym wtPsym TE_arOf TE_resOf parOf TE_\<Phi> D eintF eintP"
  unfolding UM_Model_def UM_Struct_def
  using M unfolding CU.Model_def CU.Struct_def U.Model_def
  using ProblemIkTpart.T_monotonic[OF P,
  unfolded TE_wtFsym_def[symmetric] TE_arOf_def[symmetric]
           TE_resOf_def[symmetric] TE_\<Phi>_def[symmetric]]
  by (auto simp: MonotProblem_def M_Problem_def M_Signature_def M.Problem_def)
  show ?thesis
  unfolding intT_def intF_def intP_def
  apply(rule ProblemIkTpart_TEModel.T_completeness)
  unfolding ProblemIkTpart_TEModel_def apply safe
  apply(rule P)
  apply(rule UM_Model.M_U_completeness)
  apply(rule UM[unfolded TE_wtFsym_def TE_arOf_def TE_resOf_def TE_\<Phi>_def])
  done
qed

text\<open>\ \\ \bf Completeness of the guard encodings \ \\\<close>

theorem guards_completeness:
fixes wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list" and resOf :: "'fsym \<Rightarrow> 'tp" and parOf :: "'psym \<Rightarrow> 'tp list"
and \<Phi> :: "('fsym, 'psym) prob" and infTp :: "'tp \<Rightarrow> bool"
and tpD :: "'tp \<Rightarrow> bool" and tpFD :: "'tp \<Rightarrow> bool" and tpCD :: "'tp \<Rightarrow> bool"

and D :: "univ \<Rightarrow> bool"
and eintF :: "('fsym,'tp) G.efsym \<Rightarrow> univ list \<Rightarrow> univ"
and eintP :: "('psym,'tp) G.epsym \<Rightarrow> univ list \<Rightarrow> bool"

\<comment> \<open>The problem translation (the same as in the case of soundness):\<close>
defines "GE_wtFsym \<equiv> ProblemIkTpartG.GE_wtFsym wtFsym resOf tpCD"
and "GE_wtPsym \<equiv> ProblemIkTpartG.GE_wtPsym wtPsym tpD tpFD"
and "GE_arOf \<equiv> ProblemIkTpartG.GE_arOf arOf"
and "GE_resOf \<equiv> ProblemIkTpartG.GE_resOf resOf"
and "GE_parOf \<equiv> ProblemIkTpartG.GE_parOf parOf"
defines "GE_\<Phi> \<equiv> ProblemIkTpartG.gPB wtFsym arOf resOf \<Phi> tpD tpFD tpCD"
and "U_arOf \<equiv> length \<circ> GE_arOf"
and "U_parOf \<equiv> length \<circ> GE_parOf"
defines "U_\<Phi> \<equiv> GE_\<Phi>"

\<comment> \<open>The backward model translation:\<close>
defines "intT \<equiv> ProblemIkTpartG_GEModel.intT tpD tpFD (\<lambda>\<sigma>::'tp. D) eintP"
and "intF \<equiv> ProblemIkTpartG_GEModel.intF eintF"
and "intP \<equiv> ProblemIkTpartG_GEModel.intP eintP"

assumes
P: "ProblemIkTpartG wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD tpCD" and
M: "CU.Model GE_wtFsym GE_wtPsym (length o GE_arOf)
            (length o GE_parOf) GE_\<Phi> D eintF eintP"

shows "CM.Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP"
proof-
  have UM: "UM_Model GE_wtFsym GE_wtPsym GE_arOf GE_resOf GE_parOf GE_\<Phi> D eintF eintP"
  unfolding UM_Model_def UM_Struct_def
  using M unfolding CU.Model_def CU.Struct_def U.Model_def
  using ProblemIkTpartG.G_monotonic[OF P,
  unfolded GE_wtFsym_def[symmetric] GE_arOf_def[symmetric]
           GE_wtPsym_def[symmetric] GE_parOf_def[symmetric]
           GE_resOf_def[symmetric] GE_\<Phi>_def[symmetric]]
  by (auto simp: MonotProblem_def M_Problem_def M_Signature_def M.Problem_def)
  show ?thesis
  unfolding intT_def intF_def intP_def
  apply(rule ProblemIkTpartG_GEModel.G_completeness)
  unfolding ProblemIkTpartG_GEModel_def apply safe
  apply(rule P)
  apply(rule UM_Model.M_U_completeness)
  apply(rule UM[unfolded GE_wtFsym_def GE_wtPsym_def GE_parOf_def
             GE_arOf_def GE_resOf_def GE_\<Phi>_def])
  done
qed

end
