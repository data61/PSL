(*  Title:       An example submission to the Archive of Formal Proofs
    Author:      Gerwin Klein <kleing at cse.unsw.edu.au>, 2004
    Maintainer:  Gerwin Klein <kleing at cse.unsw.edu.au>
*)

section "An Example Submission"

theory Submission 
  imports Main 
begin

text \<open>
  This is an example submission to the Archive of Formal Proofs.

  The scope of the archive encompasses examples, textbook-style
  proofs, libraries and larger scientific developments.
\<close>

section "Format of a submission"

text \<open>
  Submission should be via the web page @{url "https://ci.isabelle.systems/afp-submission/"}.

  The tar file submission of the example you are reading is at
  @{url "http://isa-afp.org/release/afp-Example-Submission-current.tar.gz"}.
\<close>

section "Proof styles"

text \<open>
  We accept proofs in \isakeyword{apply}-script style like the
  following.
\<close>

lemma true: "True" 
  apply blast
  done

text \<open>
  We encourage structured proofs with comments and
  explanations. The Isabelle document preparation tools support
  antiquotations like @{thm true}, normal {\LaTeX} commands and BibTeX
  citations. See \cite{LNCS2283} and the Isabelle documentation for
  more information.  
\<close>
lemma very_true: "True"
proof -
  \<comment> \<open>a very roundabout way\<close>
  fix P have "P \<longrightarrow> True" by blast
  \<comment> \<open>to show @{term True}\<close>
  thus True by blast
qed

section "The anatomy of a submission"

text \<open>
  The directory structure of this example submission is the following  
\begin{verbatim}
Example-Submission/
    document/
        root.tex
        root.bib
    ROOT
    Submission.thy
\end{verbatim}

The document directory contains the {\LaTeX} master file
\texttt{root.tex} and the bibliography \texttt{root.bib}. 
The {\LaTeX} part of your
submission should contain title, abstract, author, and any
further documentation
you wish to provide. 

\texttt{ROOT} controls which theories should be loaded. If you have
one main theory that depends on all the others, you only need to
include this one. You can also use the \texttt{ROOT} file to control the
order in which theories are read. 

The file \texttt{Submission.thy} is the Isabelle theory containing
this text. A usual submission has more than one theory file. You can
devise your own subdirectory structure if you have more theories and
one directory becomes too crowded. You can also build on existing articles
in the AFP by importing them. For example, if you build on theory W in 
the article MiniML, the way to import it is:

\begin{verbatim}
theory My_Theory
  imports MiniML.W
begin
\end{verbatim}
\<close>

end

