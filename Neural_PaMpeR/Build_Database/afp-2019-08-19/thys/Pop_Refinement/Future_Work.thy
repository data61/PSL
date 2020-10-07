chapter \<open>Future Work\<close>

theory %invisible Future_Work
imports Main
begin

text \<open>\label{chap:future}\<close>


section \<open>Populating the Framework\<close>
text \<open>\label{sec:populate}\<close>

text \<open>Pop-refinement provides a framework,
which must be populated with re-usable
concepts, methodologies, and theorem prover libraries
for full fruition.
The simple examples in \chapref{chap:exampleI} and \chapref{chap:exampleII},
and the discussion in \chapref{chap:general},
suggests a few initial ideas.
Working out examples of increasing complexity should suggest more ideas.\<close>


section \<open>Automated Transformations\<close>
text \<open>\label{sec:xform}\<close>

text \<open>A pop-refinement step from @{term spec\<^sub>i} can be performed manually,
by writing down \<open>spec\<^sub>i\<^sub>+\<^sub>1\<close> and proving \<open>spec\<^sub>i\<^sub>+\<^sub>1 p \<Longrightarrow> spec\<^sub>i p\<close>.
It is sometimes possible to generate \<open>spec\<^sub>i\<^sub>+\<^sub>1\<close> from @{term spec\<^sub>i},
along with a proof of \<open>spec\<^sub>i\<^sub>+\<^sub>1 p \<Longrightarrow> spec\<^sub>i p\<close>,
using automated transformation techniques like
term rewriting,
application of algorithmic templates,
and term construction by witness finding,
e.g.\ \cite{SmithMarktoberdorf,SpecwareWebSite}.
Automated transformations may require
parameters to be provided and applicability conditions to be proved,
but should generally save effort
and make derivations more robust against changes in requirement specifications.
Extending existing theorem provers with automated transformation capabilities
would be advantageous for pop-refinement.\<close>


section \<open>Other Kinds of Design Objects\<close>
text \<open>\label{sec:otherdesign}\<close>

text \<open>It has been suggested~\cite{LambertPrivate}
that pop-refinement could be used
to develop other kinds of design objects than programs,
e.g.\ protocols, digital circuits, and hybrid systems.
Perhaps pop-refinement could be used to develop
engines, cars, buildings, etc.
So long as these design objects can be described
by languages amenable to formalization,
pop-refinement should be applicable.\<close>


end %invisible
