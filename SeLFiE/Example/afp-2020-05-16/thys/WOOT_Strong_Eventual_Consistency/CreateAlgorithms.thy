subsection \<open>Edit Operations \label{sec:edit}\<close>

theory CreateAlgorithms
  imports BasicAlgorithms
begin

fun is_visible :: "('\<I>, '\<Sigma>) woot_character \<Rightarrow> bool"
  where "is_visible (InsertMessage _ _ _ s) = (s \<noteq> None)"

fun nth_visible :: "('\<I>, '\<Sigma>) woot_character list \<Rightarrow> nat \<Rightarrow> error + '\<I> extended"
  where
    "nth_visible s k = (let v = ext_ids (filter is_visible s) in 
      if k < length v then 
        return (v ! k) 
      else 
        error (STR ''Argument k out of bounds.''))"

text \<open>Let @{term l} be the count of visible symbols in @{term s}. The function
  @{term "nth_visible s n"}:
  %
  \begin{itemize}
  \item Returns the identifier of the $n$-th visible element in $s$ if $1 \leq n \leq l$.
  \item Returns @{term \<turnstile>} if $n = 0$, and @{term \<stileturn>} if $n = l + 1$.
  \item Returns an error otherwise.
  \end{itemize}
  %
  Note that, with this definition, the first visible character in the string has the index $1$.

  Algorithms @{text create_insert} and @{term create_delete} detail the process by which messages
  are created in response to a user action.\<close>

fun from_non_extended :: "'\<I> extended \<Rightarrow> error + '\<I>"
  where
    "from_non_extended \<lbrakk> i \<rbrakk> = Inr i" |
    "from_non_extended _ = error (STR ''Expected InString'')"

fun create_insert :: 
  "('\<I>, '\<Sigma>) woot_character list \<Rightarrow> nat \<Rightarrow> '\<Sigma> \<Rightarrow>  '\<I> \<Rightarrow> error + ('\<I>, '\<Sigma>) message"
  where "create_insert s n \<sigma>' i =
    do {
      p \<leftarrow> nth_visible s n;
      q \<leftarrow> nth_visible s (n + 1);
      return (Insert (InsertMessage p i q \<sigma>'))
    }"

text \<open>In particular, when a user inserts a character @{term \<sigma>'} between visible position
  @{term n} and its successor of the string of a peer with state @{term s}, @{term create_insert}
  starts by retrieving the identifiers @{term p} of the last visible character before @{term n}
  in @{term w} (or @{term \<turnstile>} if no such character exists) and @{text q} of the first
  visible one after @{term n} (or @{term \<stileturn>}).

  It then broadcasts the message @{term "Insert (InsertMessage p i q \<sigma>')"} with the new
  identifier @{term i}.\<close>

fun create_delete :: "('\<I>, '\<Sigma>) woot_character list \<Rightarrow> nat \<Rightarrow> error + ('\<I>, '\<Sigma>) message"
  where "create_delete s n =
    do {
      m \<leftarrow> nth_visible s n;
      i \<leftarrow> from_non_extended m;
      return (Delete (DeleteMessage i))
    }"

text \<open>When the user deletes the visible character at position @{term n}, @{term create_delete}
  retrieves the identifier @{term i} of the @{term n}'th visible character in @{term s} and
  broadcasts the message @{term "Delete (DeleteMessage i)"}.

  In both cases the message will be integrated into the peer's own state, with the same
  algorithm that integrates messages received from other peers.\<close>

end