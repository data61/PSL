subsection \<open>Basic Algorithms\<close>

theory BasicAlgorithms
  imports Data ErrorMonad
begin

text \<open>
  In this section, we introduce preliminary definitions and functions, required by the
  integration and edit algorithms in the following sections.
\<close>

definition ext_ids :: "('\<I>, '\<Sigma>) woot_character list \<Rightarrow> '\<I> extended list"
  where "ext_ids s = \<turnstile>#(map (\<lambda>x. \<lbrakk> I x \<rbrakk>) s)@[\<stileturn>]"

text \<open>
  The function @{term ext_ids} returns the set of extended identifiers in a string @{term s},
  including the beginning and end markers @{term "\<turnstile>"} and @{term "\<stileturn>"}.
\<close>

fun idx :: "('\<I>, '\<Sigma>) woot_character list \<Rightarrow> '\<I> extended \<Rightarrow> error + nat"
  where
    "idx s i = fromSingleton (filter (\<lambda>j. (ext_ids s ! j = i)) [0..<(length (ext_ids s))])"

text \<open>
  The function @{term idx} returns the index in @{term w} of a W-character with a given identifier
   @{term i}:
  %
  \begin{itemize}
  \item If the identifier @{term i} occurs exactly once in the string then
        @{term "idx s \<lbrakk>i\<rbrakk> = return (j+1)"} where @{term "I (s ! j) = i"}, otherwise
        @{term "idx s \<lbrakk>i\<rbrakk>"} will be an error.
  \item @{term "idx s \<turnstile> = Inr 0"} and @{term "idx s \<stileturn> = return (length w + 1)"}.
  \end{itemize}
\<close>

fun nth :: "('\<I>, '\<Sigma>) woot_character list \<Rightarrow> nat \<Rightarrow> error + ('\<I>, '\<Sigma>) woot_character"
  where
    "nth s 0 = error (STR ''Index has to be >= 1.'')" |
    "nth s (Suc k) = (
      if k < (length s) then
        return (s ! k)
      else
        error (STR ''Index has to be <= length s''))"

text \<open>
  The function @{text nth} returns the W-character at a given index in @{term s}.
  The first character has the index 1.
\<close>

fun list_update ::
  "('\<I>, '\<Sigma>) woot_character list \<Rightarrow> nat \<Rightarrow> ('\<I>, '\<Sigma>) woot_character \<Rightarrow> 
  error + ('\<I>, '\<Sigma>) woot_character list"
  where
    "list_update s (Suc k) v = (
        if k < length s then
          return (List.list_update s k v)
        else
          error (STR ''Illegal arguments.''))" |
    "list_update _ 0 _ = error (STR ''Illegal arguments.'')"

text \<open>
  The function @{text list_update} substitutes the W-character at the index @{term "k"} in
  @{term s} with the W-character @{term v}. As before, we use the convention of using the index 1
  for the first character.
\<close>

end
