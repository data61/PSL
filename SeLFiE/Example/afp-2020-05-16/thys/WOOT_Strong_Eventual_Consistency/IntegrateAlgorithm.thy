subsection \<open>Integration algorithm \label{sec:integrate}\<close>

text \<open>In this section we describe the algorithm to integrate a received message into a peers'
  state.\<close>

theory IntegrateAlgorithm
  imports BasicAlgorithms Data
begin

fun fromSome :: "'a option \<Rightarrow> error + 'a"
  where
    "fromSome (Some x) = return x" |
    "fromSome None = error (STR ''Expected Some'')"

lemma fromSome_ok_simp [simp]: "(fromSome x = Inr y) = (x = Some y)"
  by (cases x, simp+)

fun substr :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "substr s l u = take (u - (Suc l)) (drop l s)"

fun concurrent ::
  "('a, 's) woot_character list
  \<Rightarrow> nat
  \<Rightarrow> nat
  \<Rightarrow> ('a, 's) woot_character
  \<Rightarrow> error + ('a extended list)"
  where
    "concurrent s l u w =
      do {
        p_pos \<leftarrow> idx s (P w);
        s_pos \<leftarrow> idx s (S w);
        return (if (p_pos \<le> l \<and> s_pos \<ge> u) then [\<lbrakk>I w\<rbrakk>] else [])
      }"

function integrate_insert
  where
    "integrate_insert m w p s =
      do {
        l \<leftarrow> idx w p;
        u \<leftarrow> idx w s;
        assert (l < u);
        if Suc l = u then
          return ((take l w)@[to_woot_char m]@(drop l w))
        else do {
          d \<leftarrow> mapM (concurrent w l u) (substr w l u);
          assert (concat d \<noteq> []);
          (p', s') \<leftarrow> fromSome (find ((\<lambda>x.\<lbrakk>I m\<rbrakk> < x \<or> x = s) \<circ> snd) 
                        (zip (p#concat d) (concat d@[s])));
          integrate_insert m w p' s'
        }
      }"
  by fastforce+

fun integrate_delete ::
  "('a :: linorder) delete_message
  \<Rightarrow> ('a, 's) woot_character list
  \<Rightarrow> error + ('a, 's) woot_character list"
  where
    "integrate_delete (DeleteMessage i) s =
      do {
        k \<leftarrow> idx s \<lbrakk>i\<rbrakk>;
        w \<leftarrow> nth s k;
        list_update s k 
          (case w of (InsertMessage p i u _) \<Rightarrow> InsertMessage p i u None)
      }"

fun integrate ::
  "('a, 's) woot_character list
  \<Rightarrow> ('a :: linorder, 's) message
  \<Rightarrow> error + ('a, 's) woot_character list"
  where
    "integrate s (Insert m) = integrate_insert m s (P m) (S m)" |
    "integrate s (Delete m) = integrate_delete m s"

text \<open>Algorithm @{term integrate} describes the main function that is called when a new message
  @{term m} has to be integrated into the state @{term s} of a peer.
  It is called both when @{term m} was generated locally or received from another peer.
  Note that we require that the antecedant messages have already been integrated. See also 
  Section \ref{sec:networkModel} for the delivery assumptions that ensure this requirement.

  Algorithm @{term integrate_delete} describes the procedure to integrate a delete message:
  @{term "DeleteMessage i"}.
  The algorithm just replaces the symbol of the W-character with identifier @{term i} with the value
  @{term "None"}.
  It is not possible to entirely remove a W-character if it is deleted, since there might be 
  unreceived insertion messages that depend on its position.

  Algorithm @{term integrate_insert} describes the procedure to integrate an insert message:
  @{term "m = InsertMessage p i s \<sigma>"}.
  Since insertion operations can happen concurrently and the order of message delivery is not fixed,
  it can happen that a remote peer receiving @{term m} finds multiple possible insertion points 
  between the predecessor @{term p} and successor @{term s} that were recorded when the message 
  was generated.
  An example of this situation is the conflict between
  @{term "InsertMessage \<turnstile> (A,0 :: nat) \<stileturn> (CHR ''I'')"} and @{term "InsertMessage \<turnstile> (B,0 :: nat) \<stileturn> (CHR ''N'')"}
  in Figure~\ref{fig:session}.

  A first attempt to resolve this would be to insert the W-characters by choosing an insertion point
  using the order induced by their identifiers to achieve a consistent ordering.
  But this method fails in some cases: a counter-example was found by 
  Oster et al.~\cite[section 2]{oster2006data}.

  The solution introduced by the authors of WOOT is to restrict the identifier comparison to the 
  set of W-characters in the range @{term "substr l u s"} whose predecessor and successor are
  outside of the possible range, i.e. @{text "idx s (P w) \<le> l"} and @{text "idx s (S w) \<ge> u"}.

  New narrowed bounds are selected by finding the first W-character within that restricted set 
  with an identifier strictly larger than the identifier of the new W-character.

  This leads to a narrowed range where the found character forms an upper bound and its immediately
  preceeding character the lower bound. The method is applied recursively until the insertion point 
  is uniquely determined.

  Note that the fact that this strategy leads to a consistent ordering has only been verified for a
  bounded model.
  One of the contributions of this paper is to provide a complete proof for it.\<close>

end