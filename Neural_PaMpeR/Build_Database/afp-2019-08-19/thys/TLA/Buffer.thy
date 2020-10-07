(*  Title:       A Definitional Encoding of TLA in Isabelle/HOL
    Authors:     Gudmund Grov <ggrov at inf.ed.ac.uk>
                 Stephan Merz <Stephan.Merz at loria.fr>
    Year:        2011
    Maintainer:  Gudmund Grov <ggrov at inf.ed.ac.uk>
*)

section \<open>Refining a Buffer Specification\<close>

theory Buffer
imports State
begin

text \<open>
  We specify a simple FIFO buffer and prove that two FIFO buffers
  in a row implement a FIFO buffer.
\<close>

subsection "Buffer specification"

text \<open>
  The following definitions all take three parameters: a state function
  representing the input channel of the FIFO buffer, another representing
  the internal queue, and a third one representing the output channel.
  These parameters will be instantiated later in the definition of the
  double FIFO.
\<close>

definition BInit :: "'a statefun \<Rightarrow> 'a list statefun \<Rightarrow> 'a statefun \<Rightarrow> temporal"
where "BInit ic q oc \<equiv> TEMP $q = #[]
                          \<and> $ic = $oc"   \<comment> \<open>initial condition of buffer\<close>

definition Enq :: "'a statefun \<Rightarrow> 'a list statefun \<Rightarrow> 'a statefun \<Rightarrow> temporal"
where "Enq ic q oc \<equiv> TEMP ic$ \<noteq> $ic
                        \<and> q$ = $q @ [ ic$ ]
                        \<and> oc$ = $oc"     \<comment> \<open>enqueue a new value\<close>

definition Deq :: "'a statefun \<Rightarrow> 'a list statefun \<Rightarrow> 'a statefun \<Rightarrow> temporal"
where "Deq ic q oc \<equiv> TEMP # 0 < length<$q>
                        \<and> oc$ = hd<$q>
                        \<and> q$ = tl<$q>
                        \<and> ic$ = $ic"     \<comment> \<open>dequeue value at front\<close>

definition Nxt :: "'a statefun \<Rightarrow> 'a list statefun \<Rightarrow> 'a statefun \<Rightarrow> temporal"
where "Nxt ic q oc \<equiv> TEMP (Enq ic q oc \<or> Deq ic q oc)"

\<comment> \<open>internal specification with buffer visible\<close>
definition ISpec :: "'a statefun \<Rightarrow> 'a list statefun \<Rightarrow> 'a statefun \<Rightarrow> temporal"
where "ISpec ic q oc \<equiv> TEMP BInit ic q oc
                          \<and> \<box>[Nxt ic q oc]_(ic,q,oc)
                          \<and> WF(Deq ic q oc)_(ic,q,oc)"

\<comment> \<open>external specification: buffer hidden\<close>
definition Spec :: "'a statefun \<Rightarrow> 'a statefun \<Rightarrow> temporal"
where "Spec ic oc == TEMP (\<exists>\<exists> q. ISpec ic q oc)"

subsection "Properties of the buffer"

text \<open>
  The buffer never enqueues the same element twice. We therefore
  have the following invariant:
  \begin{itemize}
  \item any two subsequent elements in the queue are different, and
    the last element in the queue is different from the value of the
    output channel,
  \item if the queue is non-empty then the last element in the queue
    is the value that appears on the input channel,
  \item if the queue is empty then the values on the output and input
    channels are equal.
  \end{itemize}

  The following auxiliary predicate \<open>noreps\<close> is true if no
  two subsequent elements in a list are identical.
\<close>

definition noreps :: "'a list \<Rightarrow> bool"
where "noreps xs \<equiv> \<forall>i < length xs - 1. xs!i \<noteq> xs!(Suc i)"

definition BInv :: "'a statefun \<Rightarrow> 'a list statefun \<Rightarrow> 'a statefun \<Rightarrow> temporal"
where "BInv ic q oc \<equiv> TEMP List.last<$oc # $q> = $ic \<and> noreps<$oc # $q>"

lemmas buffer_defs = BInit_def Enq_def Deq_def Nxt_def 
                     ISpec_def Spec_def BInv_def

lemma ISpec_stutinv: "STUTINV (ISpec ic q oc)"
  unfolding buffer_defs by (simp add: bothstutinvs livestutinv)

lemma Spec_stutinv: "STUTINV Spec ic oc"
  unfolding buffer_defs by (simp add: bothstutinvs livestutinv eexSTUT)

text \<open>A lemma about lists that is useful in the following\<close>
lemma tl_self_iff_empty[simp]: "(tl xs = xs) = (xs = [])"
proof
  assume 1: "tl xs = xs"
  show "xs = []"
  proof (rule ccontr)
    assume "xs \<noteq> []" with 1 show "False"
      by (auto simp: neq_Nil_conv)
  qed
qed (auto)

lemma tl_self_iff_empty'[simp]: "(xs = tl xs) = (xs = [])"
proof
  assume 1: "xs = tl xs"
  show "xs = []"
  proof (rule ccontr)
    assume "xs \<noteq> []" with 1 show "False"
      by (auto simp: neq_Nil_conv)
  qed
qed (auto)

lemma Deq_visible:
  assumes v: "\<turnstile> Unchanged v \<longrightarrow> Unchanged q"
  shows "|~ <Deq ic q oc>_v = Deq ic q oc"
proof (auto simp: tla_defs)
  fix w
  assume deq: "w \<Turnstile> Deq ic q oc" and unch: "v (w (Suc 0)) = v (w 0)"
  from unch v[unlifted] have "q (w (Suc 0)) = q (w 0)"
    by (auto simp: tla_defs)
  with deq show "False" by (auto simp: Deq_def tla_defs)
qed

lemma Deq_enabledE: "\<turnstile> Enabled <Deq ic q oc>_(ic,q,oc) \<longrightarrow> $q ~= #[]"
  by (auto elim!: enabledE simp: Deq_def tla_defs)

text \<open>
  We now prove that \<open>BInv\<close> is an invariant of the Buffer
  specification.

  We need several lemmas about \<open>noreps\<close> that are used in the
  invariant proof.
\<close>

lemma noreps_empty [simp]: "noreps []"
  by (auto simp: noreps_def)

lemma noreps_singleton: "noreps [x]"  \<comment> \<open>special case of following lemma\<close>
  by (auto simp: noreps_def)

lemma noreps_cons [simp]:
  "noreps (x # xs) = (noreps xs \<and> (xs = [] \<or> x \<noteq> hd xs))"
proof (auto simp: noreps_singleton)
  assume cons: "noreps (x # xs)"
  show "noreps xs"
  proof (auto simp: noreps_def)
    fix i
    assume i: "i < length xs - Suc 0" and eq: "xs!i = xs!(Suc i)"
    from i have "Suc i < length (x#xs) - 1" by auto
    moreover
    from eq have "(x#xs)!(Suc i) = (x#xs)!(Suc (Suc i))" by auto
    moreover
    note cons
    ultimately show False by (auto simp: noreps_def)
  qed
next
  assume 1: "noreps (hd xs # xs)" and 2: "xs \<noteq> []"
  from 2 obtain x xxs where "xs = x # xxs" by (cases xs, auto)
  with 1 show False by (auto simp: noreps_def)
next
  assume 1: "noreps xs" and 2: "x \<noteq> hd xs"
  show "noreps (x # xs)"
  proof (auto simp: noreps_def)
    fix i
    assume i: "i < length xs" and eq: "(x # xs)!i = xs!i"
    from i obtain y ys where xs: "xs = y # ys" by (cases xs, auto)
    show False
    proof (cases i)
      assume "i = 0"
      with eq 2 xs show False by auto
    next
      fix k
      assume k: "i = Suc k"
      with i eq xs 1 show False by (auto simp: noreps_def)
    qed
  qed
qed

lemma noreps_append [simp]:
  "noreps (xs @ ys) = 
   (noreps xs \<and> noreps ys \<and> (xs = [] \<or> ys = [] \<or> List.last xs \<noteq> hd ys))"
proof auto
  assume 1: "noreps (xs @ ys)"
  show "noreps xs"
  proof (auto simp: noreps_def)
    fix i
    assume i: "i < length xs - Suc 0" and eq: "xs!i = xs!(Suc i)"
    from i have "i < length (xs @ ys) - Suc 0" by auto
    moreover
    from i eq have "(xs @ ys)!i = (xs@ys)!(Suc i)" by (auto simp: nth_append)
    moreover note 1
    ultimately show "False" by (auto simp: noreps_def)
  qed
next
  assume 1: "noreps (xs @ ys)"
  show "noreps ys"
  proof (auto simp: noreps_def)
    fix i
    assume i: "i < length ys - Suc 0" and eq: "ys!i = ys!(Suc i)"
    from i have "i + length xs < length (xs @ ys) - Suc 0" by auto
    moreover
    from i eq have "(xs @ ys)!(i+length xs) = (xs@ys)!(Suc (i + length xs))"
      by (auto simp: nth_append)
    moreover note 1
    ultimately show "False" by (auto simp: noreps_def)
  qed
next
  assume 1: "noreps (xs @ ys)" and 2: "xs \<noteq> []" and 3: "ys \<noteq> []"
     and 4: "List.last xs = hd ys"
  from 2 obtain x xxs where xs: "xs = x # xxs" by (cases xs, auto)
  from 3 obtain y yys where ys: "ys = y # yys" by (cases ys, auto)
  from xs ys have 5: "length xxs < length (xs @ ys) - 1" by auto
  from 4 xs ys have "(xs @ ys) ! (length xxs) = (xs @ ys) ! (Suc (length xxs))"
    by (auto simp: nth_append last_conv_nth)
  with 5 1 show "False" by (auto simp: noreps_def)
next
  assume 1: "noreps xs" and 2: "noreps ys" and 3: "List.last xs \<noteq> hd ys"
  show "noreps (xs @ ys)"
  proof (cases "xs = [] \<or> ys = []")
    case True
    with 1 2 show ?thesis by auto
  next
    case False
    then obtain x xxs where xs: "xs = x # xxs" by (cases xs, auto)
    from False obtain y yys where ys: "ys = y # yys" by (cases ys, auto)
    show ?thesis
    proof (auto simp: noreps_def)
      fix i
      assume i: "i < length xs + length ys - Suc 0"
         and eq: "(xs @ ys)!i = (xs @ ys)!(Suc i)"
      show "False"
      proof (cases "i < length xxs")
        case True
        hence "i < length (x # xxs)" by simp
        hence xsi: "((x # xxs) @ ys)!i = (x # xxs)!i"
          unfolding nth_append by simp
        from True have "(xxs @ ys)!i = xxs!i" by (auto simp: nth_append)
        with True xsi eq 1 xs show "False" by (auto simp: noreps_def)
      next
        assume i2: "\<not>(i < length xxs)"
        show False
        proof (cases "i = length xxs")
          case True
          with xs have xsi: "(xs @ ys)!i = List.last xs"
            by (auto simp: nth_append last_conv_nth)
          from True xs ys have "(xs @ ys)!(Suc i) = y"
            by (auto simp: nth_append)
          with 3 ys eq xsi show False by simp
        next
          case False
          with i2 xs have xsi: "\<not>(i < length xs)" by auto
          hence "(xs @ ys)!i = ys!(i - length xs)"
            by (simp add: nth_append)
          moreover
          from xsi have "Suc i - length xs = Suc (i - length xs)" by auto
          with xsi have "(xs @ ys)!(Suc i) = ys!(Suc (i - length xs))"
            by (simp add: nth_append)
          moreover
          from i xsi have "i - length xs < length ys - 1" by auto
          with 2 have "ys!(i - length xs) \<noteq> ys!(Suc (i - length xs))"
            by (auto simp: noreps_def)
          moreover
          note eq
          ultimately show False by simp
        qed
      qed
    qed
  qed
qed

lemma ISpec_BInv_lemma:
  "\<turnstile> BInit ic q oc \<and> \<box>[Nxt ic q oc]_(ic,q,oc) \<longrightarrow> \<box>(BInv ic q oc)"
proof (rule invmono)
  show "\<turnstile> BInit ic q oc \<longrightarrow> BInv ic q oc"
    by (auto simp: BInit_def BInv_def)
next
  have enq: "|~ Enq ic q oc \<longrightarrow> BInv ic q oc \<longrightarrow> \<circle>(BInv ic q oc)"
    by (auto simp: Enq_def BInv_def tla_defs)
  have deq: "|~ Deq ic q oc \<longrightarrow> BInv ic q oc \<longrightarrow> \<circle>(BInv ic q oc)"
    by (auto simp: Deq_def BInv_def tla_defs neq_Nil_conv)
  have unch: "|~ Unchanged (ic,q,oc) \<longrightarrow> BInv ic q oc \<longrightarrow> \<circle>(BInv ic q oc)"
    by (auto simp: BInv_def tla_defs)
  show "|~ BInv ic q oc \<and> [Nxt ic q oc]_(ic, q, oc) \<longrightarrow> \<circle>(BInv ic q oc)"
    by (auto simp: Nxt_def actrans_def 
             elim: enq[unlift_rule] deq[unlift_rule] unch[unlift_rule])
qed

theorem ISpec_BInv: "\<turnstile> ISpec ic q oc \<longrightarrow> \<box>(BInv ic q oc)"
  by (auto simp: ISpec_def intro: ISpec_BInv_lemma[unlift_rule])


subsection "Two FIFO buffers in a row implement a buffer"

locale DBuffer =
  fixes inp :: "'a statefun"       \<comment> \<open>input channel for double FIFO\<close>
    and mid :: "'a statefun"       \<comment> \<open>channel linking the two buffers\<close>
    and out :: "'a statefun"       \<comment> \<open>output channel for double FIFO\<close>
    and q1  :: "'a list statefun"  \<comment> \<open>inner queue of first FIFO\<close>
    and q2  :: "'a list statefun"  \<comment> \<open>inner queue of second FIFO\<close>
    and vars
  defines "vars \<equiv> LIFT (inp,mid,out,q1,q2)"
  assumes DB_base: "basevars vars"
begin

  text \<open>
    We need to specify the behavior of two FIFO buffers in a row.
    Intuitively, that specification is just the conjunction of
    two buffer specifications, where the first buffer has input
    channel \<open>inp\<close> and output channel \<open>mid\<close> whereas
    the second one receives from \<open>mid\<close> and outputs on \<open>out\<close>.
    However, this conjunction allows a simultaneous enqueue action
    of the first buffer and dequeue of the second one. It would not
    implement the previous buffer specification, which excludes such
    simultaneous enqueueing and dequeueing (it is written in
    ``interleaving style''). We could relax the specification of
    the FIFO buffer above, which is esthetically pleasant, but
    non-interleaving specifications are usually hard to get right
    and to understand. We therefore impose an interleaving constraint
    on the specification of the double buffer, which requires that
    enqueueing and dequeueing do not happen simultaneously.
\<close>

  definition DBSpec
  where "DBSpec \<equiv> TEMP ISpec inp q1 mid
                     \<and> ISpec mid q2 out
                     \<and> \<box>[\<not>(Enq inp q1 mid \<and> Deq mid q2 out)]_vars"

  text \<open>
    The proof rules of TLA are geared towards specifications of the
    form \<open>Init \<and> \<box>[Next]_vars \<and> L\<close>, and we prove that
    \<open>DBSpec\<close> corresponds to a specification in this form,
    which we now define.
\<close>

  definition FullInit
  where "FullInit \<equiv> TEMP (BInit inp q1 mid \<and> BInit mid q2 out)"

  definition FullNxt
  where "FullNxt \<equiv> TEMP (Enq inp q1 mid \<and> Unchanged (q2,out)
                       \<or> Deq inp q1 mid \<and> Enq mid q2 out
                       \<or> Deq mid q2 out \<and> Unchanged (inp,q1))"

  definition FullSpec
  where "FullSpec \<equiv> TEMP FullInit
                       \<and> \<box>[FullNxt]_vars
                       \<and> WF(Deq inp q1 mid)_vars
                       \<and> WF(Deq mid q2 out)_vars"

  text \<open>
    The concatenation of the two queues will serve as the refinement mapping.
\<close>
  definition qc :: "'a list statefun"
  where "qc \<equiv> LIFT (q2 @ q1)"


  lemmas db_defs = buffer_defs DBSpec_def FullInit_def FullNxt_def FullSpec_def
                   qc_def vars_def

  lemma DBSpec_stutinv: "STUTINV DBSpec"
    unfolding db_defs by (simp add: bothstutinvs livestutinv)

  lemma FullSpec_stutinv: "STUTINV FullSpec"
    unfolding db_defs by (simp add: bothstutinvs livestutinv)

  text \<open>
    We prove that \<open>DBSpec\<close> implies \<open>FullSpec\<close>. (The converse
    implication also holds but is not needed for our implementation proof.)
\<close>

  text \<open>
    The following lemma is somewhat more bureaucratic than we'd like
    it to be. It shows that the conjunction of the next-state relations,
    together with the invariant for the first queue, implies the full
    next-state relation of the combined queues.
\<close>
  lemma DBNxt_then_FullNxt:
    "\<turnstile> \<box>BInv inp q1 mid
        \<and> \<box>[Nxt inp q1 mid]_(inp,q1,mid) 
        \<and> \<box>[Nxt mid q2 out]_(mid,q2,out)
        \<and> \<box>[\<not>(Enq inp q1 mid \<and> Deq mid q2 out)]_vars
        \<longrightarrow> \<box>[FullNxt]_vars"
    (is "\<turnstile> \<box>?inv \<and> ?nxts \<longrightarrow> \<box>[FullNxt]_vars")
  proof -
    have "\<turnstile> \<box>[Nxt inp q1 mid]_(inp,q1,mid)
          \<and> \<box>[Nxt mid q2 out]_(mid,q2,out)
          \<longrightarrow> \<box>[  [Nxt inp q1 mid]_(inp,q1,mid) 
               \<and> [Nxt mid q2 out]_(mid,q2,out)]_((inp,q1,mid),(mid,q2,out))"
      (is "\<turnstile> ?tmp \<longrightarrow> \<box>[?b1b2]_?vs")
      by (auto simp: M12[int_rewrite])
    moreover
    have "\<turnstile> \<box>[?b1b2]_?vs \<longrightarrow> \<box>[?b1b2]_vars"
      by (rule R1, auto simp: vars_def tla_defs)
    ultimately
    have 1: "\<turnstile> \<box>[Nxt inp q1 mid]_(inp,q1,mid)
             \<and> \<box>[Nxt mid q2 out]_(mid,q2,out)
             \<longrightarrow> \<box>[  [Nxt inp q1 mid]_(inp,q1,mid) 
                   \<and> [Nxt mid q2 out]_(mid,q2,out) ]_vars"
      by force
    have 2: "\<turnstile> \<box>[?b1b2]_vars \<and> \<box>[\<not>(Enq inp q1 mid \<and> Deq mid q2 out)]_vars
               \<longrightarrow> \<box>[?b1b2 \<and> \<not>(Enq inp q1 mid \<and> Deq mid q2 out)]_vars"
      (is "\<turnstile> ?tmp2 \<longrightarrow> \<box>[?mid]_vars")
      by (simp add: M8[int_rewrite])
    have "\<turnstile> ?inv \<longrightarrow> #True" by auto
    moreover
    have "|~ ?inv \<and> \<circle>?inv \<and> [?mid]_vars \<longrightarrow> [FullNxt]_vars"
    proof -
      have "|~ ?inv \<and> ?mid \<longrightarrow> [FullNxt]_vars"
      proof -
        have A: "|~ Nxt inp q1 mid
                    \<longrightarrow> [Nxt mid q2 out]_(mid,q2,out)
                    \<longrightarrow> \<not>(Enq inp q1 mid \<and> Deq mid q2 out)
                    \<longrightarrow> ?inv
                    \<longrightarrow> FullNxt"
        proof -
          have enq: "|~ Enq inp q1 mid
                        \<and> [Nxt mid q2 out]_(mid,q2,out)
                        \<and> \<not>(Deq mid q2 out)
                        \<longrightarrow> Unchanged (q2,out)"
            by (auto simp: db_defs tla_defs)
          have deq1: "|~ Deq inp q1 mid \<longrightarrow> ?inv \<longrightarrow> mid$ \<noteq> $mid"
            by (auto simp: Deq_def BInv_def)
          have deq2: "|~ Deq mid q2 out \<longrightarrow> mid$ = $mid"
            by (auto simp: Deq_def)
          have deq: "|~ Deq inp q1 mid
                        \<and> [Nxt mid q2 out]_(mid,q2,out)
                        \<and> ?inv
                        \<longrightarrow> Enq mid q2 out"
            by (force simp: Nxt_def tla_defs
                      dest: deq1[unlift_rule] deq2[unlift_rule])
          with enq show ?thesis by (force simp: Nxt_def FullNxt_def)
        qed
        have B: "|~ Nxt mid q2 out
                    \<longrightarrow> Unchanged (inp,q1,mid)
                    \<longrightarrow> FullNxt"
          by (auto simp: db_defs tla_defs)
        have C: "\<turnstile> Unchanged (inp,q1,mid) 
                \<longrightarrow> Unchanged (mid,q2,out)
                \<longrightarrow> Unchanged vars"
          by (auto simp: vars_def tla_defs)
        show ?thesis
          by (force simp: actrans_def 
                    dest: A[unlift_rule] B[unlift_rule] C[unlift_rule])
      qed
      thus ?thesis by (auto simp: tla_defs)
    qed
    ultimately
    have "\<turnstile> \<box>?inv \<and> \<box>[?mid]_vars \<longrightarrow> \<box>#True \<and> \<box>[FullNxt]_vars"
      by (rule TLA2)
    with 1 2 show ?thesis by force
  qed

  text \<open>
    It is now easy to show that \<open>DBSpec\<close> refines \<open>FullSpec\<close>.
\<close>
  theorem DBSpec_impl_FullSpec: "\<turnstile> DBSpec \<longrightarrow> FullSpec"
  proof -
    have 1: "\<turnstile> DBSpec \<longrightarrow> FullInit"
      by (auto simp: DBSpec_def FullInit_def ISpec_def)
    have 2: "\<turnstile> DBSpec \<longrightarrow> \<box>[FullNxt]_vars"
    proof -
      have "\<turnstile> DBSpec \<longrightarrow> \<box>(BInv inp q1 mid)"
        by (auto simp: DBSpec_def intro: ISpec_BInv[unlift_rule])
      moreover have "\<turnstile> DBSpec \<and> \<box>(BInv inp q1 mid) \<longrightarrow> \<box>[FullNxt]_vars"
        by (auto simp: DBSpec_def ISpec_def
                 intro: DBNxt_then_FullNxt[unlift_rule])
      ultimately show ?thesis by force
    qed
    have 3: "\<turnstile> DBSpec \<longrightarrow> WF(Deq inp q1 mid)_vars"
    proof -
      have 31: "\<turnstile> Unchanged vars \<longrightarrow> Unchanged q1"
        by (auto simp: vars_def tla_defs)
      have 32: "\<turnstile> Unchanged (inp,q1,mid) \<longrightarrow> Unchanged q1"
        by (auto simp: tla_defs)
      have deq: "|~ \<langle>Deq inp q1 mid\<rangle>_vars = \<langle>Deq inp q1 mid\<rangle>_(inp,q1,mid)"
        by (simp add: Deq_visible[OF 31, int_rewrite] 
                      Deq_visible[OF 32, int_rewrite])
      show ?thesis
        by (auto simp: DBSpec_def ISpec_def WeakF_def 
                       deq[int_rewrite] deq[THEN AA26,int_rewrite])
    qed
    have 4: "\<turnstile> DBSpec \<longrightarrow> WF(Deq mid q2 out)_vars"
    proof -
      have 41: "\<turnstile> Unchanged vars \<longrightarrow> Unchanged q2"
        by (auto simp: vars_def tla_defs)
      have 42: "\<turnstile> Unchanged (mid,q2,out) \<longrightarrow> Unchanged q2"
        by (auto simp: tla_defs)
      have deq: "|~ \<langle>Deq mid q2 out\<rangle>_vars = \<langle>Deq mid q2 out\<rangle>_(mid,q2,out)"
        by (simp add: Deq_visible[OF 41, int_rewrite] 
                      Deq_visible[OF 42, int_rewrite])
      show ?thesis
        by (auto simp: DBSpec_def ISpec_def WeakF_def 
                       deq[int_rewrite] deq[THEN AA26,int_rewrite])
    qed
    show ?thesis
      by (auto simp: FullSpec_def 
               elim: 1[unlift_rule] 2[unlift_rule] 3[unlift_rule] 
                     4[unlift_rule])
  qed

  text \<open>
    We now prove that two FIFO buffers in a row (as specified by formula
    \<open>FullSpec\<close>) implement a FIFO buffer whose internal queue is the
    concatenation of the two buffers. We start by proving step simulation.
\<close>  

  lemma FullInit: "\<turnstile> FullInit \<longrightarrow> BInit inp qc out"
    by (auto simp: db_defs tla_defs)

  lemma Full_step_simulation:
    "|~ [FullNxt]_vars \<longrightarrow> [Nxt inp qc out]_(inp,qc,out)"
    by (auto simp: db_defs tla_defs)

  text \<open>
    The liveness condition requires that the combined buffer
    eventually performs a \<open>Deq\<close> action on the output channel
    if it contains some element. The idea is to use the
    fairness hypothesis for the first buffer to prove that in that
    case, eventually the queue of the second buffer will be
    non-empty, and that it must therefore eventually dequeue
    some element.

    The first step is to establish the enabledness conditions
    for the two \<open>Deq\<close> actions of the implementation.
\<close>

  lemma Deq1_enabled: "\<turnstile> Enabled \<langle>Deq inp q1 mid\<rangle>_vars = ($q1 \<noteq> #[])"
  proof -
    have 1: "|~ \<langle>Deq inp q1 mid\<rangle>_vars = Deq inp q1 mid"
      by (rule Deq_visible, auto simp: vars_def tla_defs)
    have "\<turnstile> Enabled (Deq inp q1 mid) = ($q1 \<noteq> #[])"
      by (force simp: Deq_def tla_defs vars_def
                intro: base_enabled[OF DB_base] elim!: enabledE)
    thus ?thesis by (simp add: 1[int_rewrite])
  qed

  lemma Deq2_enabled: "\<turnstile> Enabled \<langle>Deq mid q2 out\<rangle>_vars = ($q2 \<noteq> #[])"
  proof -
    have 1: "|~ \<langle>Deq mid q2 out\<rangle>_vars = Deq mid q2 out"
      by (rule Deq_visible, auto simp: vars_def tla_defs)
    have "\<turnstile> Enabled (Deq mid q2 out) = ($q2 \<noteq> #[])"
      by (force simp: Deq_def tla_defs vars_def
                intro: base_enabled[OF DB_base] elim!: enabledE)
    thus ?thesis by (simp add: 1[int_rewrite])
  qed

  text \<open>
    We now use rule \<open>WF2\<close> to prove that the combined buffer
    (behaving according to specification \<open>FullSpec\<close>)
    implements the fairness condition of the single buffer under
    the refinement mapping.
\<close>
  lemma Full_fairness:
    "\<turnstile> \<box>[FullNxt]_vars \<and> WF(Deq mid q2 out)_vars \<and> \<box>WF(Deq inp q1 mid)_vars
       \<longrightarrow> WF(Deq inp qc out)_(inp,qc,out)"
  proof (rule WF2)
    \<comment> \<open>the helpful action is the @{text Deq} action of the second queue\<close>
    show "|~ \<langle>FullNxt \<and> Deq mid q2 out\<rangle>_vars \<longrightarrow> \<langle>Deq inp qc out\<rangle>_(inp,qc,out)"
      by (auto simp: db_defs tla_defs)
  next
    \<comment> \<open>the helpful condition is the second queue being non-empty\<close>
    show "|~ ($q2 \<noteq> #[]) \<and> \<circle>($q2 \<noteq> #[]) \<and> \<langle>FullNxt \<and> Deq mid q2 out\<rangle>_vars 
             \<longrightarrow> Deq mid q2 out"
      by (auto simp: tla_defs)
  next
    show "\<turnstile> $q2 \<noteq> #[] \<and> Enabled \<langle>Deq inp qc out\<rangle>_(inp, qc, out)
             \<longrightarrow> Enabled \<langle>Deq mid q2 out\<rangle>_vars"
      unfolding Deq2_enabled[int_rewrite] by auto
  next
    txt \<open>
      The difficult part of the proof is to show that the helpful
      condition will eventually always be true provided that the
      combined dequeue action is eventually always enabled and that
      the helpful action is never executed. We prove that (1) the
      helpful condition persists and (2) that it must eventually
      become true.
\<close>
    have "\<turnstile> \<box>\<box>[FullNxt \<and> \<not>(Deq mid q2 out)]_vars
            \<longrightarrow> \<box>($q2 \<noteq> #[] \<longrightarrow> \<box>($q2 \<noteq> #[]))"
    proof (rule STL4)
      have "|~ $q2 \<noteq> #[] \<and> [FullNxt \<and> \<not>(Deq mid q2 out)]_vars
               \<longrightarrow> \<circle>($q2 \<noteq> #[])"
        by (auto simp: db_defs tla_defs)
      from this[THEN INV1]
      show "\<turnstile> \<box>[FullNxt \<and> \<not> Deq mid q2 out]_vars
              \<longrightarrow> ($q2 \<noteq> #[] \<longrightarrow> \<box>($q2 \<noteq> #[]))"
        by auto
    qed
    hence 1: "\<turnstile> \<box>[FullNxt \<and> \<not>(Deq mid q2 out)]_vars
                \<longrightarrow> \<diamond>($q2 \<noteq> #[]) \<longrightarrow> \<diamond>\<box>($q2 \<noteq> #[])"
      by (force intro: E31[unlift_rule])
    have 2: "\<turnstile> \<box>[FullNxt \<and> \<not>(Deq mid q2 out)]_vars
               \<and> WF(Deq inp q1 mid)_vars
               \<longrightarrow> (Enabled \<langle>Deq inp qc out\<rangle>_(inp, qc, out) \<leadsto> $q2 \<noteq> #[])"
    proof -
      have qc: "\<turnstile> ($qc \<noteq> #[]) = ($q1 \<noteq> #[] \<or> $q2 \<noteq> #[])"
        by (auto simp: qc_def tla_defs)
      have "\<turnstile> \<box>[FullNxt \<and> \<not>(Deq mid q2 out)]_vars \<and> WF(Deq inp q1 mid)_vars
              \<longrightarrow> ($q1 \<noteq> #[] \<leadsto> $q2 \<noteq> #[])"
      proof (rule WF1)
        show "|~ $q1 \<noteq> #[] \<and> [FullNxt \<and> \<not> Deq mid q2 out]_vars
                 \<longrightarrow> \<circle>($q1 \<noteq> #[]) \<or> \<circle>($q2 \<noteq> #[])"
          by (auto simp: db_defs tla_defs)
      next
        show "|~ $q1 \<noteq> #[] 
                 \<and> \<langle>(FullNxt \<and> \<not> Deq mid q2 out) \<and> Deq inp q1 mid\<rangle>_vars \<longrightarrow>
                 \<circle>($q2 \<noteq> #[])"
          by (auto simp: db_defs tla_defs)
      next
        show "\<turnstile> $q1 \<noteq> #[] \<longrightarrow> Enabled \<langle>Deq inp q1 mid\<rangle>_vars"
          by (simp add: Deq1_enabled[int_rewrite])
      next
        show "|~ $q1 \<noteq> #[] \<and> Unchanged vars \<longrightarrow> \<circle>($q1 \<noteq> #[])"
          by (auto simp: vars_def tla_defs)
      qed
      hence "\<turnstile> \<box>[FullNxt \<and> \<not>(Deq mid q2 out)]_vars 
                  \<and> WF(Deq inp q1 mid)_vars
                  \<longrightarrow> ($qc \<noteq> #[] \<leadsto> $q2 \<noteq> #[])"
        by (auto simp: qc[int_rewrite] LT17[int_rewrite] LT1[int_rewrite])
      moreover
      have "\<turnstile> Enabled \<langle>Deq inp qc out\<rangle>_(inp, qc, out) \<leadsto> $qc \<noteq> #[]"
        by (rule Deq_enabledE[THEN LT3])
      ultimately show ?thesis by (force elim: LT13[unlift_rule])
    qed
    with LT6 
    have "\<turnstile> \<box>[FullNxt \<and> \<not>(Deq mid q2 out)]_vars
             \<and> WF(Deq inp q1 mid)_vars
             \<and> \<diamond>Enabled \<langle>Deq inp qc out\<rangle>_(inp, qc, out)
             \<longrightarrow> \<diamond>($q2 \<noteq> #[])"
      by force
    with 1 E16
    show "\<turnstile> \<box>[FullNxt \<and> \<not>(Deq mid q2 out)]_vars
            \<and> WF(Deq mid q2 out)_vars
            \<and> \<box>WF(Deq inp q1 mid)_vars
            \<and> \<diamond>\<box> Enabled \<langle>Deq inp qc out\<rangle>_(inp, qc, out)
            \<longrightarrow> \<diamond>\<box>($q2 \<noteq> #[])"
      by force
  qed

  text \<open>
    Putting everything together, we obtain that \<open>FullSpec\<close> refines
    the Buffer specification under the refinement mapping.
\<close>
  theorem FullSpec_impl_ISpec: "\<turnstile> FullSpec \<longrightarrow> ISpec inp qc out"
    unfolding FullSpec_def ISpec_def
    using FullInit Full_step_simulation[THEN M11] Full_fairness
    by force

  theorem FullSpec_impl_Spec: "\<turnstile> FullSpec \<longrightarrow> Spec inp out"
    unfolding Spec_def using FullSpec_impl_ISpec
    by (force intro: eexI[unlift_rule])

  text \<open>
    By transitivity, two buffers in a row also implement a single buffer.
\<close>
  theorem DBSpec_impl_Spec: "\<turnstile> DBSpec \<longrightarrow> Spec inp out"
    by (rule lift_imp_trans[OF DBSpec_impl_FullSpec FullSpec_impl_Spec])

end \<comment> \<open>locale DBuffer\<close>

end
