(*<*)
theory Examples
  imports Monitor_Code
begin
(*>*)

section \<open>Examples\<close>

abbreviation "TT \<equiv> MFOTL.Eq (MFOTL.Const ''_'') (MFOTL.Const ''_'')"
abbreviation "Eventually I \<psi> \<equiv> MFOTL.Until TT I \<psi>"

definition "\<phi>\<^sub>e\<^sub>x = MFOTL.And_Not (MFOTL.Pred ''A'' [MFOTL.Var 0])
  (Eventually (interval 1 2) (MFOTL.Exists (MFOTL.Pred ''B'' [MFOTL.Var 1, MFOTL.Var 0])))"

lemma "mmonitorable \<phi>\<^sub>e\<^sub>x" by eval

text \<open>Offline monitoring:\<close>

lift_definition \<pi>\<^sub>e\<^sub>x :: "string MFOTL.prefix" is
  "[ ({(''A'', [''d'']), (''A'', [''e''])}, 1)
   , ({(''B'', [''d'', ''f''])}, 2)
   , ({(''B'', [''e'', ''f''])}, 5)
  ]"
  by simp

lemma "monitor \<phi>\<^sub>e\<^sub>x \<pi>\<^sub>e\<^sub>x = {(0, [Some ''e''])}" by eval

text \<open>Online monitoring:\<close>

definition "m1 = mstep ({(''A'', [''d'']), (''A'', [''e''])}, 1) (minit \<phi>\<^sub>e\<^sub>x)"
definition "m2 = mstep ({(''B'', [''d'', ''f''])}, 2) (snd m1)"
definition "m3 = mstep ({(''B'', [''e'', ''f''])}, 5) (snd m2)"

lemma "fst m1 = {}" by eval
lemma "fst m2 = {}" by eval
lemma "fst m3 = {(0, [Some ''e''])}" by eval


text \<open>Operation of the monitor:\<close>

lemma "minit \<phi>\<^sub>e\<^sub>x = \<lparr>
  mstate_i = 0,
  mstate_m =
    MAnd (MPred ''A'' [MFOTL.Var 0]) False
     (MUntil True (MRel {[None]}) (interval 1 2) (MExists (MPred ''B'' [MFOTL.Var 1, MFOTL.Var 0]))
       ([], []) [] [])
     ([], []),
  mstate_n = 1\<rparr>"
  by eval

lemma "mstate_m (snd m1) = MAnd (MPred ''A'' [MFOTL.Var 0]) False
  (MUntil True (MRel {[None]}) (interval 1 2) (MExists (MPred ''B'' [MFOTL.Var 1, MFOTL.Var 0]))
    ([], []) [] [(1, {[None]}, {})])
  ([{[Some ''d''], [Some ''e'']}], [])"
  by eval

lemma "mstate_m (snd m2) = MAnd (MPred ''A'' [MFOTL.Var 0]) False
  (MUntil True (MRel {[None]}) (interval 1 2) (MExists (MPred ''B'' [MFOTL.Var 1, MFOTL.Var 0]))
   ([], []) [] [(1, {[None]}, {[Some ''d'']}), (2, {[None]}, {})])
  ([{[Some ''d''], [Some ''e'']}, {}], [])"
  by eval

lemma "mstate_m (snd m3) = MAnd (MPred ''A'' [MFOTL.Var 0]) False
  (MUntil True (MRel {[None]}) (interval 1 2) (MExists (MPred ''B'' [MFOTL.Var 1, MFOTL.Var 0]))
    ([], []) [] [(5, {[None]}, {})])
  ([{}], [])"
  by eval

(*<*)
end
(*>*)
