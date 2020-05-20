(*  Author:     Lukas Bulwahn, TU Muenchen, 2009  *)

theory Execute
imports secTypes
begin

section \<open>Executing the small step semantics\<close>

code_pred (modes: i => o => bool as exec_red, i => i * o => bool, i => o * i => bool, i => i => bool) red .
thm red.equation

definition [code]: "one_step x = Predicate.the (exec_red x)"

lemmas [code_pred_intro] = typeVal[where lev = Low] typeVal[where lev = High]
  typeVar
  typeBinOp1 typeBinOp2[where lev = Low] typeBinOp2[where lev = High] typeBinOp3[where lev = Low]

code_pred (modes: i => i => o => bool as compute_secExprTyping,
  i => i => i => bool as check_secExprTyping) secExprTyping
proof -
  case secExprTyping
  from secExprTyping.prems show thesis
  proof
    fix \<Gamma> V lev assume "x = \<Gamma>" "xa = Val V" "xb = lev"
    from secExprTyping(1-2) this show thesis by (cases lev) auto
  next
    fix \<Gamma> Vn lev
    assume "x = \<Gamma>" "xa = Var Vn" "xb = lev" "\<Gamma> Vn = Some lev"
    from secExprTyping(3) this show thesis by (auto simp add: Predicate.eq_is_eq)
  next
    fix \<Gamma> e1 e2 bop
    assume "x = \<Gamma>" "xa = e1\<guillemotleft>bop\<guillemotright> e2" "xb = Low"
      "\<Gamma> \<turnstile> e1 : Low" "\<Gamma> \<turnstile> e2 : Low"
    from secExprTyping(4) this show thesis by auto
  next
    fix \<Gamma> e1 e2 lev bop
    assume "x = \<Gamma>" "xa = e1\<guillemotleft>bop\<guillemotright> e2" "xb = High"
    "\<Gamma> \<turnstile> e1 : High" "\<Gamma> \<turnstile> e2 : lev"
    from secExprTyping(5-6) this show thesis by (cases lev) (auto)
  next
    fix \<Gamma> e1 e2 lev bop
    assume "x = \<Gamma>" "xa = e1\<guillemotleft>bop\<guillemotright> e2" "xb = High"
    "\<Gamma> \<turnstile> e1 : lev" "\<Gamma> \<turnstile> e2 : High"
    from secExprTyping(6-7) this show thesis by (cases lev) (auto)
  qed
qed

lemmas [code_pred_intro] = typeSkip[where T=Low] typeSkip[where T=High]
  typeAssH[where T = Low] typeAssH[where T=High]
  typeAssL typeSeq typeWhile typeIf typeConvert

code_pred (modes: i => o => i => bool as compute_secComTyping,
  i => i => i => bool as check_secComTyping) secComTyping
proof -
  case secComTyping
  from secComTyping.prems show thesis
  proof
    fix \<Gamma> T assume "x = \<Gamma>" "xa = T" "xb = Skip"
    from secComTyping(1-2) this show thesis by (cases T) auto
  next
    fix \<Gamma> V T e assume "x = \<Gamma>" "xa = T" "xb = V:=e" "\<Gamma> V = Some High"
    from secComTyping(3-4) this show thesis by (cases T) (auto)
  next
    fix \<Gamma> e V
    assume "x = \<Gamma>" "xa = Low" "xb = V:=e" "\<Gamma> \<turnstile> e : Low" "\<Gamma> V = Some Low"
    from secComTyping(5) this show thesis by auto
  next
    fix \<Gamma> T c1 c2
    assume "x = \<Gamma>" "xa = T" "xb = Seq c1 c2" "\<Gamma>,T \<turnstile> c1" "\<Gamma>,T \<turnstile> c2"
    from secComTyping(6) this show thesis by auto
  next
    fix \<Gamma> b T c
    assume "x = \<Gamma>" "xa = T" "xb = while (b) c" "\<Gamma> \<turnstile> b : T" "\<Gamma>,T \<turnstile> c"
    from secComTyping(7) this show thesis by auto
  next
    fix \<Gamma> b T c1 c2
    assume "x = \<Gamma>" "xa = T" "xb = if (b) c1 else c2" "\<Gamma> \<turnstile> b : T" "\<Gamma>,T \<turnstile> c1" "\<Gamma>,T \<turnstile> c2"
    from secComTyping(8) this show thesis by blast
  next
    fix \<Gamma> c
    assume "x = \<Gamma>" "xa = Low" "xb = c" "\<Gamma>,High \<turnstile> c"
    from secComTyping(9) this show thesis by blast
  qed
qed

thm secComTyping.equation

subsection \<open>An example taken from Volpano, Smith, Irvine\<close>

definition "com = if (Var ''x'' \<guillemotleft>Eq\<guillemotright> Val (Intg 1)) (''y'' :=  Val (Intg 1)) else (''y'' := Val (Intg 0))"
definition "Env = map_of [(''x'', High), (''y'', High)]"

values "{T. Env \<turnstile> (Var ''x'' \<guillemotleft>Eq\<guillemotright> Val (Intg 1)): T}"
value "Env, High \<turnstile> com"
value "Env, Low \<turnstile> com"
values 1 "{T. Env, T \<turnstile> com}"

definition "Env' = map_of [(''x'', Low), (''y'', High)]"

value "Env', Low \<turnstile> com"
value "Env', High \<turnstile> com"
values 1 "{T. Env, T \<turnstile> com}"

  
end
