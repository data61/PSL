(*  Title:      Jinja/J/Examples.thy

    Author:     Christoph Petzinger
    Copyright   2004 Technische Universitaet Muenchen
*)

section \<open>Example Expressions\<close>

theory Examples imports Expr begin

definition classObject::"J_mb cdecl"
where
  "classObject == (''Object'','''',[],[])"


definition classI :: "J_mb cdecl"
where
  "classI ==
  (''I'', Object,
  [],
  [(''mult'',[Integer,Integer],Integer,[''i'',''j''],
   if (Var ''i'' \<guillemotleft>Eq\<guillemotright> Val(Intg 0)) (Val(Intg 0))
   else Var ''j'' \<guillemotleft>Add\<guillemotright>
       Var this \<bullet> ''mult''([Var ''i'' \<guillemotleft>Add\<guillemotright> Val(Intg (- 1)),Var ''j'']))
  ])"


definition classL :: "J_mb cdecl"
where
  "classL ==
  (''L'', Object,
  [(''F'',Integer), (''N'',Class ''L'')],
  [(''app'',[Class ''L''],Void,[''l''],
   if (Var this \<bullet> ''N''{''L''} \<guillemotleft>Eq\<guillemotright> null)
      (Var this \<bullet> ''N''{''L''} := Var ''l'')
   else (Var this \<bullet> ''N''{''L''}) \<bullet> ''app''([Var ''l'']))
  ])"


definition testExpr_BuildList :: "expr"
where
  "testExpr_BuildList ==
  {''l1'':Class ''L'' := new ''L'';
   Var ''l1''\<bullet>''F''{''L''} := Val(Intg 1);;
  {''l2'':Class ''L'' := new ''L'';
   Var ''l2''\<bullet> ''F''{''L''} := Val(Intg 2);;
  {''l3'':Class ''L'' := new ''L'';
   Var ''l3''\<bullet> ''F''{''L''} := Val(Intg 3);;
  {''l4'':Class ''L'' := new ''L'';
   Var ''l4''\<bullet> ''F''{''L''} := Val(Intg 4);;
   Var ''l1''\<bullet>''app''([Var ''l2'']);;
   Var ''l1''\<bullet>''app''([Var ''l3'']);;
   Var ''l1''\<bullet>''app''([Var ''l4''])}}}}"

definition testExpr1 ::"expr"
where
  "testExpr1 == Val(Intg 5)"
definition testExpr2 ::"expr"
where
  "testExpr2 == BinOp (Val(Intg 5)) Add (Val(Intg 6))"
definition testExpr3 ::"expr"
where
  "testExpr3 == BinOp (Var ''V'') Add (Val(Intg 6))"
definition testExpr4 ::"expr"
where
  "testExpr4 == ''V'' := Val(Intg 6)"
definition testExpr5 ::"expr"
where
  "testExpr5 == new ''Object'';; {''V'':(Class ''C'') := new ''C''; Var ''V''\<bullet>''F''{''C''} := Val(Intg 42)}"
definition testExpr6 ::"expr"
where
  "testExpr6 == {''V'':(Class ''I'') := new ''I''; Var ''V''\<bullet>''mult''([Val(Intg 40),Val(Intg 4)])}"

definition mb_isNull:: "expr"
where
  "mb_isNull == Var this \<bullet> ''test''{''A''} \<guillemotleft>Eq\<guillemotright> null "

definition mb_add:: "expr"
where
  "mb_add == (Var this \<bullet> ''int''{''A''} :=( Var this \<bullet> ''int''{''A''} \<guillemotleft>Add\<guillemotright> Var ''i''));; (Var this \<bullet> ''int''{''A''})"

definition mb_mult_cond:: "expr"  
where
  "mb_mult_cond == (Var ''j'' \<guillemotleft>Eq\<guillemotright> Val (Intg 0)) \<guillemotleft>Eq\<guillemotright> Val (Bool False)"

definition mb_mult_block:: "expr"
where
  "mb_mult_block == ''temp'':=(Var ''temp'' \<guillemotleft>Add\<guillemotright> Var ''i'');;''j'':=(Var ''j'' \<guillemotleft>Add\<guillemotright> Val (Intg (- 1)))"

definition mb_mult:: "expr"
where
  "mb_mult == {''temp'':Integer:=Val (Intg 0); While (mb_mult_cond) mb_mult_block;; ( Var this \<bullet> ''int''{''A''} := Var ''temp'';; Var ''temp'' )}"

definition classA:: "J_mb cdecl"
where
  "classA ==
  (''A'', Object,
  [(''int'',Integer),
   (''test'',Class ''A'') ],
  [(''isNull'',[],Boolean,[], mb_isNull),
   (''add'',[Integer],Integer,[''i''], mb_add),
   (''mult'',[Integer,Integer],Integer,[''i'',''j''], mb_mult) ])"
  

definition testExpr_ClassA:: "expr"
where
  "testExpr_ClassA ==
  {''A1'':Class ''A'':= new ''A''; 
  {''A2'':Class ''A'':= new ''A''; 
  {''testint'':Integer:= Val (Intg 5);
   (Var ''A2''\<bullet> ''int''{''A''} := (Var ''A1''\<bullet> ''add''([Var ''testint''])));;
   (Var ''A2''\<bullet> ''int''{''A''} := (Var ''A1''\<bullet> ''add''([Var ''testint''])));;
   Var ''A2''\<bullet> ''mult''([Var ''A2''\<bullet> ''int''{''A''}, Var ''testint'']) }}}"

end
