chapter "Quickcheck setup (fishy)"

theory CakeML_Quickcheck
imports
  "generated/CakeML/SemanticPrimitives"
begin

datatype_compat namespace
datatype_compat t
datatype_compat pat
datatype_compat sem_env

context begin

qualified definition handle_0 where
"handle_0 n = Handle n []"

qualified definition handle_1 where
"handle_1 n p1 e1 = Handle n [(p1, e1)]"

qualified definition handle_2 where
"handle_2 n p1 e1 p2 e2 = Handle n [(p1, e1), (p2, e2)]"

qualified definition con_0 where
"con_0 n = Con n []"

qualified definition con_1 where
"con_1 n e1 = Con n [e1]"

qualified definition con_2 where
"con_2 n e1 e2 = Con n [e1, e2]"

qualified definition app_0 where
"app_0 n = App n []"

qualified definition app_1 where
"app_1 n e1 = App n [e1]"

qualified definition app_2 where
"app_2 n e1 e2 = App n [e1, e2]"

qualified definition mat_0 where
"mat_0 n = Mat n []"

qualified definition mat_1 where
"mat_1 n p1 e1 = Mat n [(p1, e1)]"

qualified definition mat_2 where
"mat_2 n p1 e1 p2 e2 = Mat n [(p1, e1), (p2, e2)]"

qualified definition conv_0 where
"conv_0 n = Conv n []"

qualified definition conv_1 where
"conv_1 n v1 = Conv n [v1]"

qualified definition conv_2 where
"conv_2 n v1 v2 = Conv n [v1, v2]"

qualified definition closure_dummy where
"closure_dummy es var = Closure \<lparr> v = Bind [] [], c = Bind [] [] \<rparr> es var"

qualified definition recclosure_dummy where
"recclosure_dummy es var = Recclosure \<lparr> v = Bind [] [], c = Bind [] [] \<rparr> es var"

qualified definition vectorv_0 where
"vectorv_0 = Vectorv []"

qualified definition vectorv_1 where
"vectorv_1 v1 = Vectorv [v1]"

qualified definition vectorv_2 where
"vectorv_2 v1 v2 = Vectorv [v1, v2]"

end

quickcheck_generator exp0
  constructors:
    Raise,
    CakeML_Quickcheck.handle_0,
    CakeML_Quickcheck.handle_1,
    CakeML_Quickcheck.handle_2,
    Lit,
    CakeML_Quickcheck.con_0,
    CakeML_Quickcheck.con_1,
    CakeML_Quickcheck.con_2,
    Var,
    Fun,
    CakeML_Quickcheck.app_0,
    CakeML_Quickcheck.app_1,
    CakeML_Quickcheck.app_2,
    Log,
    If,
    CakeML_Quickcheck.mat_0,
    CakeML_Quickcheck.mat_1,
    CakeML_Quickcheck.mat_2,
    Let,
    Tannot,
    Lannot

quickcheck_generator v
  constructors:
    Litv,
    CakeML_Quickcheck.conv_0,
    CakeML_Quickcheck.conv_1,
    CakeML_Quickcheck.conv_2,
    CakeML_Quickcheck.closure_dummy,
    CakeML_Quickcheck.recclosure_dummy,
    Loc,
    CakeML_Quickcheck.vectorv_0,
    CakeML_Quickcheck.vectorv_1,
    CakeML_Quickcheck.vectorv_2

quickcheck_generator dec
  constructors: Dlet, Dletrec, Dtype, Dtabbrev, Dexn

lemma
  fixes t :: "dec"
  shows "t \<noteq> t"
  quickcheck [expect = counterexample, timeout = 90]
  quickcheck [random, expect = counterexample, timeout = 90]
  oops

lemma
  fixes t :: "v"
  shows "t \<noteq> t"
  quickcheck [expect = counterexample, timeout = 90]
  quickcheck [random, expect = counterexample, timeout = 90]
  oops

end