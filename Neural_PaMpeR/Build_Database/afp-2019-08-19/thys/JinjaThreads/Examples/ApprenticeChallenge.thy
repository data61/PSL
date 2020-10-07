(*  Title:      JinjaThreads/Examples/AppenticeChallenge.thy
    Author:     Andreas Lochbihler
*)

chapter \<open>Examples\<close>

section \<open>Apprentice challenge\<close>

theory ApprenticeChallenge 
imports
  "../Execute/Code_Generation"
begin

text \<open>This theory implements the apprentice challenge by Porter and Moore \cite{MoorePorter2002TOPLAS}.\<close>

definition ThreadC :: "addr J_mb cdecl"
where 
  "ThreadC = 
  (Thread, Object, [], 
    [(run, [], Void, \<lfloor>([], unit)\<rfloor>),
     (start, [], Void, Native),
     (join, [], Void, Native),
     (interrupt, [], Void, Native),
     (isInterrupted, [], Boolean, Native)])"

definition Container :: cname
where "Container = STR ''Container''"

definition ContainerC :: "addr J_mb cdecl"
where "ContainerC = (Container, Object, [(STR ''counter'', Integer, \<lparr>volatile=False\<rparr>)], [])"

definition String :: cname
where "String = STR ''String''"

definition StringC :: "addr J_mb cdecl"
where
  "StringC = (String, Object, [], [])"

definition Job :: cname
where "Job = STR ''Job''"

definition JobC :: "addr J_mb cdecl"
where
  "JobC =
  (Job, Thread, [(STR ''objref'', Class Container, \<lparr>volatile=False\<rparr>)],
   [(STR ''incr'', [], Class Job, \<lfloor>([],
     sync(Var (STR ''objref''))
         ((Var (STR ''objref''))\<bullet>STR ''counter''{STR ''''} := ((Var (STR ''objref''))\<bullet>STR ''counter''{STR ''''} \<guillemotleft>Add\<guillemotright> Val (Intg 1)));;
     Var this)\<rfloor>),
    (STR ''setref'', [Class Container], Void, \<lfloor>([STR ''o''],
     LAss (STR ''objref'') (Var (STR ''o'')))\<rfloor>),
    (run, [], Void, \<lfloor>([],
     while (true) (Var this\<bullet>STR ''incr''([])))\<rfloor>)
    ])"

definition Apprentice :: cname
where "Apprentice = STR ''Apprentice''"

definition ApprenticeC :: "addr J_mb cdecl"
where
  "ApprenticeC =
  (Apprentice, Object, [],
   [(STR ''main'', [Class String\<lfloor>\<rceil>], Void, \<lfloor>([STR ''args''],
    {STR ''container'':Class Container=None;
       (STR ''container'' := new Container);;
       (while (true) 
          {STR ''job'':Class Job=None;
              (STR ''job'' := new Job);;
              (Var (STR ''job'')\<bullet>STR ''setref''([Var (STR ''container'')]));;
              (Var (STR ''job'')\<bullet>Type.start([]))
          }
       )
    })\<rfloor>)])"

definition ApprenticeChallenge
where
  "ApprenticeChallenge = Program (SystemClasses @ [StringC, ThreadC, ContainerC, JobC, ApprenticeC])"

definition ApprenticeChallenge_annotated
where "ApprenticeChallenge_annotated = annotate_prog_code ApprenticeChallenge"

lemma "wf_J_prog ApprenticeChallenge_annotated"
by eval

lemmas [code_unfold] = 
  Container_def Job_def String_def Apprentice_def

definition main :: "String.literal" where "main = STR ''main''"

ML_val \<open>
  val _ = tracing "started";
  val program = @{code ApprenticeChallenge_annotated};
  val _ = tracing "prg";
  val compiled = @{code J2JVM} program;
  val _ = tracing "compiled";

  @{code exec_J_rr}
    @{code "1 :: nat"}
    program
    @{code Apprentice}
    @{code main}
    [ @{code Null}];

  val _ = tracing "J_rr";
  @{code exec_JVM_rr} 
    @{code "1 :: nat"}
    compiled
    @{code Apprentice}
    @{code main}
    [ @{code Null}];
  val _ = tracing "JVM_rr";
\<close>

end
