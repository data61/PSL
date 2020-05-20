(*  Title:      JinjaThreads/Examples/BufferExample.thy
    Author:     Andreas Lochbihler
*)

section \<open>Buffer example\<close>

theory BufferExample imports 
  "../Execute/Code_Generation"
begin

definition ThreadC :: "addr J_mb cdecl"
where 
  "ThreadC = 
  (Thread, Object, [], 
    [(run, [], Void, \<lfloor>([], unit)\<rfloor>),
     (start, [], Void, Native),
     (join, [], Void, Native),
     (interrupt, [], Void, Native),
     (isInterrupted, [], Boolean, Native)])"

definition IntegerC :: "addr J_mb cdecl"
where "IntegerC = (STR ''Integer'', Object, [(STR ''value'', Integer, \<lparr>volatile=False\<rparr>)], [])"

definition Buffer :: cname
where "Buffer = STR ''Buffer''"

definition BufferC :: "addr J_mb cdecl"
where
  "BufferC =
   (Buffer, Object,
    [(STR ''buffer'', Class Object\<lfloor>\<rceil>, \<lparr>volatile=False\<rparr>),
     (STR ''front'', Integer, \<lparr>volatile=False\<rparr>),
     (STR ''back'', Integer, \<lparr>volatile=False\<rparr>),
     (STR ''size'', Integer, \<lparr>volatile=False\<rparr>)],
    [(STR ''constructor'', [Integer], Void, \<lfloor>([STR ''size''],
      (STR ''buffer'' := newA (Class Object)\<lfloor>Var (STR ''size'')\<rceil>);;
      (STR ''front'' := Val (Intg 0));;
      (STR ''back'' := Val (Intg (- 1)));;
      (Var this\<bullet>(STR ''size''){STR ''''} := Val (Intg 0)))\<rfloor>),
     (STR ''empty'', [], Boolean, \<lfloor>([], sync(Var this) (Var (STR ''size'') \<guillemotleft>Eq\<guillemotright> Val (Intg 0)))\<rfloor>),
     (STR ''full'', [], Boolean, \<lfloor>([],
      sync(Var this) (Var (STR ''size'') \<guillemotleft>Eq\<guillemotright> ((Var (STR ''buffer''))\<bullet>length)))\<rfloor>),
     (STR ''get'', [], Class Object, \<lfloor>([],
      sync(Var this) (
        (while (Var this\<bullet>(STR ''empty'')([])) 
          (try (Var this\<bullet>wait([])) catch(InterruptedException (STR ''e'')) unit));;
        (STR ''size'' := (Var (STR ''size'') \<guillemotleft>Subtract\<guillemotright> Val (Intg 1)));;
        {(STR ''result''):Class Object=None; 
          ((STR ''result'') := ((Var (STR ''buffer''))\<lfloor>Var (STR ''front'')\<rceil>));;
          (STR ''front'' := (Var (STR ''front'') \<guillemotleft>Add\<guillemotright> Val (Intg 1)));;
          (if ((Var (STR ''front'')) \<guillemotleft>Eq\<guillemotright> ((Var (STR ''buffer''))\<bullet>length))
             (STR ''front'' := Val (Intg 0))
           else unit);;
          (Var this\<bullet>notifyAll([]));;
          Var (STR ''result'')
        }
      ))\<rfloor>),
     (STR ''put'', [Class Object], Void, \<lfloor>([STR ''o''],
      sync(Var this) (
        (while (Var this\<bullet>STR ''full''([]))
          (try (Var this\<bullet>wait([])) catch(InterruptedException STR ''e'') unit));;
        (STR ''back'' := (Var (STR ''back'') \<guillemotleft>Add\<guillemotright> Val (Intg 1)));;
        (if (Var (STR ''back'') \<guillemotleft>Eq\<guillemotright> ((Var (STR ''buffer''))\<bullet>length))
           (STR ''back'' := Val (Intg 0))
         else unit);;
        (AAss (Var (STR ''buffer'')) (Var (STR ''back'')) (Var (STR ''o'')));;
        (STR ''size'' := ((Var (STR ''size'')) \<guillemotleft>Add\<guillemotright> Val (Intg 1)));;
        (Var this\<bullet>notifyAll([]))
      ))\<rfloor>)
    ])"

definition Producer :: cname
where "Producer = STR ''Producer''"

definition ProducerC :: "int \<Rightarrow> addr J_mb cdecl"
where
  "ProducerC n =
   (Producer, Thread, [(STR ''buffer'', Class Buffer, \<lparr>volatile=False\<rparr>)],
    [(run, [], Void, \<lfloor>([],
     {STR ''i'':Integer=\<lfloor>Intg 0\<rfloor>;
        while (Var (STR ''i'') \<guillemotleft>NotEq\<guillemotright> Val (Intg (word_of_int n))) (
          (Var (STR ''buffer''))\<bullet>STR ''put''([{STR ''temp'':Class (STR ''Integer'')=None; (STR ''temp'' := new (STR ''Integer'');; ((FAss (Var (STR ''temp'')) (STR ''value'') (STR '''') (Var (STR ''i'')));; Var (STR ''temp'')))} ]);;
          STR ''i'' := (Var (STR ''i'') \<guillemotleft>Add\<guillemotright> (Val (Intg 1))))
     })\<rfloor>)])"

definition Consumer :: cname
where "Consumer = STR ''Consumer''"

definition ConsumerC :: "int \<Rightarrow> addr J_mb cdecl"
where
  "ConsumerC n =
  (Consumer, Thread, [(STR ''buffer'', Class Buffer, \<lparr>volatile=False\<rparr>)],
   [(run, [], Void, \<lfloor>([],
    {STR ''i'':Integer=\<lfloor>Intg 0\<rfloor>;
      while (Var (STR ''i'') \<guillemotleft>NotEq\<guillemotright> Val (Intg (word_of_int n))) (
        {STR ''o'':Class Object=None; 
          Seq (STR ''o'' := ((Var (STR ''buffer''))\<bullet>STR ''get''([])))
              (STR ''i'' := (Var (STR ''i'') \<guillemotleft>Add\<guillemotright> Val (Intg 1)))})
    })\<rfloor>)])"

definition String :: cname
where "String = STR ''String''"

definition StringC :: "addr J_mb cdecl"
where
  "StringC = (String, Object, [], [])"

definition Test :: cname
where "Test = STR ''Test''"

definition TestC :: "addr J_mb cdecl"
where
  "TestC =
  (Test, Object, [],
   [(STR ''main'', [Class String\<lfloor>\<rceil>], Void, \<lfloor>([STR ''args''], 
    {STR ''b'':Class Buffer=None; (STR ''b'' := new Buffer);;
      (Var (STR ''b'')\<bullet>STR ''constructor''([Val (Intg 10)]));;
      {STR ''p'':Class Producer=None; STR ''p'' := new Producer;;
        {STR ''c'':Class Consumer=None; 
           (STR ''c'' := new Consumer);;
           (Var (STR ''c'')\<bullet>STR ''buffer''{STR ''''} := Var (STR ''b''));;
           (Var (STR ''p'')\<bullet>STR ''buffer''{STR ''''} := Var (STR ''b''));;
           (Var (STR ''c'')\<bullet>Type.start([]));;(Var (STR ''p'')\<bullet>Type.start([]))
        }
      }
    })\<rfloor>)])"
    
definition BufferExample
where
  "BufferExample n = Program (SystemClasses @ [ThreadC, StringC, IntegerC, BufferC, ProducerC n, ConsumerC n, TestC])"

definition BufferExample_annotated
where
  "BufferExample_annotated n = annotate_prog_code (BufferExample n)"

lemmas [code_unfold] =
  IntegerC_def Buffer_def Producer_def Consumer_def Test_def
  String_def

lemma "wf_J_prog (BufferExample_annotated 10)"
by eval

definition main where "main = STR ''main''"
definition five :: int where "five = 5"

ML_val \<open>
  val program = @{code BufferExample_annotated} @{code "five"};
  val compiled = @{code J2JVM} program;

  val run = 
    @{code exec_J_rr}
      @{code "1 :: nat"}
      program
      @{code Test}
      @{code main}
      [ @{code Null}];
  val _ = @{code terminal} run;

  val jvm_run = 
    @{code exec_JVM_rr} 
      @{code "1 :: nat"}
      compiled
      @{code Test}
      @{code main}
      [ @{code Null}];
  val _ = @{code terminal} run;
\<close>

end
