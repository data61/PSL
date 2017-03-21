(*  Title:      DetectMain.ML
    Author:     Yilun He, Data61, CSIRO

    This ML file is not used in the current system
    It provides only one function: Detect.iMain: (textrange) => context => (str*bool) list 
    This function takes the tactic as input, analyse its arguments and
    Check if they are facts from Main.
*)

signature DETECT = 
sig
  val iMain : Method.text_range -> Proof.context -> (string*bool) list
end;
structure Detect:DETECT = 
struct
  fun get_Main ctxt = 
    SOME (Theory.check ctxt ("Main", Position.none))
    handle ERROR _ => NONE;
  
  fun att2list (src:Token.src) =
        let
          val invalidlist = ["metis","smt","mason","rule","drule","erule"]
          val meth_name = Token.name_of_src src|>fst:string;
          val attribs = if List.exists (fn a => a = meth_name) invalidlist then [] else Token.args_of_src src : Token.T list;
          
        in
          attribs
  end;
  fun trimatt (x::(y::ys)) = if y = ":" then trimatt ys else (x::(trimatt (y::ys)))
     |trimatt (x::[]) = [x]
     |trimatt [] = []
  
  fun ansestor_list ctxt= (Theory.ancestors_of (Proof_Context.theory_of ctxt)|> map Context.theory_name)
  
  fun mainlist ance_list ctxt= if List.exists (fn x => x = "Main") ance_list
                        then  (Theory.ancestors_of (Context.get_theory (Proof_Context.theory_of ctxt) "Main") |> map Context.theory_name)
                           else []
  (*Try the function: ML_Context.thm ("foobar") *)
  
  
  fun getTheory ctxt str = SOME (Thm.get_name_hint (Proof_Context.get_thm ctxt str))
          handle ERROR msg => 
            let 
              val tks = String.tokens Char.isSpace msg 
            in 
  
  
              if hd tks= "Expected" then SOME ((String.tokens (fn x => x = #"\"")(nth tks 3))|>hd) 
              else NONE
            end;
  fun getTlist _ [] = []
     |getTlist ctxt (x::xs) = (getTheory ctxt x)::(getTlist ctxt xs)
  
  fun inMain [] _= []
     |inMain (str::sl) mlist= ((str, (List.exists (fn x => x = ((Long_Name.explode str)|>hd)) mlist)) :: (inMain sl mlist))handle Option.Option => inMain sl mlist
  
  fun token2list (x::xs :Token.T list) = (Token.content_of x)::(token2list xs)
      |token2list [] = []
  fun iMain txtrange ctxt= 
      inMain ((getTlist ctxt (trimatt(token2list (att2list (the (Method.get_src (txtrange|>fst)))))))|>filter is_some|>map the) (mainlist (ansestor_list ctxt) ctxt)
    handle Option.Option => []
end;
