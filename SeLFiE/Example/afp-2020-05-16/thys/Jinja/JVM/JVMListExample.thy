(*  Title:      Jinja/JVM/JVMListExample.thy
    Author:     Stefan Berghofer, Gerwin Klein
*)

section \<open>Example for generating executable code from JVM semantics \label{sec:JVMListExample}\<close>

theory JVMListExample
imports
  "../Common/SystemClasses"
  JVMExec
  "HOL-Library.Code_Target_Numeral"
begin

definition list_name :: string
where
  "list_name == ''list''"

definition test_name :: string
where
  "test_name == ''test''"

definition val_name :: string
where
  "val_name == ''val''"

definition next_name :: string
where
  "next_name == ''next''"

definition append_name :: string
where
  "append_name == ''append''"

definition makelist_name :: string
where
  "makelist_name == ''makelist''"

definition append_ins :: bytecode
where
  "append_ins == 
       [Load 0,
        Getfield next_name list_name,
        Load 0,
        Getfield next_name list_name,
        Push Null,
        CmpEq,
        IfFalse 7,
        Pop,
        Load 0,
        Load 1,
        Putfield next_name list_name,
        Push Unit,
        Return,
        Load 1,       
        Invoke append_name 1,
        Return]"

definition list_class :: "jvm_method class"
where
  "list_class ==
    (Object,
     [(val_name, Integer), (next_name, Class list_name)],
     [(append_name, [Class list_name], Void,
        (3, 0, append_ins, [(1, 2, NullPointer, 7, 0)]))])"

definition make_list_ins :: bytecode
where
  "make_list_ins ==
       [New list_name,
        Store 0,
        Load 0,
        Push (Intg 1),
        Putfield val_name list_name,
        New list_name,
        Store 1,
        Load 1,
        Push (Intg 2),
        Putfield val_name list_name,
        New list_name,
        Store 2,
        Load 2,
        Push (Intg 3),
        Putfield val_name list_name,
        Load 0,
        Load 1,
        Invoke append_name 1,
        Pop,
        Load 0,
        Load 2,
        Invoke append_name 1,
        Return]"

definition test_class :: "jvm_method class"
where
  "test_class ==
    (Object, [],
     [(makelist_name, [], Void, (3, 2, make_list_ins, []))])"

definition E :: jvm_prog
where
  "E == SystemClasses @ [(list_name, list_class), (test_name, test_class)]"

definition undefined_cname :: cname 
  where [code del]: "undefined_cname = undefined"
declare undefined_cname_def[symmetric, code_unfold]
code_printing constant undefined_cname \<rightharpoonup> (SML) "object"

definition undefined_val :: val
  where [code del]: "undefined_val = undefined"
declare undefined_val_def[symmetric, code_unfold]
code_printing constant undefined_val \<rightharpoonup> (SML) "Unit"

lemmas [code_unfold] = SystemClasses_def [unfolded ObjectC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def]

definition "test = exec (E, start_state E test_name makelist_name)"

ML_val \<open>
  @{code test};
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);

  val SOME (_, (h, _)) = it;
  if snd (@{code the} (h (@{code nat_of_integer} 3))) (@{code val_name}, @{code list_name}) =
    SOME (@{code Intg} (@{code int_of_integer} 1)) then () else error "wrong result";
  if snd (@{code the} (h (@{code nat_of_integer} 3))) (@{code next_name}, @{code list_name}) =
    SOME (@{code Addr} (@{code nat_of_integer} 4)) then () else error "wrong result";
  if snd (@{code the} (h (@{code nat_of_integer} 4))) (@{code val_name}, @{code list_name}) =
    SOME (@{code Intg} (@{code int_of_integer} 2)) then () else error "wrong result";
  if snd (@{code the} (h (@{code nat_of_integer} 4))) (@{code next_name}, @{code list_name}) =
    SOME (@{code Addr} (@{code nat_of_integer} 5)) then () else error "wrong result";
  if snd (@{code the} (h (@{code nat_of_integer} 5))) (@{code val_name}, @{code list_name}) =
    SOME (@{code Intg} (@{code int_of_integer} 3)) then () else error "wrong result";
  if snd (@{code the} (h (@{code nat_of_integer} 5))) (@{code next_name}, @{code list_name}) =
    SOME @{code Null} then () else error "wrong result";
\<close>

end
