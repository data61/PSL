(* 
Title:       Kernel_programming_language.thy
Author:      John Wickerson
Date:        2 April 2014
Description: 
  This theory file accompanies the article "The Design and 
  Implementation of a Verification Technique for GPU Kernels" 
  by Adam Betts, Nathan Chong, Alastair F. Donaldson, Jeroen
  Ketema, Shaz Qadeer, Paul Thomson and John Wickerson. It
  formalises all of the definitions provided in Sections 3
  and 4. 
*)

theory Kernel_programming_language imports
(* 1. SOME GENERAL PURPOSE STUFF *)
  Misc
(* 2. SYNTAX OF KPL *)
  KPL_syntax
(* 3. WELL-FORMEDNESS OF KPL KERNELS *)
  KPL_wellformedness
(* 4. THREAD, GROUP, AND KERNEL STATES *)
  KPL_state
(* 5. EXECUTION RULES FOR THREADS *)
  KPL_execution_thread
(* 6. EXECUTION RULES FOR GROUPS *)
  KPL_execution_group
(* 7. EXECUTION RULES FOR KERNELS *)
  KPL_execution_kernel
begin 

end
