section \<open>Example Usage of Generated ML Code\<close>
theory Generated_Code_Test
imports Fifo_Push_Relabel_Impl Relabel_To_Front_Impl
begin
  
  ML_val \<open>
    let
      val cnv_edge_list = 
        map (fn (u,v,w) => 
              ( @{code nat_of_integer} u, 
                (@{code nat_of_integer} v, 
                 @{code int_of_integer} w)))

      fun relabel_to_front el s t = 
        @{code relabel_to_front} 
          (cnv_edge_list el) 
          (@{code nat_of_integer} s)
          (@{code nat_of_integer} t)

      fun fifo_push_relabel el s t = 
        @{code fifo_push_relabel} 
          (cnv_edge_list el) 
          (@{code nat_of_integer} s)
          (@{code nat_of_integer} t)

      fun fifo_push_relabel_cvv el s t = 
        @{code fifo_push_relabel_compute_flow_val} 
          (cnv_edge_list el) 
          (@{code nat_of_integer} s)
          (@{code nat_of_integer} t)

      val test_net = [
        (0,1,22),
        (0,2,22),
        (1,3,20),
        (2,3,20),
        (1,4,1),
        (2,4,1),
        (4,3,2)
      ]

      val r1 = relabel_to_front test_net 0 3 ()
      val r2 = fifo_push_relabel test_net 0 3 ()
      val r3 = fifo_push_relabel_cvv test_net 0 3 ()

      val _ = case r1 of NONE => raise ERROR "rtf" | _ => ()
      val _ = case r2 of NONE => raise ERROR "fifo" | _ => ()
      val _ = r3 = SOME (@{code int_of_integer} 42) orelse raise ERROR "fifo-cvv"

    in
      (r1,r2,r3)
    end
  \<close>

end
