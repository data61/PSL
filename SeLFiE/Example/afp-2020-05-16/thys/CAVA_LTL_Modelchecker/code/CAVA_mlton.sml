structure ConvIntN =
  struct
    type 'a t = 'a -> IntInf.int

    val fInt8 = Int8.toLarge
    val fInt16 = Int16.toLarge
    val fInt32 = Int32.toLarge
    val fInt64 = Int64.toLarge
  end 

structure C_SLong_Conv = C_SLong_ChooseIntN(ConvIntN);

structure CAVA_Support = struct
  val isMLton = true
  
  local
    (* this requires rusage.c to be added to the compile phase *)
    val max_rss' = _import "get_max_rss" public: unit -> C_SLong.t;
  in
    val max_rss = C_SLong_Conv.f o max_rss'
  end

  val objSize = MLton.size
end
