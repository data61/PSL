theory PromelaStatistics
imports 
  CAVA_Base.CAVA_Base
begin

code_printing
  code_module PromelaStatistics \<rightharpoonup> (SML) \<open>
    structure PromelaStatistics = struct
      val active = Unsynchronized.ref false
      val parseTime = Unsynchronized.ref Time.zeroTime
      val time = Unsynchronized.ref Time.zeroTime

      fun is_active () = !active

      fun start () = (
            active := true; 
            if !parseTime = Time.zeroTime then () else parseTime := Time.- (Time.now (), !parseTime);
            time := Time.now ())
      fun start_parse () = (active := true; parseTime := Time.now())
      fun stop_timer () = (time := Time.- (Time.now (), !time))

      fun to_string () = let
        val t = Time.toMilliseconds (!time)
        val pt = Time.toMilliseconds (!parseTime)
      in
        (if pt = 0 then "" else 
        "Parsing time : " ^ IntInf.toString pt ^ "ms\n")
      ^ "Building time: " ^ IntInf.toString t ^ "ms\n"
      end
        
      val _ = Statistics.register_stat ("Promela",is_active,to_string)
    end
\<close>
code_reserved SML PromelaStatistics

ML_val \<open>@{code hd}\<close>

consts 
  start :: "unit \<Rightarrow> unit"
  start_parse :: "unit \<Rightarrow> unit"
  stop_timer :: "unit \<Rightarrow> unit"

code_printing
  constant start \<rightharpoonup> (SML) "PromelaStatistics.start"
| constant start_parse \<rightharpoonup> (SML) "PromelaStatistics.start'_parse"
| constant stop_timer \<rightharpoonup> (SML) "PromelaStatistics.stop'_timer"

hide_const (open) start start_parse stop_timer

end
