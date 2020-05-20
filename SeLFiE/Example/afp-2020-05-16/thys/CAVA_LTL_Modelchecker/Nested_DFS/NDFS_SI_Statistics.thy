theory NDFS_SI_Statistics
imports 
  CAVA_Base.CAVA_Base
begin

code_printing
  code_module NDFS_SI_Statistics \<rightharpoonup> (SML) \<open>
    structure NDFS_SI_Statistics = struct
      val active = Unsynchronized.ref false
      val cur_limit = Unsynchronized.ref 1000000
      val blue_vis = Unsynchronized.ref 0
      val blue_match = Unsynchronized.ref 0
      val red_vis = Unsynchronized.ref 0
      val time = Unsynchronized.ref Time.zeroTime

      fun is_active () = !active
      fun vis_blue () = (
            if !cur_limit < !blue_vis then (
              TextIO.print("*** " ^ IntInf.toString((!cur_limit) div 1000000) ^ "e+06 states\n");
              cur_limit := !cur_limit + 1000000)
            else ();
            blue_vis := !blue_vis + 1)
      fun match_blue () = blue_match := !blue_match + 1
      fun vis_red () = red_vis := !red_vis + 1

      fun start () = (active := true; time := Time.now ())
      fun stop () = (time := Time.- (Time.now (), !time))

      fun to_string () = let
        val t = Time.toReal (!time)
        val states_per_s = real (!blue_vis) / t
        val realStr = Real.fmt (StringCvt.FIX (SOME 2))

      in
        "Required time  : " ^ realStr t ^ "s\n"
      ^ "States per sec : " ^ realStr states_per_s ^ "\n"
      ^ "Blue states (v): " ^ IntInf.toString (!blue_vis) ^ "\n"
      ^ "Blue states (m): " ^ IntInf.toString (!blue_match) ^ "\n"
      ^ "Blue edges     : " ^ IntInf.toString (!blue_match + !blue_vis) ^ "\n"
      ^ "Red states     : " ^ IntInf.toString (!red_vis) ^ "\n"
      end
        
      val _ = Statistics.register_stat ("NDFS",is_active,to_string)
    end
\<close>
code_reserved SML NDFS_SI_Statistics

ML_val \<open>@{code hd}\<close>

consts 
  vis_red :: "unit \<Rightarrow> unit"
  vis_blue :: "unit \<Rightarrow> unit"
  match_blue :: "unit \<Rightarrow> unit"
  start :: "unit \<Rightarrow> unit"
  stop :: "unit \<Rightarrow> unit"

code_printing
  constant vis_red \<rightharpoonup> (SML) "NDFS'_SI'_Statistics.vis'_red"
| constant vis_blue \<rightharpoonup> (SML) "NDFS'_SI'_Statistics.vis'_blue"
| constant match_blue \<rightharpoonup> (SML) "NDFS'_SI'_Statistics.match'_blue"
| constant start \<rightharpoonup> (SML) "NDFS'_SI'_Statistics.start"
| constant stop \<rightharpoonup> (SML) "NDFS'_SI'_Statistics.stop"

lemma [autoref_rules]: 
  "(vis_red,vis_red) \<in> unit_rel \<rightarrow> unit_rel"
  "(vis_blue,vis_blue) \<in> unit_rel \<rightarrow> unit_rel"
  "(match_blue,match_blue) \<in> unit_rel \<rightarrow> unit_rel"
  "(start,start) \<in> unit_rel \<rightarrow> unit_rel"
  "(stop,stop) \<in> unit_rel \<rightarrow> unit_rel"
  by auto

abbreviation "vis_red_nres \<equiv> RETURN (vis_red ())"
abbreviation "vis_blue_nres \<equiv> RETURN (vis_blue ())"
abbreviation "match_blue_nres \<equiv> RETURN (match_blue ())"
abbreviation "start_nres \<equiv> RETURN (start ())"
abbreviation "stop_nres \<equiv> RETURN (stop ())"

hide_const (open) vis_red vis_blue match_blue start stop
hide_const (open) vis_red_nres vis_blue_nres match_blue_nres start_nres stop_nres

export_code List.append checking SML (* Verification that code-module did 
  not mess up something. *)

end
