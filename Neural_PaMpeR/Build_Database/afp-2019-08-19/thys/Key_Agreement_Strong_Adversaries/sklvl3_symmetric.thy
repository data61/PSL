(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  sklvl3_symmetric.thy (Isabelle/HOL 2016-1)
  ID:      $Id: sklvl3_symmetric.thy 133183 2017-01-31 13:55:43Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Level-3 SKEME/IKEv1 protocol; symmetric instantiation of version with generic
  channel implementation. Refines model sklvl2 based on channel assumptions.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>SKEME Protocol (L3 with symmetric implementation)\<close>

theory sklvl3_symmetric
imports sklvl3 Implem_symmetric
begin

interpretation sklvl3_sym: sklvl3 implem_sym
by (unfold_locales)

end
