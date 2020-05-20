(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  sklvl3_asymmetric.thy (Isabelle/HOL 2016-1)
  ID:      $Id: sklvl3_asymmetric.thy 133183 2017-01-31 13:55:43Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Level-3 SKEME/IKEv1 protocol; asymmetric instantiation of version with generic
  channel implementation. Refines model sklvl2 based on channel assumptions.
  This corresponds to the basic mode of the SKEME protocol and to the public-key 
  variant of the IKEv1 protocol in agressive mode.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>SKEME Protocol (L3 with asymmetric implementation)\<close>

theory sklvl3_asymmetric
imports sklvl3 Implem_asymmetric
begin

interpretation sklvl3_asym: sklvl3 implem_asym
by (unfold_locales)

end
