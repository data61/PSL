(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  pfslvl3_symmetric.thy (Isabelle/HOL 2016-1)
  ID:      $Id: pfslvl3_symmetric.thy 133183 2017-01-31 13:55:43Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Level-3 protocol using ephemeral asymmetric keys to achieve forward secrecy.
  Symmetric instantiation.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Key Transport Protocol with PFS (L3, symmetric implementation)\<close>

theory pfslvl3_symmetric
imports pfslvl3 Implem_symmetric
begin

interpretation pfslvl3_asym: pfslvl3 implem_sym
by (unfold_locales)


end
