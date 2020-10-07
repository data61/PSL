(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  dhlvl3_symmetric.thy (Isabelle/HOL 2016-1)
  ID:      $Id: dhlvl3_symmetric.thy 133183 2017-01-31 13:55:43Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Level-3 Diffie-Hellman protocol; symmetric instantiation of 
  version with generic channel implementation.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Authenticated Diffie-Hellman Protocol (L3, symmetric)\<close>

theory dhlvl3_symmetric
imports dhlvl3 Implem_symmetric
begin

interpretation dhlvl3_sym: dhlvl3 implem_sym
by (unfold_locales)

end
