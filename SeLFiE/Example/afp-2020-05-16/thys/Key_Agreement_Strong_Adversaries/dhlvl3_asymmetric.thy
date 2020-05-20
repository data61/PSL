(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  dhlvl3_asymmetric.thy (Isabelle/HOL 2016-1)
  ID:      $Id: dhlvl3_asymmetric.thy 133183 2017-01-31 13:55:43Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Level-3 Diffie-Hellman protocol; asymmetric instantiation of version with 
  generic channel implementation. This corresponds to a standard signature-
  authenticated Diffie-Hellman protocol. 

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Authenticated Diffie-Hellman Protocol (L3, asymmetric)\<close>

theory dhlvl3_asymmetric
imports dhlvl3 Implem_asymmetric
begin

interpretation dhlvl3_asym: dhlvl3 implem_asym
by (unfold_locales)

end
