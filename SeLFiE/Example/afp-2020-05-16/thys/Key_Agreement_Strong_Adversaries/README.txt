Refining Authenticated Key Agreement with Strong Adversaries
README file accompanying Isabelle/HOL sources
================================================================================

authors: 
  Joseph Lallemand <joseph.lallemand@loria.fr>
  Christoph Sprenger <sprenger@inf.ethz.ch>
version: 
  Isabelle/HOL 2016-1


Related publications
--------------------------------------------------------------------------------

This directory contains the Isabelle/HOL 2016-1 sources associated with the
paper

- Joseph Lallemand, Christoph Sprenger, and David Basin
  Refining Authenticated Key Agreement with Strong Adversaries, EuroS&P 2017

This development extends the framework and development described in the 
following two papers:

- Christoph Sprenger and David Basin
  Developing Security Protocols by Refinement, CCS 2010

- Christoph Sprenger and David Basin
  Refining Key Establishment, CSF 2012


Mapping of the model names in the Isabelle/HOL theories to those used in paper
--------------------------------------------------------------------------------

For the sake of the presentation, the paper uses shorter names for the models 
than the Isabelle theories. Here is a mapping of the names (cf. Figure 1 in 
the paper). On the left you find Isabelle/HOL theory name and on the right the  
the corresponding model name used in the paper. A "-" means that the theory is 
not described in the paper. Note that the Isabelle theories contain a separate 
lemma or theorem for each invariant and refinement result.


Level 0	------------------------------- 

  s0g_secrecy	s0			secrecy model
  a0n_agree     -  			non-injective agreement
  a0i_agree		a0i 		injective agreement

Level 1 ------------------------------- 

  dhlvl1		dh1         Authenticated Diffie-Hellman    		            
  sklvl1		dh1n        ... with nonces added
  pfslvl1		-			Key transport with PFS

Level 2	-------------------------------	

  dhlvl2		dh2			Authenticated Diffie-Hellman
  sklvl2 		sk2			SKEME protocol
  pfslvl2		-			Key transport with PFS

Level 3	-------------------------------	

  dhlvl3		dh3			Authenticated Diffie-Hellman
  sklvl3		sk3			SKEME protocol
  pfslvl3		-			Key transport with PFS
  
Note: For each Isabelle theory at Level 3 there is one subscripted with 
"asymmetric" and one with "symmetric" ("asym" and "sym" in the paper). 
There are the implementations of the generic theories listed above with
asymmetric resp. symmetric cryptography.


Unpack and build the complete sources
--------------------------------------------------------------------------------

Unzip and load the theory Import_all.thy into Isabelle/HOL 2016-1.
This theory will load all others.

You may also build the logic images corresponding to the main session by typing

  isabelle build -v -b -d . Compromising

in the Key_Agreement_Strong_Adversaries directory. See also ROOT file and 
comments there regarding other sessions.

