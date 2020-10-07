(*  Title:       variants/a_norreqid/A_Norreqid.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
    Author:      Peter Höfner, NICTA
*)

theory %invisible A_Norreqid
imports "../../Aodv_Basic"
begin

chapter "Variant A: Skipping the RREQ ID"

text \<open>
  Explanation~\cite[\textsection 10.1]{FehnkerEtAl:AWN:2013}:
  AODV does not need the route request identifier. This number, in 
  combination with the IP address of the originator, is used to identify 
  every RREQ message in a unique way. This variant shows that the 
  combination of the originator's IP address and its sequence number is just 
  as suited to uniquely determine the route request to which the message 
  belongs. Hence, the route request identifier field is not required. This 
  can then reduce the size of the RREQ message.
\<close>

end %invisible

