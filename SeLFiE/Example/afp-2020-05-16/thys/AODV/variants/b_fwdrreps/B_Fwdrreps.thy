(*  Title:       variants/b_fwdrreps/B_Fwdrreps.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
    Author:      Peter Höfner, NICTA
*)

theory %invisible B_Fwdrreps
imports "../../Aodv_Basic"
begin

chapter "Variant B: Forwarding the Route Reply"

text \<open>
  Explanation~\cite[\textsection 10.2]{FehnkerEtAl:AWN:2013}:
  In AODV's route discovery process, a RREP message from the destination 
  node is unicast back along a route towards the originator of the RREQ 
  message. Every intermediate node on the selected route will process the 
  RREP message and, in most cases, forward it towards the originator node. 
  However, there is a possibility that the RREP message is discarded at an 
  intermediate node, which results in the originator node not receiving a 
  reply. The discarding of the RREP message is due to the RFC specification 
  of AODV~\cite{RFC3561} stating that an intermediate node only forwards the 
  RREP message if it is not the originator node and it has created or 
  updated a routing table entry to the destination node described in the 
  RREP message. The latter requirement means that if a valid routing table 
  entry to the destination node already exists, and is not updated when 
  processing the RREP message, then the intermediate node will not forward 
  the message. A solution to this problem is to require intermediate nodes 
  to forward all RREP messages that they receive.
\<close>

end %invisible

