(*  Title:       variants/d_fwdrreqs/D_Fwdrreqs.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
    Author:      Peter Höfner, NICTA
*)

theory %invisible D_Fwdrreqs
imports "../../Aodv_Basic"
begin

chapter "Variant D: Forwarding the Route Request"

text \<open>
  Explanation~\cite[\textsection 10.5]{FehnkerEtAl:AWN:2013}:
  In AODV's route discovery process, a destination node (or an intermediate 
  node with an active route to the destination) will generate a RREP message 
  in response to a received RREQ message. The RREQ message is then dropped 
  and not forwarded. This termination of the route discovery process at the 
  destination can lead to other nodes inadvertently creating non-optimal 
  routes to the source node~\cite{MK10}.
  A possible modification to solve this problem is to allow the destination 
  node to continue to forward the RREQ message. A route request is only 
  stopped if it has been handled before. The forwarded RREQ message from the 
  destination node needs to be modified to include a Boolean flag 
  \verb+handled+ that indicates a RREP message has already been generated 
  and sent in response to the former message. In case the flag is set to 
  true, it prevents other nodes (with valid route to the destination) from 
  sending a RREP message in response to their reception of the forwarded 
  RREQ message.
\<close>

end %invisible

