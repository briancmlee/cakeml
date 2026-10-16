(*
  Buffer closure, revised (for review, design/35 §7).

  The §7 draft's buf_rel related the inside and outside runs prefix by
  prefix, independently (each outside prefix to SOME inside prefix).  That
  loses the common time a relay needs.  What a relay guarantees holds at
  each instant t of the joint run, per front episode:
   - what U has read inside is a prefix of what the proxy read outside;
   - what the proxy wrote outside is a prefix of what U wrote inside.
  (U reads only what the proxy forwarded, which is what the client sent and
  the proxy read; the proxy writes back only what U wrote.)

  A per-connection safety predicate S read written survives relaying if it
  is closed under more reading and less writing (relay_closed).  Then U's
  safety at every instant gives the system's (relay_safety).  Echo's
  safety predicate is relay-closed (proved).  HTTP's and KV's are claims:
  HTTP's needs that parsing is monotone (more bytes, more complete
  requests, in order); KV's needs that a relay only widens request
  intervals, so precedes outside implies precedes inside.
*)
Theory peerBuffer
Ancestors
  llist ffi EchoSpec HttpSpec KvSpec peerSpecForms peerOpen
Libs
  preamble

(* P: what a connection has read, what it has written; closed under reading
   more and writing less *)
Definition relay_closed_def:
  relay_closed (P : word8 list -> word8 list -> bool) ⇔
    ∀r w r' w'. P r w ∧ r ≼ r' ∧ w' ≼ w ⇒ P r' w'
End

(* The relay relation at one instant, for one front episode: inside (U)
   and outside (the system) streams *)
Definition relays_def:
  relays (r_in, w_in) (r_out, w_out) ⇔ r_in ≼ r_out ∧ w_out ≼ w_in
End

(* MAIN: U's safety at every instant, through a relay at every instant,
   is the system's safety at every instant *)
Theorem relay_safety:
  relay_closed P ∧
  (∀t. P (FST (inside t)) (SND (inside t))) ∧
  (∀t. relays (inside t) (outside t)) ⇒
  ∀t. P (FST (outside t)) (SND (outside t))
Proof
  rw[relay_closed_def] >> first_x_assum irule >>
  qexistsl_tac [‘FST (inside t)’, ‘SND (inside t)’] >>
  first_x_assum (qspec_then ‘t’ mp_tac) >>
  Cases_on ‘inside t’ >> Cases_on ‘outside t’ >> simp[relays_def] >>
  metis_tac[FST, SND]
QED

(* Echo's per-connection safety: written is a prefix of read *)
Theorem echo_relay_closed:
  relay_closed (λr w. w ≼ r)
Proof
  rw[relay_closed_def] >> metis_tac[IS_PREFIX_TRANS]
QED

(* HTTP's per-connection safety (http_safe's body) *)
Definition http_conn_safe_def:
  http_conn_safe files r w ⇔
    ∀rs rest. EVERY valid_brequest rs ∧ r = brequests rs ++ rest ∧ no_full_brequest rest ⇒
              w ≼ bresponses files rs
End

(* CLAIM: HTTP's per-connection safety is relay-closed (parsing is
   monotone) *)
Definition http_relay_closed_claim_def:
  http_relay_closed_claim ⇔ ∀files. relay_closed (http_conn_safe files)
End
