(*
  Two programs connected by the network (for the user's review;
  statements only, proofs after review).

  A JOINT RUN of a client P1 and a server P2 (listening on address a):
  each program runs (diverges) against an endpoint world, and m interleaves
  their traces; the WIRING says that each world's environment behaves as
  the other program did, prefix by prefix of m:
   - P1's j-th connect to a is P2's j-th accepted channel (and is
     accepted);
   - delivery is causal and unconditional: what P2's world says the peer
     of channel j sent is a prefix of what P1 had sent in its episode j,
     and eventually all of it (and symmetrically);
   - drains are reads: P1's world drains channel j as P2 reads episode j
     (and symmetrically);
   - EOF: a world reports the peer's EOF only after the other program shut
     the episode down (shutdown or close), and eventually does.
  Composition is over the traces WITH their causal order (m, prefix by
  prefix): this avoids the Brock–Ackerman anomaly, which comes from
  composing nondeterministic input/output relations.

  PROJECTION (claim): the worlds of a fair joint run can be chosen to
  satisfy the rely (whatever the program had done, the environment's
  arrivals make sense), and a peer that is the other program keeps
  reading exactly when that program does.
  COMPOSITION (claim, an instance): the toy HTTP client and an HTTP server
  meeting their endpoint specs, joined, give the client the response.

  Not yet: n-ary OPEN systems (a set of processes open to an environment
  that plays the external addresses, whose external view is an io_event
  trace, so the headline predicates apply to it unamended), and the
  buffer-closure lemma (a relay only delays writes and advances reads, so
  proxy ‖ U meets U's spec).  Design note 35 §6.
*)
Theory endpointCompose
Ancestors
  llist ffi semantics ffiSpikeSocketFFI EchoSpec EchoSpec2 HttpSpec
  HttpSpecBodies endpointWorld endpointFair endpointSpecForms
  endpointServers endpointClients
Libs
  preamble

(* The events of program k in a finite interleaving *)
Definition side_def:
  side k (ms : (num # io_event) list) = MAP SND (FILTER (λx. FST x = k) ms)
End

(* The trace of program k in the interleaving *)
Definition proj_def:
  proj k (m : (num # io_event) llist) = LMAP SND (LFILTER (λx. FST x = k) m)
End

(* The read events of episode j *)
Definition nreads_ep_def:
  nreads_ep j evs =
    LENGTH (FILTER (λev. case ev of IO_event (ExtCall n) _ _ => n = «sock_read» | _ => F)
                   (ch_events j 0 [] evs))
End

(* One direction of a link: what program k sent in its episode j reaches
   the peer of channel c in program k''s world w' (episode j' there) *)
Definition flows_def:
  flows k j k' w' c m ⇔
    ∀ms. LPREFIX (fromList ms) m ⇒
         (* causal *)
         peer_sent_at w' (side k' ms) c ≼ ch_sent j (side k ms) ∧
         (ch_shut j (side k ms) ∨
          ¬(c < LENGTH (ep_replay w' (side k' ms)).chans ∧
            (EL c (ep_replay w' (side k' ms)).chans).peer_eof)) ∧
         (* unconditional eventual delivery, of bytes and of EOF *)
         (∃ms'. LPREFIX (fromList ms') m ∧
                ch_sent j (side k ms) ≼ peer_sent_at w' (side k' ms') c ∧
                (ch_shut j (side k ms) ⇒
                 c < LENGTH (ep_replay w' (side k' ms')).chans ∧
                 (EL c (ep_replay w' (side k' ms')).chans).peer_eof))
End

(* Drains are reads: program k''s reads of its episode j' drain channel c
   of program k's world w *)
Definition drains_are_reads_def:
  drains_are_reads k w c k' j' m ⇔
    ∀ms. LPREFIX (fromList ms) m ⇒
         peer_reads_at w (side k ms) c ≤ nreads_ep j' (side k' ms) ∧
         ∃ms'. LPREFIX (fromList ms') m ∧ nreads_ep j' (side k' ms) ≤ peer_reads_at w (side k ms') c
End

(* The wiring of P1 (in w1) to P2 (in w2): P1's episode j, connected to a,
   is channel c1 of w1; P2's episode j, accepted, is channel c2 of w2 *)
Definition wired_def:
  wired a w1 w2 m ⇔
    ∀ms j. LPREFIX (fromList ms) m ∧ j < LENGTH (opened_fds (side 2 ms)) ⇒
      ep_accepted (side 2 ms) j ∧ ep_connected_to (side 1 ms) j a ∧
      ∃c1 c2. ep_chan w1 (side 1 ms) j = SOME c1 ∧ ep_chan w2 (side 2 ms) j = SOME c2 ∧
              ch_reaches w1 (proj 1 m) c1 Up ∧
              flows 1 j 2 w2 c2 m ∧ flows 2 j 1 w1 c1 m ∧
              drains_are_reads 1 w1 c1 2 j m ∧ drains_are_reads 2 w2 c2 1 j m
End

(* A joint run of P1 and P2, in the worlds w1 and w2 *)
Definition joint_run_def:
  joint_run P1 P2 lfd a w1 w2 m ⇔
    ep_client_world w1 ∧ ep_server_world all_calls lfd a w2 ∧
    semantics_prog (init_state (ep_ffi w1)) init_env P1 (Diverge (proj 1 m)) ∧
    semantics_prog (init_state (ep_ffi w2)) init_env P2 (Diverge (proj 2 m)) ∧
    wired a w1 w2 m
End

(* CLAIM (projection): the worlds of a joint run can be chosen to satisfy
   the rely; then the peer of a linked channel keeps reading exactly when
   the other program keeps reading its episode *)
Definition projection_def:
  projection ⇔
    ∀P1 P2 lfd a w1 w2 m.
      joint_run P1 P2 lfd a w1 w2 m ⇒
      ∃w1' w2'. joint_run P1 P2 lfd a w1' w2' m ∧ ep_rely w1' ∧ ep_rely w2'
End

(* CLAIM (composition, an instance): the toy HTTP client of request r and
   an HTTP server meeting the endpoint HttpSpecBodies, joined, give the
   client the whole response *)
Definition client_server_compose_def:
  client_server_compose ⇔
    ∀P1 P2 lfd a r files w1 w2 m.
      http_client_spec a r P1 ∧ ep_http_spec all_calls lfd a files P2 ∧
      joint_run P1 P2 lfd a w1 w2 m ⇒
      ∃ms. LPREFIX (fromList ms) m ∧ bresponses files [r] ≼ ch_read 0 (side 1 ms)
End
