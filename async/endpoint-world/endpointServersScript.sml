(*
  The headline server specs in the endpoint world (for the user's review).

  SYMMETRIC FORMS.  Each headline guarantee (EchoSpec's echo_safe,
  HttpSpecBodies' http_safe_b, HttpKvSpec's kv_safe) is a property of a
  trace whose fds name connections.  In the endpoint world fds are reused,
  so a spec renames each episode's fd to its own name, n2w j for episode j
  (ren_evs, as close-v2's simulation does), and applies the UNCHANGED
  headline safety to the renamed trace.  Liveness is per channel: what
  the peer of channel c sends is eventually answered in c's episode,
  assuming only that c's own peer keeps reading (reads_fair w io c), so one
  peer that stops reading cannot excuse starving another.

  ONE SPEC PER SERVER, about all endpoint server worlds (any backpressure
  policy, any fd allocation).  The world without backpressure is an
  instance, and the simple spec is a corollary (proved here, by
  rg_spec_mono).  That the simple spec, for programs using version 1's
  calls, is the UNAMENDED headline spec is the claim *_sym_equiv
  (statements only, for review; proofs after review).
*)
Theory endpointServers
Ancestors
  llist ffi semantics ffiSpikeSocketFFI EchoSpec EchoSpec2 HttpSpec
  HttpSpecBodies HttpKvSpec endpointWorld endpointFair endpointSpecForms
Libs
  preamble

(* ------------------------------------------------------------------------
   Renaming episodes
   ------------------------------------------------------------------------ *)

(* The fd of a read, write or send event *)
Definition rw_fd_def:
  rw_fd (IO_event (ExtCall n) conf bytes) =
    (if n = «sock_read» ∧ LENGTH conf = 8 then SOME (bytes_fd conf)
     else if (n = «sock_write» ∨ n = «sock_send») ∧ 8 ≤ LENGTH conf
     then SOME (bytes_fd (TAKE 8 conf))
     else NONE) ∧
  rw_fd _ = NONE
End

(* The same event on fd c; a send becomes the write of what was sent *)
Definition ren_ev_def:
  ren_ev c (IO_event (ExtCall n) conf bytes) =
    (if n = «sock_read» then IO_event (ExtCall n) (fd_bytes c) bytes
     else if n = «sock_write» then IO_event (ExtCall n) (fd_bytes c ++ DROP 8 conf) bytes
     else IO_event (ExtCall «sock_write»)
            (fd_bytes c ++ TAKE (w82n (MAP SND bytes)) (DROP 8 conf)) []) ∧
  ren_ev c ev = ev
End

(* The trace with episode j's reads and writes on fd n2w j; everything
   else dropped *)
Definition ren_evs_def:
  ren_evs (k:num) (opn : (word64 # num) list) [] = [] ∧
  ren_evs k opn (ev :: evs) =
    (case rw_fd ev of
     | SOME f => (case ALOOKUP opn f of SOME j => [ren_ev (n2w j) ev] | NONE => [])
     | NONE => []) ++
    (case event_opened ev of
     | SOME f => ren_evs (k + 1) ((f, k) :: ADELKEY f opn) evs
     | NONE =>
         case event_closed ev of
         | SOME f => ren_evs k (ADELKEY f opn) evs
         | NONE => ren_evs k opn evs)
End

(* A headline safety property, of every prefix of the renamed trace *)
Definition sym_safe_def:
  sym_safe S io ⇔ always (λevs. S (fromList (ren_evs 0 [] evs))) io
End

(* Per-channel liveness: whatever the peer of channel c has sent by some
   point (x), eventually c's episode has sent y with P x y, provided c's
   peer keeps reading *)
Definition sym_live_def:
  sym_live P w io ⇔
    ∀evs c. LPREFIX (fromList evs) io ∧ reads_fair w io c ∧ peer_sent_at w evs c ≠ [] ⇒
            eventually (λevs'. ∃j. ep_chan w evs' j = SOME c ∧
                                   P (peer_sent_at w evs c) (ch_sent j evs')) io
End

(* ------------------------------------------------------------------------
   Echo
   ------------------------------------------------------------------------ *)

Definition ep_echo_guar_def:
  ep_echo_guar w io ⇔
    sym_safe echo_safe io ∧ sym_live (λx y. x ≼ y) w io ∧ ticks_forever w io
End

(* THE SPEC: about all endpoint server worlds offering the calls cs, with
   input liveness (needed to compose under backpressure) *)
Definition ep_echo_spec_def:
  ep_echo_spec cs lfd a prog ⇔
    rg_spec (ep_server_world cs lfd a) (λw io. ep_echo_guar w io ∧ input_live w io) prog
End

(* MAIN: the simple spec (no backpressure, today's guarantee) is a corollary *)
Theorem ep_echo_spec_simple:
  ep_echo_spec cs lfd a prog ⇒
  rg_spec (λw. ep_server_world cs lfd a w ∧ no_backpressure w) ep_echo_guar prog
Proof
  rw[ep_echo_spec_def] >> irule rg_spec_mono >> qexists_tac ‘ep_server_world cs lfd a’ >>
  simp[] >> irule rg_spec_weaken >> first_x_assum (irule_at Any) >> simp[]
QED

(* CLAIM (for review): for version 1's calls, the simple symmetric spec is
   EchoSpec's headline spec, unamended.  NOT TRUE for every program, as
   stated: version 1's connections are usable before they are accepted
   (endpointInstances' not_v1_instance), so a program that polls an fd it
   has not accepted behaves differently in the two worlds.  The version-1
   claims (echo, http, kv) are to be restricted to fd-disciplined programs
   (endpointInstances, draft): PENDING USER DECISION *)
Definition echo_sym_equiv_def:
  echo_sym_equiv ⇔
    ∀lfd a prog. echo_spec lfd prog ⇔
                 rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
                   ep_echo_guar prog
End

(* EchoSpec2, per episode: its three clauses in the endpoint vocabulary *)
Definition ep_echo2_guar_def:
  ep_echo2_guar w io ⇔
    always (λevs. ∀j. ch_sent j evs ≼ ch_read j evs) io ∧
    sym_live (λx y. x ≼ y) w io ∧ ticks_forever w io ∧ echo_closes2 io
End

(* CLAIM: for version 2's calls, the simple symmetric form is EchoSpec2's.
   PROVED in the form endpointEcho2Conv's echo2_sym_equiv_thm: ⇐ as
   stated; ⇒ for worlds that do not fill the fd space (nonsat).  As
   stated, ⇒ is false in that corner: once about 2^64 clients have come
   and closed, a program may stop polling, which ticks_forever forbids *)
Definition echo2_sym_equiv_def:
  echo2_sym_equiv ⇔
    ∀lfd a prog. echo_spec2 lfd prog ⇔
                 rg_spec (λw. ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
                   ep_echo2_guar prog
End

(* ------------------------------------------------------------------------
   HTTP (HttpSpecBodies)
   ------------------------------------------------------------------------ *)

Definition ep_http_guar_def:
  ep_http_guar files w io ⇔
    sym_safe (http_safe_b files) io ∧
    sym_live (λx y. ∀rs. EVERY valid_brequest rs ∧ brequests rs ≼ x ⇒
                         bresponses files rs ≼ y) w io ∧
    ticks_forever w io
End

Definition ep_http_spec_def:
  ep_http_spec cs lfd a files prog ⇔
    rg_spec (ep_server_world cs lfd a) (λw io. ep_http_guar files w io ∧ input_live w io) prog
End

Theorem ep_http_spec_simple:
  ep_http_spec cs lfd a files prog ⇒
  rg_spec (λw. ep_server_world cs lfd a w ∧ no_backpressure w) (ep_http_guar files) prog
Proof
  rw[ep_http_spec_def] >> irule rg_spec_mono >> qexists_tac ‘ep_server_world cs lfd a’ >>
  simp[] >> irule rg_spec_weaken >> first_x_assum (irule_at Any) >> simp[]
QED

Definition http_sym_equiv_def:
  http_sym_equiv ⇔
    ∀lfd a files prog.
      http_spec_b lfd files prog ⇔
      rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
        (ep_http_guar files) prog
End

(* ------------------------------------------------------------------------
   The key-value server (HttpKvSpec)
   ------------------------------------------------------------------------ *)

Definition ep_kv_guar_def:
  ep_kv_guar w io ⇔
    sym_safe kv_safe io ∧
    sym_live (λx y. ∀rs. EVERY valid_brequest rs ∧ brequests rs ≼ x ⇒
                         ∃ans. LENGTH ans = LENGTH rs ∧ reply_bytes ans ≼ y) w io ∧
    ticks_forever w io
End

Definition ep_kv_spec_def:
  ep_kv_spec cs lfd a prog ⇔
    rg_spec (ep_server_world cs lfd a) (λw io. ep_kv_guar w io ∧ input_live w io) prog
End

Theorem ep_kv_spec_simple:
  ep_kv_spec cs lfd a prog ⇒
  rg_spec (λw. ep_server_world cs lfd a w ∧ no_backpressure w) ep_kv_guar prog
Proof
  rw[ep_kv_spec_def] >> irule rg_spec_mono >> qexists_tac ‘ep_server_world cs lfd a’ >>
  simp[] >> irule rg_spec_weaken >> first_x_assum (irule_at Any) >> simp[]
QED

Definition kv_sym_equiv_def:
  kv_sym_equiv ⇔
    ∀lfd a prog.
      kv_spec lfd prog ⇔
      rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w) ep_kv_guar prog
End

(* ------------------------------------------------------------------------
   Bite: one peer that stops reading cannot excuse starving another
   ------------------------------------------------------------------------ *)

(* CLAIM (for review): in a fair world whose channel-0 peer never reads
   (so a server that blocks writing to it stalls) and whose channel-1 peer
   reads and has sent data, a run that never sends anything in channel 1's
   episode violates the echo guarantee; and such worlds exist *)
Definition starve_bite_def:
  starve_bite ⇔
    (∃w io. ep_server_world all_calls 3w 80 w ∧ ep_rely w ∧
            ¬reads_fair w io 0 ∧ reads_fair w io 1 ∧
            ∃evs. LPREFIX (fromList evs) io ∧ peer_sent_at w evs 1 ≠ []) ∧
    ∀w io. reads_fair w io 1 ∧
           (∃evs. LPREFIX (fromList evs) io ∧ peer_sent_at w evs 1 ≠ []) ∧
           (∀evs j. LPREFIX (fromList evs) io ∧ ep_chan w evs j = SOME 1 ⇒
                    ch_sent j evs = []) ⇒
           ¬ep_echo_guar w io
End

(* CLAIM (for review): input liveness is not implied by the headline
   guarantee: a server that reads a request only once it is complete meets
   ep_http_guar yet, under backpressure, can leave a client's large request
   unread for ever *)
Definition input_live_bite_def:
  input_live_bite ⇔
    ∃files w io. ep_server_world all_calls 3w 80 w ∧ ep_rely w ∧
                 ep_http_guar files w io ∧ ¬input_live w io
End

(* ------------------------------------------------------------------------
   Bite: a program that never lets time pass meets no server guarantee
   ------------------------------------------------------------------------ *)

(* MAIN (review-driven fix): liveness is not vacuous for a program that
   never polls: a run in which no time passes violates every endpoint
   server guarantee *)
Theorem never_polls_bite:
  (∀evs. LPREFIX (fromList evs) io ⇒ (ep_replay w evs).clock = w.clock) ⇒
  ¬ep_echo_guar w io ∧ ¬ep_echo2_guar w io ∧ ¬ep_http_guar files w io ∧
  ¬ep_kv_guar w io
Proof
  strip_tac >>
  ‘¬ticks_forever w io’
    by (rw[ticks_forever_def, eventually_def] >> qexists_tac ‘w.clock + 1’ >>
        rw[] >> Cases_on ‘LPREFIX (fromList evs) io’ >> res_tac >> simp[]) >>
  fs[ep_echo_guar_def, ep_echo2_guar_def, ep_http_guar_def, ep_kv_guar_def]
QED
