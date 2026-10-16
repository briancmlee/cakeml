(*
  DRAFT STATEMENTS for the next review round (design/35 §7): terminating
  programs, n-ary open systems, and the buffer-closure lemma.  The claims
  are definitions of propositions, as before; the small structural lemmas
  are proved.

  1. TERMINATING PROGRAMS (rg_spec_term).  rg_spec asks every run to
     diverge, so a finished client idles.  rg_spec_term lets a run either
     terminate successfully or diverge; a terminating run's (finite) trace
     must meet the guarantee, and a diverging run must never reach `done`
     (e.g. "closed its connection"): a program that is done must stop.
     The toy HTTP client is restated this way.

  2. N-ARY OPEN SYSTEMS.  A system is a list of processes, each a program
     with at most one listener on an address.  It is OPEN: an outside
     world W plays the addresses no process owns, and the clients that
     connect to the system's listeners from outside.  In a run of the
     system (sys_run):
      - each process diverges in its own endpoint world, and an
        interleaving m orders all their events;
      - a LINK pairs each episode that connects to an owned address with
        the owner's accepted episode; linked episodes are wired as in
        endpointCompose (causal and eventual delivery, drains are reads,
        EOF after shutdown);
      - every other episode is EXTERNAL: its peer is W's.  The channel's
        peer-side state (what the peer sent, its EOF, its reads) is the
        same in the process's world and in W.
     The system's EXTERNAL VIEW (ext_io) is an ordinary io_event trace: the
     external episodes' opens, reads, writes and closes, the k-th external
     episode on fd n2w k.  So a headline guarantee applies to a system
     unamended: sys_spec cls guar sys.  A closed system (endpointCompose's
     joint run) is the case with no external episodes.

  3. BUFFER CLOSURE.  A relay (the proxy) can only delay what the server
     writes and read early what the client sends, per episode, in order,
     and without loss (buf_rel).  A guarantee closed under that relation
     (buffer_closed) survives being put behind a proxy (buffer_closure):
     proxy ‖ U meets U's own guarantee at the proxy's address.  Claims:
     echo's, HTTP's and KV's guarantees are buffer closed; for KV this is
     "a linearizable server behind a proxy is still linearizable" (a relay
     only widens request intervals).

  Not claimed: existence of system runs for arbitrary programs (the Kahn
  fixpoint; report §A-7), and liveness with feedback under backpressure
  (each needs its own induction; report §B, B-6).
*)
Theory endpointOpen
Ancestors
  llist ffi semantics ffiSpikeSocketFFI EchoSpec EchoSpec2 HttpSpec
  HttpSpecBodies HttpKvSpec endpointWorld endpointFair endpointSpecForms
  endpointServers endpointClients endpointCompose
Libs
  preamble

(* ------------------------------------------------------------------------
   1. Terminating programs
   ------------------------------------------------------------------------ *)

(* Every run of prog, in every world of the class satisfying the rely,
   terminates successfully with a trace meeting guar, or diverges meeting
   guar without ever reaching done *)
Definition rg_spec_term_def:
  rg_spec_term cls guar done (prog : dec list) ⇔
    ∀w. cls w ∧ ep_rely w ⇒
        (∃evs. semantics_prog (init_state (ep_ffi w)) init_env prog
                 (Terminate Success evs) ∧ guar w (fromList evs)) ∨
        (∃io. semantics_prog (init_state (ep_ffi w)) init_env prog (Diverge io) ∧
              guar w io ∧ always (λevs. ¬done evs) io)
End

Theorem rg_spec_term_mono:
  rg_spec_term cls guar done prog ∧ (∀w. cls' w ⇒ cls w) ⇒
  rg_spec_term cls' guar done prog
Proof
  rw[rg_spec_term_def]
QED

Theorem rg_spec_term_weaken:
  rg_spec_term cls guar done prog ∧ (∀w io. cls w ∧ guar w io ⇒ guar' w io) ⇒
  rg_spec_term cls guar' done prog
Proof
  rw[rg_spec_term_def] >> metis_tac[]
QED

(* A diverging spec is a terminating spec that never finishes *)
Theorem rg_spec_term_rg_spec:
  rg_spec cls guar prog ⇒ rg_spec_term cls guar (λevs. F) prog
Proof
  rw[rg_spec_def, rg_spec_term_def, always_def] >> metis_tac[]
QED

(* The toy HTTP client, terminating: once it has closed its connection it
   exits (instead of idling) *)
Definition http_client_term_spec_def:
  http_client_term_spec a r prog ⇔
    valid_brequest r ∧
    rg_spec_term ep_client_world (client_guar a r) (λevs. ch_closed 0 evs) prog
End

(* ------------------------------------------------------------------------
   2. N-ary open systems
   ------------------------------------------------------------------------ *)

Datatype:
  proc = <| prog : dec list ; lfd : word64 option ; addr : num |>
End

(* Address a is played by a process of the system *)
Definition owned_def:
  owned (sys : proc list) a ⇔
    ∃k. k < LENGTH sys ∧ IS_SOME (EL k sys).lfd ∧ (EL k sys).addr = a
End

(* Process k's world at the start: its listener (if any), nothing open,
   every call *)
Definition proc_world_def:
  proc_world (p : proc) w ⇔
    w.listening = (case p.lfd of SOME l => [(l, p.addr, [])] | NONE => []) ∧
    w.chans = [] ∧ w.open_fds = [] ∧ w.calls = all_calls
End

(* An episode (process, episode index) *)
Type episode = “:num # num”

(* The peer-side state of channel c of a world after a trace: what the peer
   sent, whether it closed its side, how often it read, the connect's
   outcome *)
Definition peer_view_def:
  peer_view w evs c =
    let w' = ep_replay w evs in
      if c < LENGTH w'.chans then
        SOME ((EL c w'.chans).recv, (EL c w'.chans).peer_eof,
              (EL c w'.chans).drained, (EL c w'.chans).status)
      else NONE
End

(* The external episodes of a prefix ms, in order of opening: those not
   in the domain of the link *)
Definition ext_opens_def:
  ext_opens (link : episode -> episode option) (ms : (num # io_event) list) =
    FILTER (λ(k, j). link (k, j) = NONE)
      (FLAT (GENLIST (λi. let (k, ev) = EL i ms in
                            if IS_SOME (event_opened ev)
                            then [(k, LENGTH (opened_fds (side k (TAKE i ms))))]
                            else [])
                     (LENGTH ms)))
End

(* The external view of one event of process k: opens, reads, writes and
   closes of external episodes, the x-th external episode on fd n2w x
   (opn maps the process's open external fds to x) *)
Definition ext_ev_def:
  ext_ev (W_lfd : word64) (x : num) (opn : (num # word64 # num) list) k ev =
    case event_opened ev of
    | SOME f =>
        (case ev of
         | IO_event (ExtCall n) conf bs =>
             [IO_event (ExtCall n) (if n = «sock_accept» then fd_bytes W_lfd else conf)
                (ZIP (MAP FST bs, TAKE 1 (MAP SND bs) ++ fd_bytes (n2w x)))]
         | _ => [])
    | NONE =>
        case rw_fd ev of
        | SOME f => (case FIND (λ(k', f', y). k' = k ∧ f' = f) opn of
                     | SOME (_, _, y) => [ren_ev (n2w y) ev]
                     | NONE => [])
        | NONE =>
            case event_closed ev of
            | SOME f => (case FIND (λ(k', f', y). k' = k ∧ f' = f) opn of
                         | SOME (_, _, y) =>
                             [IO_event (ExtCall «sock_close») (fd_bytes (n2w y)) []]
                         | NONE => [])
            | NONE => []
End

(* The external view of a finite interleaving.  x counts the external
   episodes opened so far; opn as above *)
Definition ext_evs_def:
  ext_evs W_lfd link (x : num) opn (pre : (num # io_event) list) [] = [] ∧
  ext_evs W_lfd link x opn pre ((k, ev) :: ms) =
    let j = LENGTH (opened_fds (side k pre)) in
    let is_ext = (IS_SOME (event_opened ev) ∧ link (k, j) = NONE) in
    (if IS_SOME (event_opened ev) ∧ ¬is_ext then [] else ext_ev W_lfd x opn k ev) ++
    ext_evs W_lfd link (if is_ext then x + 1 else x)
      (case event_opened ev of
       | SOME f => if is_ext then (k, f, x) :: opn else opn
       | NONE => case event_closed ev of
                 | SOME f => FILTER (λ(k', f', y). ¬(k' = k ∧ f' = f)) opn
                 | NONE => opn)
      (pre ++ [(k, ev)]) ms
End

(* The external view of an infinite interleaving: the limit of the views of
   its prefixes *)
Definition ext_io_def:
  ext_io W_lfd link m io ⇔
    lprefix_lub {fromList (ext_evs W_lfd link 0 [] [] ms) | ms | LPREFIX (fromList ms) m} io
End

(* A run of the system sys, open to the outside world W (whose listener is
   W_lfd): process worlds ws, a link, and an interleaving m *)
Definition sys_run_def:
  sys_run (sys : proc list) W_lfd W ws link m ⇔
    (∀k. k < LENGTH sys ⇒
         proc_world (EL k sys) (ws k) ∧
         semantics_prog (init_state (ep_ffi (ws k))) init_env (EL k sys).prog
           (Diverge (proj k m))) ∧
    (* only processes of the system take part *)
    (∀ms. LPREFIX (fromList ms) m ⇒ EVERY (λ(k, ev). k < LENGTH sys) ms) ∧
    (* links: a connect to an owned address is linked to an accepted
       episode of its owner, both ways, and the two are wired *)
    (∀ms k j k' j'. LPREFIX (fromList ms) m ∧ link (k, j) = SOME (k', j') ⇒
       link (k', j') = SOME (k, j) ∧
       (j < LENGTH (opened_fds (side k ms)) ∧ j' < LENGTH (opened_fds (side k' ms)) ⇒
        ∃c c'. ep_chan (ws k) (side k ms) j = SOME c ∧
               ep_chan (ws k') (side k' ms) j' = SOME c' ∧
               flows k j k' (ws k') c' m ∧ flows k' j' k (ws k) c m ∧
               drains_are_reads k (ws k) c k' j' m ∧
               drains_are_reads k' (ws k') c' k j m)) ∧
    (∀ms k j a. LPREFIX (fromList ms) m ∧ ep_connected_to (side k ms) j a ∧ owned sys a ⇒
                IS_SOME (link (k, j))) ∧
    (* external episodes: the peer is the outside world's *)
    (∀ms x k j. LPREFIX (fromList ms) m ∧ x < LENGTH (ext_opens link ms) ∧
                EL x (ext_opens link ms) = (k, j) ⇒
                ∃c cx. ep_chan (ws k) (side k ms) j = SOME c ∧
                       ep_chan W (ext_evs W_lfd link 0 [] [] ms) x = SOME cx ∧
                       peer_view (ws k) (side k ms) c =
                       peer_view W (ext_evs W_lfd link 0 [] [] ms) cx)
End

(* THE SPEC FORM for systems: in every outside world of the class
   satisfying the rely, the system has a run (in process worlds that
   satisfy the rely) whose external view meets guar.  guar can be a
   headline guarantee, unamended *)
Definition sys_spec_def:
  sys_spec cls guar (sys : proc list) W_lfd ⇔
    ∀W. cls W ∧ ep_rely W ⇒
        ∃ws link m io. sys_run sys W_lfd W ws link m ∧
                       (∀k. k < LENGTH sys ⇒ ep_rely (ws k)) ∧
                       ext_io W_lfd link m io ∧ guar W io
End

(* ------------------------------------------------------------------------
   3. Buffer closure
   ------------------------------------------------------------------------ *)

(* io' (outside) relays io (inside), episode by episode: the same episodes;
   what the program sends shows outside no earlier than inside, and all of
   it eventually; what the peer sends is read outside no later than
   inside *)
Definition buf_rel_def:
  buf_rel (io : io_event llist) (io' : io_event llist) ⇔
    (∀evs'. LPREFIX (fromList evs') io' ⇒
       ∃evs. LPREFIX (fromList evs) io ∧
             LENGTH (opened_fds evs') ≤ LENGTH (opened_fds evs) ∧
             ∀j. ch_sent j evs' ≼ ch_sent j evs ∧ ch_read j evs' ≼ ch_read j evs) ∧
    (∀evs. LPREFIX (fromList evs) io ⇒
       ∃evs'. LPREFIX (fromList evs') io' ∧
              LENGTH (opened_fds evs) ≤ LENGTH (opened_fds evs') ∧
              ∀j. ch_sent j evs ≼ ch_sent j evs' ∧ ch_read j evs ≼ ch_read j evs')
End

(* A guarantee survives relaying: if the inside run (in world w) meets it,
   so does the outside run (in world W), provided that whatever W's peers
   sent outside reached w's peers inside *)
Definition buffer_closed_def:
  buffer_closed guar ⇔
    ∀w io W io'. guar w io ∧ buf_rel io io' ∧
                 (∀evs' c. LPREFIX (fromList evs') io' ⇒
                    ∃evs. LPREFIX (fromList evs) io ∧
                          peer_sent_at W evs' c ≼ peer_sent_at w evs c) ⇒
                 guar W io'
End

(* The system "proxy in front of U": the proxy listens on lfd (address a)
   and connects to U's address b *)
Definition behind_proxy_def:
  behind_proxy Pp lfd a U lfdU b =
    [<| prog := Pp; lfd := SOME lfd; addr := a |>;
     <| prog := U; lfd := SOME lfdU; addr := b |>]
End

(* CLAIM (buffer closure): a server meeting a buffer-closed guarantee,
   behind a proxy meeting proxy_spec, meets the same guarantee at the
   proxy's address *)
Definition buffer_closure_def:
  buffer_closure ⇔
    ∀Pp U lfd a lfdU b guar.
      a ≠ b ∧ proxy_spec lfd a b Pp ∧
      rg_spec (ep_server_world all_calls lfdU b) guar U ∧ buffer_closed guar ⇒
      sys_spec (ep_server_world all_calls lfd a) guar (behind_proxy Pp lfd a U lfdU b) lfd
End

(* CLAIMS: the headline guarantees are buffer closed.  For KV, kv_safe's
   precedes at the outside implies precedes inside (a relay only widens
   request intervals), so a linearizable server behind a proxy stays
   linearizable *)
Definition guars_buffer_closed_def:
  guars_buffer_closed ⇔
    buffer_closed (λw io. ep_echo_guar w io ∧ input_live w io) ∧
    (∀files. buffer_closed (λw io. ep_http_guar files w io ∧ input_live w io)) ∧
    buffer_closed (λw io. ep_kv_guar w io ∧ input_live w io)
End

(* CLAIM (corollary): a verified KV server behind a verified proxy *)
Definition kv_behind_proxy_def:
  kv_behind_proxy ⇔
    ∀Pp U lfd a lfdU b.
      a ≠ b ∧ proxy_spec lfd a b Pp ∧ ep_kv_spec all_calls lfdU b U ⇒
      sys_spec (ep_server_world all_calls lfd a) (λw io. ep_kv_guar w io ∧ input_live w io)
        (behind_proxy Pp lfd a U lfdU b) lfd
End
