(*
  Spec forms for the endpoint world (for the user's review).

  RELY/GUARANTEE.  A spec is
     rg_spec cls guar prog ⇔
       ∀w. cls w ∧ ep_rely w ⇒
           ∃io. prog runs forever in w with trace io ∧ guar w io
  The rely is the environment's sanity (endpointFair: arrivals make sense,
  the kernel's choices are sane); a liveness guarantee about channel c
  additionally assumes that c's peer keeps reading (reads_fair w io c).
  The world is reactive, so what a peer has sent is read off the run
  (peer_sent_at).  The class cls fixes
  the shape of the world at the start (which listeners, which calls).  The
  guarantee is about the trace, per EPISODE: episode j is the life of the
  j-th fd the program opened (by accept or connect) until it is closed, as
  in EchoSpec2 (fds are reused).  Guarantees come in two shapes:
   - always P: P of every finite prefix (safety: outputs are a prefix of a
     function of inputs);
   - eventually P: P of some finite prefix (liveness: outputs eventually
     reach a function of inputs the environment provided).

  FEATURES AS PARAMETERS.  Backpressure (takes), fd reuse (alloc, close)
  and outbound connections (connect, accepts) are fields of the world, and
  the specs quantify over ALL their values.  The simple worlds are
  instances: no_backpressure w (every write accepted whole), and the
  classes that offer only some calls (w.calls).  A spec about all worlds
  of a class implies the same spec about a smaller class (rg_spec_mono,
  proved below), so the simple theorems are corollaries by instantiation,
  never case splits.
*)
Theory endpointSpecForms
Ancestors
  llist ffi semantics ffiSpikeSocketFFI EchoSpec EchoSpec2 endpointWorld
  endpointFair
Libs
  preamble

(* ------------------------------------------------------------------------
   Classes of worlds
   ------------------------------------------------------------------------ *)

Definition all_calls_def:
  all_calls = [«sock_poll»; «sock_writable»; «sock_accept»; «sock_connect»;
               «sock_read»; «sock_write»; «sock_send»; «sock_close»]
End

(* Version 1's and version 2's calls *)
Definition v1_calls_def:
  v1_calls = [«sock_poll»; «sock_accept»; «sock_read»; «sock_write»]
End

Definition v2_calls_def:
  v2_calls = «sock_close» :: v1_calls
End

(* A server offering the calls cs: one listener lfd on address a, nothing
   else open *)
Definition ep_server_world_def:
  ep_server_world cs lfd a w ⇔
    w.listening = [(lfd, a, [])] ∧ w.chans = [] ∧ w.open_fds = [] ∧ w.calls = cs
End

(* A client: no listener, nothing open *)
Definition ep_client_world_def:
  ep_client_world w ⇔
    w.listening = [] ∧ w.chans = [] ∧ w.open_fds = [] ∧ w.calls = all_calls
End

(* The simple instance of backpressure: none *)
Definition no_backpressure_def:
  no_backpressure w ⇔ ∀j b n. w.takes j b n = n
End

(* ------------------------------------------------------------------------
   The trace, per episode
   ------------------------------------------------------------------------ *)

(* The fd an accept or connect event returned *)
Definition event_opened_def:
  event_opened ev =
    case event_accepted ev of
    | SOME f => SOME f
    | NONE =>
        case ev of
        | IO_event (ExtCall n) conf bytes =>
            (let out = MAP SND bytes in
             if n = «sock_connect» ∧ LENGTH out = 9 ∧ HD out = 1w
             then SOME (bytes_fd (TL out)) else NONE)
        | _ => NONE
End

(* The bytes a «sock_send» event sent on c: as many as its count *)
Definition event_sent_def:
  event_sent c (IO_event (ExtCall n) conf bytes) =
    (if n = «sock_send» ∧ 8 ≤ LENGTH conf ∧ bytes_fd (TAKE 8 conf) = c
     then TAKE (w82n (MAP SND bytes)) (DROP 8 conf) else []) ∧
  event_sent c _ = []
End

Definition opened_fds_def:
  opened_fds evs =
    FLAT (MAP (λev. case event_opened ev of SOME f => [f] | NONE => []) evs)
End

(* As EchoSpec2's ep_events, for episodes opened by accept or connect *)
Definition ch_events_def:
  ch_events (j:num) (k:num) (opn : (word64 # num) list) [] = [] ∧
  ch_events j k opn (ev :: evs) =
    (if MEM j (MAP SND opn) then [ev] else []) ++
    (case event_opened ev of
     | SOME f => ch_events j (k + 1) ((f, k) :: ADELKEY f opn) evs
     | NONE =>
         case event_closed ev of
         | SOME f => ch_events j k (ADELKEY f opn) evs
         | NONE => ch_events j k opn evs)
End

(* What the program read in, and sent in (by «sock_write» or «sock_send»),
   episode j *)
Definition ch_read_def:
  ch_read j evs =
    if j < LENGTH (opened_fds evs) then
      bytes_read_from (EL j (opened_fds evs)) (ch_events j 0 [] evs)
    else []
End

Definition ch_sent_def:
  ch_sent j evs =
    if j < LENGTH (opened_fds evs) then
      let f = EL j (opened_fds evs) in
        FLAT (MAP (λev. event_written f ev ++ event_sent f ev) (ch_events j 0 [] evs))
    else []
End

(* ------------------------------------------------------------------------
   Episodes and the world's channels
   ------------------------------------------------------------------------ *)

(* The world after the calls of a trace (its oracle is deterministic) *)
Definition ep_replay_def:
  ep_replay w [] = w ∧
  ep_replay w (IO_event (ExtCall n) conf bs :: evs) =
    (case ep_ffi_fn n conf (MAP FST bs) w of
     | SOME (_, w') => ep_replay w' evs
     | NONE => w) ∧
  ep_replay w (_ :: evs) = ep_replay w evs
End

(* The world's channel behind episode j of the trace evs: the channel of
   the fd the j-th opening returned, in the world just after it *)
Definition ep_chan_def:
  ep_chan w evs j =
    case FILTER (λi. IS_SOME (event_opened (EL i evs))) (COUNT_LIST (LENGTH evs)) of
    | is => if j < LENGTH is then
              let i = EL j is in
                ALOOKUP (ep_replay w (TAKE (SUC i) evs)).open_fds
                        (THE (event_opened (EL i evs)))
            else NONE
End

(* What the peer of channel c has sent by the end of the prefix evs (the
   world is reactive, so this depends on what the program did) *)
Definition peer_sent_at_def:
  peer_sent_at w evs c =
    let w' = ep_replay w evs in
      if c < LENGTH w'.chans then (EL c w'.chans).recv else []
End

(* How often the peer of channel c has read, by the end of evs *)
Definition peer_reads_at_def:
  peer_reads_at w evs c =
    let w' = ep_replay w evs in
      if c < LENGTH w'.chans then (EL c w'.chans).drained else 0
End

(* Episode j has ended: its fd was closed *)
Definition ch_closed_def:
  ch_closed j evs ⇔
    j < LENGTH (opened_fds evs) ∧
    EXISTS (λev. event_closed ev = SOME (EL j (opened_fds evs))) (ch_events j 0 [] evs)
End

(* ------------------------------------------------------------------------
   Rely/guarantee
   ------------------------------------------------------------------------ *)

Definition always_def:
  always P io ⇔ ∀evs. LPREFIX (fromList evs) io ⇒ P evs
End

Definition eventually_def:
  eventually P io ⇔ ∃evs. LPREFIX (fromList evs) io ∧ P evs
End

(* PROGRESS ASSUMPTION (a per-guarantee antecedent, never part of the
   rely): in the run io, channel c's peer keeps reading *)
Definition reads_fair_def:
  reads_fair w io c ⇔
    ∀evs. LPREFIX (fromList evs) io ⇒
          ∃evs'. LPREFIX (fromList evs') io ∧ peer_reads_at w evs c < peer_reads_at w evs' c
End

(* INPUT LIVENESS: whatever a peer has sent, the program eventually reads
   in that peer's episode, unless it ends the episode *)
Definition input_live_def:
  input_live w io ⇔
    ∀evs j c. LPREFIX (fromList evs) io ∧ ep_chan w evs j = SOME c ⇒
              eventually (λevs'. peer_sent_at w evs c ≼ ch_read j evs' ∨ ch_closed j evs') io
End

Definition rg_spec_def:
  rg_spec cls guar (prog : dec list) ⇔
    ∀w. cls w ∧ ep_rely w ⇒
        ∃io. semantics_prog (init_state (ep_ffi w)) init_env prog (Diverge io) ∧
             guar w io
End

(* MAIN: a spec about a class implies the same spec about a smaller class:
   the simple theorems are corollaries by instantiation *)
Theorem rg_spec_mono:
  rg_spec cls guar prog ∧ (∀w. cls' w ⇒ cls w) ⇒ rg_spec cls' guar prog
Proof
  rw[rg_spec_def]
QED

(* ... and a weaker guarantee *)
Theorem rg_spec_weaken:
  rg_spec cls guar prog ∧ (∀w io. cls w ∧ guar w io ⇒ guar' w io) ⇒ rg_spec cls guar' prog
Proof
  rw[rg_spec_def] >> metis_tac[]
QED
