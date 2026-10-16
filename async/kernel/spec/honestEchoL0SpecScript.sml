(*
  The echo server's safety over the RAW trace of the honest L0 world (the
  statement approved by the user; design/36 P3).

  An L0 event is IO_event (ExtCall «sys_…») conf (ZIP (in, out)); out
  starts with the 13-byte result header (honestL0's enc_res / dec_res):
  status 0 and an 8-byte value on success.  As EchoEpisodesSpec, the episodes are
  the accepted connections, in accept order; episode j lasts from the
  j-th successful accept up to the first successful close of its fd.
    - l0_read j evs: the bytes the server received in episode j;
    - l0_sent j evs: of each send in episode j, the bytes the kernel took
      (the count in the result header): what the real client can receive.
  echo_safe_l0: while fewer than 2^64 - 1 connections have been accepted,
  in every episode, the bytes sent are a prefix of the bytes received.
*)
Theory honestEchoL0Spec
Ancestors
  llist ffi honestL0 honestL0World honestL0Rely honestL0WorldProps socketWorld
Libs
  preamble

(* The decoded result header of an event's output *)
Definition l0_ev_res_def:
  l0_ev_res (bytes : (word8 # word8) list) = dec_res (MAP SND bytes)
End

(* The fd a successful accept returned *)
Definition l0_event_accepted_def:
  l0_event_accepted (IO_event (ExtCall n) conf bytes) =
    (if n = «sys_accept» ∧ LENGTH conf = 8 then
       case l0_ev_res bytes of SOME (Ok k) => SOME (n2w k : word64) | _ => NONE
     else NONE) ∧
  l0_event_accepted _ = NONE
End

(* The fd a successful close closed *)
Definition l0_event_closed_def:
  l0_event_closed (IO_event (ExtCall n) conf bytes) =
    (if n = «sys_close» ∧ LENGTH conf = 8 then
       case l0_ev_res bytes of SOME (Ok _) => SOME (bytes_fd conf) | _ => NONE
     else NONE) ∧
  l0_event_closed _ = NONE
End

(* The accepted fds, in order: episode j's fd is the j-th *)
Definition l0_accepted_def:
  l0_accepted evs =
    FLAT (MAP (λev. case l0_event_accepted ev of SOME f => [f] | NONE => []) evs)
End

(* The events during episode j (as EchoEpisodesSpec's ep_events): k counts the
   accepts so far; opn maps each open accepted fd to its episode *)
Definition l0_ep_events_def:
  l0_ep_events (j:num) (k:num) (opn : (word64 # num) list) [] = [] ∧
  l0_ep_events j k opn (ev :: evs) =
    (if MEM j (MAP SND opn) then [ev] else []) ++
    (case l0_event_accepted ev of
     | SOME f => l0_ep_events j (k + 1) ((f, k) :: ADELKEY f opn) evs
     | NONE =>
         case l0_event_closed ev of
         | SOME f => l0_ep_events j k (ADELKEY f opn) evs
         | NONE => l0_ep_events j k opn evs)
End

(* The bytes a successful recv on fd f returned (none at EOF) *)
Definition l0_event_recv_def:
  l0_event_recv f (IO_event (ExtCall n) conf bytes) =
    (if n = «sys_recv» ∧ LENGTH conf = 8 ∧ bytes_fd conf = f then
       case l0_ev_res bytes of
       | SOME (Ok k) => TAKE k (DROP 13 (MAP SND bytes))
       | _ => []
     else []) ∧
  l0_event_recv f _ = []
End

(* The bytes the kernel took from a successful send of bs on fd f: the
   first k, k the count in the header *)
Definition l0_event_sent_def:
  l0_event_sent f (IO_event (ExtCall n) conf bytes) =
    (if n = «sys_send» ∧ 8 ≤ LENGTH conf ∧ bytes_fd (TAKE 8 conf) = f then
       case l0_ev_res bytes of
       | SOME (Ok k) => TAKE k (DROP 8 conf)
       | _ => []
     else []) ∧
  l0_event_sent f _ = []
End

Definition l0_read_def:
  l0_read j evs =
    if j < LENGTH (l0_accepted evs) then
      FLAT (MAP (l0_event_recv (EL j (l0_accepted evs))) (l0_ep_events j 0 [] evs))
    else []
End

Definition l0_sent_def:
  l0_sent j evs =
    if j < LENGTH (l0_accepted evs) then
      FLAT (MAP (l0_event_sent (EL j (l0_accepted evs))) (l0_ep_events j 0 [] evs))
    else []
End

(* The startup contract: no listener, no connections, only the process's
   own fds (0-2 among them), within the fd limit, and the world's rely *)
Definition l0_server_world_def:
  l0_server_world w0 ⇔
    w0.listeners = [] ∧ w0.chans = [] ∧ w0.open_fds = [] ∧ w0.hist = [] ∧
    MEM 0w w0.reserved ∧ MEM 1w w0.reserved ∧ MEM 2w w0.reserved ∧
    fds_lt w0 ∧ l0_rely w0
End

(* Safety *)
Definition echo_safe_l0_def:
  echo_safe_l0 io ⇔
    ∀evs j. LPREFIX (fromList evs) io ∧ LENGTH (l0_accepted evs) < 2 ** 64 − 1 ⇒
            l0_sent j evs ≼ l0_read j evs
End
