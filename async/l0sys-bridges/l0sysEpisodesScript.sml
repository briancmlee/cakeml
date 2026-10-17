(*
  Episodes of an L0 process trace (design/45 §3.2, for B2): STATEMENT-LEVEL
  definitions, for review.  Nothing here is about the kernel: these read a
  process's own I/O events (sys_* calls of socket_ffi_l0.c), so per-process
  theorems (proxy_guar', ...) and the system bridge talk about the same
  things.

  An episode is a connection the process got an fd for, numbered in the
  order the process got them: a sys_connect that made a socket (its value
  field is the new fd, also when the connect then fails), or a sys_accept
  that returned one.  A successful send or recv on fd f belongs to the
  latest episode whose fd was f; closes need not be tracked, since a send or
  recv on a closed fd fails until the fd is handed out again, which starts
  a new episode.

  For a server (no sys_connect) these are honestEchoL0Spec's episodes
  (l0_read, l0_sent), episode by episode: l0sysEpisodesEcho.
*)
Theory l0sysEpisodes
Ancestors
  ffi mlstring Marshalling ffiSpikeSocketFFI honestL0 honestL0World
Libs
  preamble

(* The value field of a result (the fd of sys_connect/sys_accept/sys_listen) *)
Definition res_val_def:
  res_val (out : word8 list) = w82n (TAKE 8 (DROP 1 out))
End

(* The fd an event got for a new connection, and how: INL p for a connect
   to port p, INR l for an accept on listener fd l.  A connect that failed
   reports its socket's fd in the value field, and 0 for no socket, so a
   failed connect counts only with a value other than 0 *)
Definition ev_new_def:
  ev_new (IO_event (ExtCall n) conf bl) =
    (let out = MAP SND bl in
     if n = «sys_connect» ∧ LENGTH conf = 2 then
       case dec_res out of
       | SOME (Ok v) => SOME (n2w v : word64, INL (w22n conf))
       | SOME (Fail _ _) =>
           if res_val out ≠ 0 then SOME (n2w (res_val out), INL (w22n conf)) else NONE
       | NONE => NONE
     else if n = «sys_accept» ∧ LENGTH conf = 8 then
       case dec_res out of
       | SOME (Ok v) => SOME (n2w v, INR (bytes_fd conf))
       | _ => NONE
     else NONE) ∧
  ev_new _ = NONE
End

(* A listener an event opened: its fd and port *)
Definition ev_listen_def:
  ev_listen (IO_event (ExtCall n) conf bl) =
    (let out = MAP SND bl in
     if n = «sys_listen» ∧ LENGTH conf = 2 then
       case dec_res out of
       | SOME (Ok v) => SOME (n2w v : word64, w22n conf)
       | _ => NONE
     else NONE) ∧
  ev_listen _ = NONE
End

(* The bytes a send accepted, and the bytes a recv returned, with the fd *)
Definition ev_sent_def:
  ev_sent (IO_event (ExtCall n) conf bl) =
    (if n = «sys_send» ∧ 8 ≤ LENGTH conf then
       case dec_res (MAP SND bl) of
       | SOME (Ok k) => SOME (bytes_fd (TAKE 8 conf), TAKE k (DROP 8 conf))
       | _ => NONE
     else NONE) ∧
  ev_sent _ = NONE
End

Definition ev_recvd_def:
  ev_recvd (IO_event (ExtCall n) conf bl) =
    (if n = «sys_recv» ∧ LENGTH conf = 8 then
       case dec_res (MAP SND bl) of
       | SOME (Ok k) => SOME (bytes_fd conf, TAKE k (DROP l0_hdr (MAP SND bl)))
       | _ => NONE
     else NONE) ∧
  ev_recvd _ = NONE
End

(* Episode j's bytes as `sel` picks them: opn maps an fd to its latest
   episode, n counts the episodes so far.  An episode on fd 0 is counted
   but gets no bytes: fd 0 is open from the start (the startup contract),
   so it is a connection's only if the program closed it, and then a
   failed connect's value 0 cannot tell "a socket on fd 0" from "no
   socket" *)
Definition ep_io_def:
  ep_io sel (j : num) (opn : (word64 # num) list) (n : num) [] = [] ∧
  ep_io sel j opn n (ev :: evs) =
    (case sel ev of
     | SOME (f, bs) => if ALOOKUP opn f = SOME j then bs else []
     | NONE => []) ++
    (case ev_new ev of
     | SOME (f, _) => ep_io sel j (if f = 0w then opn else (f, n) :: opn) (n + 1) evs
     | NONE => ep_io sel j opn n evs)
End

(* What episode j's sends accepted, and what its recvs returned *)
Definition l0_ep_sent_def:
  l0_ep_sent j evs = ep_io ev_sent j [] 0 evs
End

Definition l0_ep_recvd_def:
  l0_ep_recvd j evs = ep_io ev_recvd j [] 0 evs
End

(* How episode j began: connected to port p, or accepted on a listener of
   port p; NONE: there is no episode j *)
Datatype:
  ep_role = Connected num | Accepted num
End

Definition ep_roles_def:
  ep_roles (lst : (word64 # num) list) [] = [] ∧
  ep_roles lst (ev :: evs) =
    (case ev_new ev of
     | SOME (_, INL p) => [Connected p]
     | SOME (_, INR l) => [Accepted (case ALOOKUP lst l of SOME p => p | NONE => 0)]
     | NONE => []) ++
    ep_roles (case ev_listen ev of SOME (l, p) => (l, p) :: lst | NONE => lst) evs
End

Definition l0_ep_role_def:
  l0_ep_role j evs =
    if j < LENGTH (ep_roles [] evs) then SOME (EL j (ep_roles [] evs)) else NONE
End
