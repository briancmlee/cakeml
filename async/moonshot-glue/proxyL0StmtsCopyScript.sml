(*
  TEMPORARY VERBATIM COPY (remove at merge): the SAFETY definitions of the
  proxy's raw-trace statement, revision 7 (user rulings), from
  async/moonshot-step9/l0/proxyL0StmtsScript.sml @ 44aef7635, with the
  four trace predicates its timeout excuse uses (poll_ev, out_poll,
  n_out_polls, send_took) from honestL1BStmts (spike/echo-live-pol
  @ e179dae84), so that
  moonshotProxyGlue can bridge them to l0sysEpisodes on this branch, which
  does not have step 9's base.
  Copied unchanged, from pbytes to proxy_safe_l0; the liveness half and
  l0_proxy_claim are left out.  The l0_event_* definitions it uses come
  from honestEchoL0SpecCopy (the same honestEchoL0Spec definitions).
  Resync it to any later revision; at the merge with step 9, delete it
  and make moonshotProxyGlue's ancestor proxyL0Stmts.
*)
Theory proxyL0StmtsCopy
Ancestors
  honestEchoL0SpecCopy honestL0 honestL0World honestL1PFModel Marshalling
Libs
  preamble

(* A port, as the C reads it (honestL1EPModel.port_bytes) *)
Definition pbytes_def:
  pbytes (p : num) : word8 list = [n2w (p DIV 256); n2w p]
End

(* The socket a connect returned (the header's value field; 0: none), and
   the port it connected to *)
Definition l0_event_connected_def:
  l0_event_connected (IO_event (ExtCall n) conf bytes) =
    (if n = «sys_connect» ∧ LENGTH conf = 2 ∧ 13 ≤ LENGTH bytes ∧
        w82n (TAKE 8 (TL (MAP SND bytes))) ≠ 0
     then SOME (n2w (w82n (TAKE 8 (TL (MAP SND bytes)))) : word64)
     else NONE) ∧
  l0_event_connected _ = NONE
End

Definition connect_port_def:
  connect_port (IO_event (ExtCall n) conf bytes) = (if n = «sys_connect» then SOME conf else NONE) ∧
  connect_port _ = NONE
End

(* The fd an event opened (accept or connect) *)
Definition l0_event_opened_def:
  l0_event_opened e =
    case l0_event_accepted e of SOME f => SOME f | NONE => l0_event_connected e
End

(* Episode p: the fd opened by event p of evs, and the events of its
   lifetime (up to a successful close of it, or a later open returning it) *)
Definition pos_fd_def:
  pos_fd p evs = if p < LENGTH evs then l0_event_opened (EL p evs) else NONE
End

Definition pos_ends_def:
  pos_ends f e ⇔ l0_event_closed e = SOME f ∨ l0_event_opened e = SOME f
End

Definition pos_events_def:
  pos_events p evs =
    case pos_fd p evs of
    | NONE => []
    | SOME f => FST (SPLITP (pos_ends f) (DROP (SUC p) evs))
End

Definition pos_open_def:
  pos_open p evs ⇔
    ∃f. pos_fd p evs = SOME f ∧ ¬EXISTS (pos_ends f) (DROP (SUC p) evs)
End

Definition pos_sent_def:
  pos_sent p evs =
    case pos_fd p evs of
    | NONE => []
    | SOME f => FLAT (MAP (l0_event_sent f) (pos_events p evs))
End

Definition pos_read_def:
  pos_read p evs =
    case pos_fd p evs of
    | NONE => []
    | SOME f => FLAT (MAP (l0_event_recv f) (pos_events p evs))
End

Definition is_front_def:
  is_front p evs ⇔ p < LENGTH evs ∧ l0_event_accepted (EL p evs) ≠ NONE
End

(* ---- verbatim from honestL1BStmts (spike/echo-live-pol @ e179dae84) ---- *)

(* A poll event *)
Definition poll_ev_def:
  poll_ev ev ⇔ ∃conf bs. ev = IO_event (ExtCall «sys_poll») conf bs
End

(* A poll that lists fd f for output (an entry (f, e), read back to the
   model's bits by pe_fe, with bit 2 of e set).  L1 polls f for output
   exactly in the rounds in which f's outbox is not empty (pf_poll_set);
   one poll per round (D20) *)
Definition out_poll_def:
  out_poll f ev ⇔
    ∃conf bs. ev = IO_event (ExtCall «sys_poll») conf bs ∧
              ∃e. MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ∧
                  2 ≤ e MOD 4
End

(* The polls in a list of events that list fd f for output; idle polls
   (which a blocking L1 collapses) never count *)
Definition n_out_polls_def:
  n_out_polls f (evs : io_event list) = LENGTH (FILTER (out_poll f) evs)
End

(* A send on fd f from which the kernel took bytes *)
Definition send_took_def:
  send_took f (IO_event nm conf bs) ⇔
    nm = ExtCall «sys_send» ∧ 8 ≤ LENGTH conf ∧ bytes_fd (TAKE 8 conf) = f ∧
    ∃k. l0_ev_res bs = SOME (Ok k) ∧ 0 < k
End

(* ---- verbatim from proxyL0Stmts revision 7 (44aef7635) ---- *)

(* D23's observed excuse, for episode p (ep_timed_out, with episodes named
   by position: for a front p that is the j-th accept, pos_timed_out K p io
   ⇔ ep_timed_out K j io, a lemma to prove) *)
Definition pos_timed_out_def:
  pos_timed_out K p io ⇔
    ∃evs span f.
      LPREFIX (fromList (evs ++ span)) io ∧ pos_open p evs ∧ pos_fd p evs = SOME f ∧
      K ≤ n_out_polls f span ∧
      EVERY (λe. poll_ev e ⇒ out_poll f e) span ∧
      ¬EXISTS (send_took f) span ∧ ¬EXISTS (pos_ends f) span
End

(* Revision 7 (user): the EXACT buffering bound, per direction p → q.
   Read on p and not yet sent on q is at most
     - L1's inbox of p: ≤ pf_chunk (L1 fetches only into an empty inbox,
       one recv of at most pf_chunk), plus
     - the proxy's read not yet written to q, plus L1's outbox of q:
       together ≤ hw + pread (pread = 4096, moonshotProxy).  The credit gate
       reads p in a round only if q's outbox after that round's writes is
       ≤ hw, and the read (≤ pread) is written in full the next round.
   Reached: q's kernel takes nothing, the last read brings q's outbox to
   exactly hw, and L1's fetch then refills p's inbox *)
Definition proxy_bnd_def:
  proxy_bnd (hw : num) = hw + pf_chunk + 4096
End

(* pr: a front's backend.  Every successful listen is on a (rev 5); relay
   prefixes both ways; a backend connects to b and serves one front; a
   front's backend is a connect (rev 5: never another front); an unpaired
   front is sent nothing; BOUNDED BUFFERING: neither direction holds more
   than proxy_bnd hw bytes read and not yet sent on, UNLESS (rev 7, user,
   option (a)) the receiving side has timed out by then (D23: L1 then
   drops that side's output, and the proxy cannot see it; option (b),
   committed with [R3](a), makes the bound unconditional) *)
Definition proxy_safe_l0_def:
  proxy_safe_l0 K hw a b (pr : num -> num option) io ⇔
    (∀p p' q. pr p = SOME q ∧ pr p' = SOME q ⇒ p = p') ∧
    ∀evs. LPREFIX (fromList evs) io ⇒
      (∀conf bs k. MEM (IO_event (ExtCall «sys_listen») conf bs) evs ∧
                   l0_ev_res bs = SOME (Ok k) ⇒ conf = pbytes a) ∧
      (∀q. q < LENGTH evs ∧ l0_event_connected (EL q evs) ≠ NONE ⇒
           connect_port (EL q evs) = SOME (pbytes b) ∧
           ∃p. p < q ∧ is_front p evs ∧ pr p = SOME q) ∧
      (∀p q. pr p = SOME q ∧ q < LENGTH evs ⇒ l0_event_connected (EL q evs) ≠ NONE) ∧
      ∀p. is_front p evs ⇒
        case pr p of
        | NONE => pos_sent p evs = []
        | SOME q =>
            pos_sent q evs ≼ pos_read p evs ∧ pos_sent p evs ≼ pos_read q evs ∧
            (pos_timed_out K q (fromList evs) ∨
             LENGTH (pos_read p evs) ≤ LENGTH (pos_sent q evs) + proxy_bnd hw) ∧
            (pos_timed_out K p (fromList evs) ∨
             LENGTH (pos_read q evs) ≤ LENGTH (pos_sent p evs) + proxy_bnd hw)
End
