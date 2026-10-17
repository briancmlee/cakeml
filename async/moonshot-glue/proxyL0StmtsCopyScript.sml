(*
  TEMPORARY VERBATIM COPY (remove at merge): the SAFETY definitions of the
  proxy's raw-trace statement, revision 6 (user-approved 2026-10-17), from
  async/moonshot-step9/l0/proxyL0StmtsScript.sml @ 3d97f542d (its safety
  definitions are revision 5's, f97d449fb, unchanged), so that
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
  honestEchoL0SpecCopy honestL0 Marshalling
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

(* pr: a front's backend.  Every successful listen is on a (rev 5); relay
   prefixes both ways; a backend connects to b and serves one front; a
   front's backend is a connect (rev 5: never another front); an unpaired
   front is sent nothing; BOUNDED BUFFERING (NEW): neither direction holds
   more than Bnd bytes read and not yet sent on *)
Definition proxy_safe_l0_def:
  proxy_safe_l0 Bnd a b (pr : num -> num option) io ⇔
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
            LENGTH (pos_read p evs) ≤ LENGTH (pos_sent q evs) + Bnd ∧
            LENGTH (pos_read q evs) ≤ LENGTH (pos_sent p evs) + Bnd
End
