(*
  The ENDPOINT HANDLE LAYER, in the model (design/36 §6, decision E1): how
  an event loop runs a library computation over close-v2's endpoint world
  (endpointWorld: listeners, accepted channels AND the program's own
  connects), as asyncHLModel does over the version-2 world.

  The computation emits actions on HANDLES (never reused; the j-th is
  hdl lfd j, skipping the listener's number):
   - EAccept l: the oldest pending connection on listener l, under a fresh
     handle (ep_accept); none if there is none;
   - EConnect a: a new channel to address a (ep_connect), under a fresh
     handle, Connecting until the next tick, when the world settles it
     (accepts a j: Up, or Refused); none if no fd is free;
   - ERead h n: a refused connect answers ERefused (once: ep_conn_err) and
     the handle is closed; otherwise ep_read: data, would-block, or EOF,
     on which the handle is closed (AUTO-CLOSE, as asyncHLModel); a closed
     handle reads EOF;
   - EWrite h bs: the bytes the world takes (ep_send; its count); all of
     them in the no-backpressure world takes j b n = n; nothing on a
     refused or closed handle; a MISUSE while the connect is pending (as
     «sock_write» is in the endpoint world): the program waits until the
     handle is reported ready.
  The poll (time passes: ep_tick): the ready handles among the interest:
  readable ones (data, EOF, refused; the listener with a pending
  connection; a closed handle) and, ONCE, a connect handle whose connect
  has settled (Up or Refused), so a client learns that its connect
  completed without polling writability.
   - ELevel h (design/45 §2.2, moonshot step 7): the level of h's
     outbox, for the proxy's cross-fd backpressure.  The layer has no
     outbox (its writes complete at once), so the answer is an ORACLE,
     lv n k for the k-th action of round n, and EVERY answer is allowed:
     a claim proved in this layer holds for every lv.  A claim that needs
     true levels is proved at L1 level (honestL1EPRefine's level_true:
     on L1's run, E1 runs this layer with lv = L1's answers, which are
     its outbox lengths) or takes a hypothesis on lv.  No world call, no
     tick.
*)
Theory endpointHLModel
Ancestors
  endpointWorld asyncHLModel asyncCore asyncLevel1 asyncM3World llist alist
Libs
  preamble

Datatype:
  eact = EAccept word64 | ERead word64 num | EWrite word64 (word8 list) | EConnect num
       | ELevel word64
End

Datatype:
  eresp = EAccepted (word64 option) | EGot ((word8 list) option) | EWrote num
        | EConnected (word64 option) | ERefused | ELvl num
End

(* The open handles and their fds; handles issued; connect handles whose
   settling has not been reported *)
Datatype:
  ehstate = <| tbl : (word64 # word64) list; nxt : num; settling : word64 list |>
End

Definition ehinit_def:
  ehinit = <| tbl := []; nxt := 0; settling := [] |>
End

Definition chan_status_def:
  chan_status w f =
    case ep_chan_of w f of SOME j => SOME (EL j w.chans).status | NONE => NONE
End

(* Forget handle h *)
Definition eh_del_def:
  eh_del h hs = hs with <| tbl := ADELKEY h hs.tbl; settling := FILTER ($≠ h) hs.settling |>
End

(* A fresh handle for fd f *)
Definition eh_new_def:
  eh_new lfd f hs = hs with <| tbl := (hdl lfd hs.nxt, f) :: hs.tbl; nxt := hs.nxt + 1 |>
End

(* One action: its response and the next world and handle state; NONE on
   misuse (an FFI call would fail, or the handles would overflow) *)
Definition ehdo_def:
  ehdo lfd v (w, hs) (EAccept l) =
    (case ep_accept l w of
     | NONE => NONE
     | SOME (NONE, w') => SOME (EAccepted NONE, (w', hs))
     | SOME (SOME f, w') =>
         if hdln (w2n lfd) hs.nxt < dimword (:64) then
           SOME (EAccepted (SOME (hdl lfd hs.nxt)), (w', eh_new lfd f hs))
         else NONE) ∧
  ehdo lfd v (w, hs) (EConnect a) =
    (case ep_connect a w of
     | (NONE, w') => SOME (EConnected NONE, (w', hs))
     | (SOME f, w') =>
         if hdln (w2n lfd) hs.nxt < dimword (:64) then
           SOME (EConnected (SOME (hdl lfd hs.nxt)),
                 (w', eh_new lfd f hs with settling := hdl lfd hs.nxt :: hs.settling))
         else NONE) ∧
  ehdo lfd v (w, hs) (ERead h n) =
    (if 0 < n ∧ n < 256 ** 8 then
       case ALOOKUP hs.tbl h of
       | NONE => SOME (EGot (SOME []), (w, hs))
       | SOME f =>
           case ep_conn_err f w of
           | SOME w1 => OPTION_MAP (λw2. (ERefused, (w2, eh_del h hs))) (ep_close f w1)
           | NONE =>
               case ep_read f n w of
               | NONE => NONE
               | SOME (SOME [], w1) =>
                   OPTION_MAP (λw2. (EGot (SOME []), (w2, eh_del h hs))) (ep_close f w1)
               | SOME (r, w1) => SOME (EGot r, (w1, hs))
     else NONE) ∧
  ehdo lfd v (w, hs) (EWrite h bs) =
    (case ALOOKUP hs.tbl h of
    | NONE => SOME (EWrote 0, (w, hs))
    | SOME f =>
        if chan_status w f = SOME Connecting then NONE
        else OPTION_MAP (λ(k, w'). (EWrote k, (w', hs))) (ep_send f bs w)) ∧
  ehdo lfd v (w, hs) (ELevel h) = SOME (ELvl v, (w, hs))
End

(* The actions of round n from the k-th on (lv: the Level oracle) *)
Definition ehacts_def:
  ehacts lfd (lv : num -> num -> num) (n : num) (k : num) st [] = SOME ([], st) ∧
  ehacts lfd lv n k st (a :: acts) =
    case ehdo lfd (lv n k) st a of
    | NONE => NONE
    | SOME (r, st1) =>
        case ehacts lfd lv n (k + 1) st1 acts of
        | NONE => NONE
        | SOME (rs, st2) => SOME (r :: rs, st2)
End

Definition ehacts_tot_def:
  ehacts_tot lfd lv n st acts =
    case ehacts lfd lv n 0 st acts of SOME x => x | NONE => ([], st)
End

(* The poll of the interest handles hfds: time passes; the ready handles,
   the world, and the handle state (settled connects reported once) *)
Definition ehpoll_def:
  ehpoll lfd hs hfds w =
    let w' = ep_tick w;
        settled = (λh. case ALOOKUP hs.tbl h of
                       | SOME f => MEM h hs.settling ∧ chan_status w' f ≠ SOME Connecting
                       | NONE => F);
        rdy = FILTER (λh. case ALOOKUP hs.tbl h of
                          | SOME f => ep_readable w' f ∨ settled h
                          | NONE => if h = lfd then ep_readable w' h else T) hfds
    in (rdy, w', hs with settling := FILTER (λh. ¬(MEM h hfds ∧ settled h)) hs.settling)
End

(* ehrounds lfd lv ifds m w0 n = (h, (w, hs)): after n rounds of the loop
   running m, polling the handles ifds h, in the endpoint world w0, with
   the Level oracle lv *)
Definition ehrounds_def:
  ehrounds lfd lv ifds m w0 0 = ([], (w0, ehinit)) ∧
  ehrounds lfd lv ifds m w0 (SUC n) =
    let (h, (w, hs)) = ehrounds lfd lv ifds m w0 n;
        (rs, (w1, hs1)) = ehacts_tot lfd lv n (w, hs) (new_actions (log_of m) h);
        (rdy, w2, hs2) = ehpoll lfd hs1 (ifds h) w1
    in (h ++ [ssnap rdy rs], (w2, hs2))
End

Definition ehhist_def:
  ehhist lfd lv ifds m w0 n = FST (ehrounds lfd lv ifds m w0 n)
End

Definition ehst_def:
  ehst lfd lv ifds m w0 n = SND (ehrounds lfd lv ifds m w0 n)
End
