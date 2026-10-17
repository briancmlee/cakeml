(*
  The prefetching L1 (honestL1PFModel) WITH CONNECT, speaking the endpoint
  handle layer's vocabulary (endpointHLModel: EAccept / EConnect / ERead /
  EWrite; design/36 §6, decision E1).  Nothing in honestL1PFModel changes.

  A connect handle lives in its own table (ctbl) until its connect has
  settled Up; only then does it join the prefetching machinery (the PF
  state's tbl).  So no recv, poll-for-input or flush ever touches a socket
  whose connect is pending or refused.
   - EConnect a (a < 2^16; a larger address is a misuse: L0 connects only
     to loopback ports): sys_connect.  No socket: EConnected NONE.  A socket
     f: a fresh handle in ctbl, pending.  An outcome known at once (connected
     or failed at once) is kept in `early` and takes effect at the round's
     tail, as the layer's Settle arrives at the next tick (so within the round
     the handle behaves as pending; close-v2's E1 refinement needs this:
     handle names are predictable);
   - ERead on a ctbl handle: pending: would-block (EGot NONE, as a
     Connecting channel reads); refused: ERefused, the socket is closed and
     the handle forgotten;
   - ELevel h: the length of h's outbox (elevel), no syscall;
   - EWrite on a ctbl handle: pending: a misuse (as in the layer); refused:
     nothing taken (EWrote 0);
   - the round's tail additionally polls each pending connect for OUT; on
     OUT, ERR or HUP it reads the socket's pending error (sys_connerr): none:
     up (the handle moves to the PF table); an error: refused;
   - the snapshot reports a connect handle ONCE when it has settled (up or
     refused), as the layer's settling list; a refused one stays readable.
  Everything else is honestL1PFModel's (EAccept is its Accept; EGot / EWrote
  translate Got / Wrote, a complete buffered write).
*)
Theory honestL1EPModel
Ancestors
  honestL1PFModel honestL1Model endpointHLModel honestL0 honestL0World
  asyncCore asyncLevel1 asyncM3World alist
Libs
  preamble

Datatype:
  cstat = CPending | CUp | CRefused
End

Datatype:
  l1e = <| p : l1p                              (* the prefetching L1's state *)
         ; ctbl : (word64 # word64) list        (* connect handle, its fd: not yet up *)
         ; cst : (word64 # cstat) list          (* fd: its connect's status *)
         ; settling : word64 list               (* connect handles not yet reported *)
         ; early : (word64 # cstat) list |>     (* fd: a connect's outcome known at
                                                   once (up or refused), applied at
                                                   the round's tail *)
End

Definition einit_def:
  einit = <| p := pinit; ctbl := []; cst := []; settling := []; early := [] |>
End

Definition cstat_of_def:
  cstat_of es f = case ALOOKUP es.cst f of SOME c => c | NONE => CPending
End

(* A port, as the C reads it: 2 bytes, big-endian *)
Definition port_bytes_def:
  port_bytes (p : num) : word8 list = [n2w (p DIV 256); n2w p]
End

Definition sys_connect_def:
  sys_connect (p : num) w = l0_do «sys_connect» (port_bytes p) 13 w
End

Definition sys_connerr_def:
  sys_connerr f w = l0_do «sys_connerr» (fd_bytes f) 13 w
End

(* The header's value (sys_connect's fd, sys_connerr's flag) *)
Definition res_val_def:
  res_val (out : word8 list) = w82n (TAKE 8 (DROP 1 out))
End

(* A connect handle leaves ctbl: forgotten (refused, read) *)
Definition ec_del_def:
  ec_del h f es = es with <| ctbl := ADELKEY h es.ctbl; cst := ADELKEY f es.cst;
                             settling := FILTER ($≠ h) es.settling |>
End

(* Level h (design/45 §2.2): the length of L1's outbox for h's fd; 0 for
   an unknown handle or a connect handle (which has no outbox yet).  No
   syscall *)
Definition elevel_def:
  elevel es h =
    case ALOOKUP es.p.b.tbl h of SOME f => LENGTH (outbox_of es.p.b f) | NONE => 0
End

Definition edo_def:
  edo lfd pol (w, es) (EAccept l) =
    (OPTION_MAP (λ(r, (w', ps'), evs).
                   ((case r of Accepted x => EAccepted x | _ => EAccepted NONE),
                    (w', es with p := ps'), evs))
       (pdo lfd (w, es.p) (Accept l))) ∧
  edo lfd pol (w, es) (EConnect a) =
    (if 65536 ≤ a then NONE
     else
       case sys_connect a w of
       | NONE => NONE
       | SOME (out, w', ev) =>
           let v = res_val out in
             if v = 0 then SOME (EConnected NONE, (w', es), [ev])
             else if l1hdln (w2n lfd) es.p.b.nxt < dimword (:64) then
               let h = l1hdl lfd es.p.b.nxt;
                   f : word64 = n2w v;
                   c = (case l0_res_of out of
                        | Ok _ => CUp
                        | Fail e _ => if e = E_INPROGRESS then CPending else CRefused) in
                 SOME (EConnected (SOME h),
                       (w', es with <| p := es.p with b := es.p.b with nxt := es.p.b.nxt + 1;
                                       ctbl := (h, f) :: es.ctbl;
                                       cst := (f, CPending) :: ADELKEY f es.cst;
                                       settling := h :: es.settling;
                                       early := if c = CPending then es.early
                                                else (f, c) :: es.early |>), [ev])
             else NONE) ∧
  edo lfd pol (w, es) (ERead h n) =
    (case ALOOKUP es.ctbl h of
     | SOME f =>
         if ¬(0 < n ∧ n < 256 ** 8) then NONE
         else if cstat_of es f = CRefused then
           OPTION_MAP (λ((w', b'), evs). (ERefused, (w', ec_del h f (es with p := es.p with b := b')), evs))
             (l1_close f (w, es.p.b))
         else SOME (EGot NONE, (w, es), [])
     | NONE =>
         OPTION_MAP (λ(r, (w', ps'), evs).
                       ((case r of Got x => EGot x | _ => EGot NONE), (w', es with p := ps'), evs))
           (pdo lfd (w, es.p) (Read h n))) ∧
  edo lfd pol (w, es) (EWrite h bs) =
    (case ALOOKUP es.ctbl h of
     | SOME f => if cstat_of es f = CRefused then SOME (EWrote 0, (w, es), []) else NONE
     | NONE =>
         OPTION_MAP (λ(r, (w', ps'), evs).
                       (EWrote (if ALOOKUP es.p.b.tbl h = NONE then 0 else LENGTH bs),
                        (w', es with p := ps'), evs))
           (pdo lfd (w, es.p) (Write h bs))) ∧
  edo lfd pol (w, es) (ELevel h) = SOME (ELvl (elevel es h), (w, es), [])
End

Definition eacts_def:
  eacts lfd pol ws [] = SOME ([], [], ws) ∧
  eacts lfd pol ws (a :: acts) =
    case edo lfd pol ws a of
    | NONE => NONE
    | SOME (r, ws1, evs1) =>
        case eacts lfd pol ws1 acts of
        | NONE => NONE
        | SOME (rs, evs, ws2) => SOME (r :: rs, evs1 ++ evs, ws2)
End

(* The pending connects' fds (not those whose outcome is already known) *)
Definition pend_fds_def:
  pend_fds es =
    MAP SND (FILTER (λ(h, f). cstat_of es f = CPending ∧ ¬MEM f (MAP FST es.early)) es.ctbl)
End

(* The connects whose outcome was known at once take it now, at the tail
   (model state only: no syscall; an implementation of this layer must
   keep the same timing) *)
Definition apply_early_def:
  apply_early es =
    es with <| cst := FOLDR (λ(f, c) l. (f, c) :: ADELKEY f l) es.cst es.early;
               early := [] |>
End

(* Settle the pending connects the poll found writable (or ERR/HUP): read
   the pending error; none: up (the handle joins the PF table); an error:
   refused; a failing getsockopt: still pending *)
Definition settle_fds_def:
  settle_fds [] ws = SOME (ws, []) ∧
  settle_fds (f :: fs) (w, es) =
    case sys_connerr f w of
    | NONE => NONE
    | SOME (out, w1, ev) =>
        let es1 =
          (case l0_res_of out of
           | Ok _ => es with cst := (f, CUp) :: ADELKEY f es.cst
           | Fail e _ => if res_val out = 1
                         then es with cst := (f, CRefused) :: ADELKEY f es.cst
                         else es) in
          case settle_fds fs (w1, es1) of
          | NONE => NONE
          | SOME (ws, evs) => SOME (ws, ev :: evs)
End

(* Connect handles that are up join the prefetching table *)
Definition promote_def:
  promote es =
    let up = FILTER (λ(h, f). cstat_of es f = CUp) es.ctbl in
      es with <| p := es.p with b := es.p.b with tbl := up ++ es.p.b.tbl;
                 ctbl := FILTER (λ(h, f). cstat_of es f ≠ CUp) es.ctbl;
                 cst := FILTER (λ(f, c). c ≠ CUp) es.cst |>
End

(* The round's tail: the PF tail (with each pending connect also polled for
   OUT), settling, promotion; the snapshot: the PF ready handles, refused
   connect handles (readable), and each settled connect handle once *)
Definition etail_def:
  etail lfd pol hs (w, es) =
    let fes = pf_poll_set lfd pol es.p hs ++ MAP (λf. (f, 2n)) (pend_fds es) in
    case l1_polls [fes] w of
    | NONE => NONE
    | SOME (rv, w1, pevs) =>
        case l1_flush (writable_fds rv) (w1, es.p.b) of
        | NONE => NONE
        | SOME ((w2, b2), fevs) =>
            case pf_fetch lfd pol (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv))
                   (w2, es.p with b := b2) of
            | NONE => NONE
            | SOME ((w3, ps3'), log, gevs) =>
                let ps3 = stall_step (pf_held ps3') (outbox_of es.p.b) log ps3' in
                case l1_reap ps3.b.closing (w3, ps3.b) of
                | NONE => NONE
                | SOME ((w4, b4), cevs) =>
                    let ready_pend = FILTER (λf. MEM f (pend_fds es) ∧
                                               (MEM f (writable_fds rv) ∨ MEM f (readable_fds rv)))
                                            (pend_fds es) in
                    case settle_fds ready_pend
                           (w4, apply_early (es with p := ps3 with <| b := b4; pause := ps3.pause − 1 |>)) of
                    | NONE => NONE
                    | SOME ((w5, es5), sevs) =>
                        let es6 = promote es5;
                            settled = (λh. MEM h es6.settling ∧
                                           (case ALOOKUP es6.ctbl h of
                                            | SOME f => cstat_of es6 f ≠ CPending
                                            | NONE => ALOOKUP es6.p.b.tbl h ≠ NONE));
                            rdy = FILTER (λh. case ALOOKUP es6.ctbl h of
                                              | SOME f => cstat_of es6 f = CRefused ∨ settled h
                                              | NONE => MEM h (pf_ready lfd es6.p [h]) ∨ settled h) hs;
                            es7 = es6 with settling := FILTER (λh. ¬(MEM h hs ∧ settled h)) es6.settling
                        in SOME (rdy, (w5, es7), log, pevs ++ fevs ++ gevs ++ cevs ++ sevs)
End

Definition eround_def:
  eround lfd pol hs ws acts =
    case eacts lfd pol ws acts of
    | NONE => NONE
    | SOME (rs, evs, ws1) =>
        case etail lfd pol hs ws1 of
        | NONE => NONE
        | SOME (rdy, ws2, log, tevs) => SOME (ssnap rdy rs, ws2, log, evs ++ tevs)
End

Definition erounds_def:
  erounds lfd pol ifds m ws0 0 = SOME ([], ws0, [], []) ∧
  erounds lfd pol ifds m ws0 (SUC n) =
    case erounds lfd pol ifds m ws0 n of
    | NONE => NONE
    | SOME (h, ws, evs, logs) =>
        case eround lfd pol (ifds h) ws (new_actions (log_of m) h) of
        | NONE => NONE
        | SOME (snap, ws', log, revs) => SOME (h ++ [snap], ws', evs ++ revs, logs ++ [log])
End
