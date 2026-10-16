(*
  The blocking L1 (L3-09; design note L3-09 §1): honestL1PFModel's
  prefetching L1, with one change: a round with nothing to do polls
  BLOCKING (block flag 1) instead of non-blocking.

  A round is idle iff
   - the server's actions are [] and it is not busy (bz h: for a stateful
     server, a store query is pending; option C's busy test);
   - L1 has nothing only the clock would end: the listener is not paused,
     every hung-up fd (D19's hups) has an empty outbox and a zero count, and
     every closing fd still has bytes to flush (none is due to be reaped);
   - the poll set fits one poll (at most 4096 entries).
  An idle round's poll waits until something in the poll set is ready, or
  forever: then the program is asleep (brounds stops, BAsleep).  Every
  other round is the PF round unchanged; after the poll, an idle round is
  the PF round's tail too (pf_after).

  MAIN: pf_tail_after (the PF round's tail is its poll, then pf_after),
  brounds_def.
*)
Theory honestL1BModel
Ancestors
  honestL1Model honestL1PFModel asyncCore asyncLevel1 asyncM3World
  honestL0 honestL0World
Libs
  preamble

(* ------------------------------------------------------------------------
   The PF round's tail, after its poll
   ------------------------------------------------------------------------ *)

Definition pf_after_def:
  pf_after lfd hw hs ps fes (rv, w1, pevs) =
    case l1_flush (writable_fds rv) (w1, ps.b) of
    | NONE => NONE
    | SOME ((w2, b2), fevs) =>
        case pf_fetch lfd hw (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv))
               (w2, ps with b := b2) of
        | NONE => NONE
        | SOME ((w3, ps3'), log, gevs) =>
            let ps3 = hup_step (hup_fds rv) (outbox_of ps.b) log ps3' in
            case l1_reap ps3.b.closing (w3, ps3.b) of
            | NONE => NONE
            | SOME ((w4, b4), cevs) =>
                let ps4 = ps3 with <| b := b4; pause := ps3.pause − 1 |> in
                  SOME (pf_ready lfd ps4 hs, (w4, ps4), log,
                        pevs ++ fevs ++ gevs ++ cevs)
End

(* MAIN: the PF tail is its (chunked, non-blocking) poll, then pf_after *)
Theorem pf_tail_after:
  pf_tail lfd hw hs (w, ps) =
    case l1_polls (poll_chunks (pf_poll_set lfd hw ps hs)) w of
    | NONE => NONE
    | SOME (rv, w1, pevs) => pf_after lfd hw hs ps (pf_poll_set lfd hw ps hs) (rv, w1, pevs)
Proof
  simp[pf_tail_def, pf_after_def] >> every_case_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   The blocking poll
   ------------------------------------------------------------------------ *)

(* A blocking poll of (fd, events) entries *)
Definition pollb_conf_def:
  pollb_conf (fes : (word64 # num) list) =
    1w :: FLAT (MAP (λ(f, e). fd_bytes f ++ [n2w e]) fes)
End

(* Its outcome: it returns (INL: the bytes, the world, the event), or it
   waits forever (INR: the configuration of the final, diverging call) *)
Definition sys_pollb_def:
  sys_pollb fes w =
    let conf = pollb_conf fes; alen = 13 + LENGTH fes in
    case l0_ffi_fn «sys_poll» conf (REPLICATE alen 0w) w of
    | SOME (FFIreturn out w') =>
        SOME (INL (out, w', IO_event (ExtCall «sys_poll») conf (ZIP (REPLICATE alen 0w, out))))
    | SOME FFIdiverge => SOME (INR (conf, REPLICATE alen (0w:word8)))
    | NONE => NONE
End

(* ------------------------------------------------------------------------
   Idle rounds, and the round
   ------------------------------------------------------------------------ *)

Definition pf_idle_def:
  pf_idle lfd hw ps hs ⇔
    ps.pause = 0 ∧
    EVERY (λ(f, n). outbox_of ps.b f = [] ∧ n = 0) ps.hups ∧
    EVERY (λf. outbox_of ps.b f ≠ [] ∧ ¬MEM f ps.b.gone) ps.b.closing ∧
    LENGTH (pf_poll_set lfd hw ps hs) ≤ 4096
End

Datatype:
  bstep = BRound ((word64, sresp) snapshot) (l0world # l1p) (fetched list) (io_event list)
          (* the snapshot, the next state, the fetch log, the events *)
        | BAsleep (io_event list) (word8 list # word8 list)
          (* asleep: the events before the poll, and the poll's call *)
End

Definition bround_def:
  bround lfd hw idle hs (w, ps) acts =
    case pacts lfd (w, ps) acts of
    | NONE => NONE
    | SOME (rs, evs, (w1, ps1)) =>
        if acts = [] ∧ idle ∧ pf_idle lfd hw ps1 hs then
          let fes = pf_poll_set lfd hw ps1 hs in
          case sys_pollb fes w1 of
          | NONE => NONE
          | SOME (INR cb) => SOME (BAsleep evs cb)
          | SOME (INL (out, w2, ev)) =>
              case pf_after lfd hw hs ps1 fes (poll_revents fes out, w2, [ev]) of
              | NONE => NONE
              | SOME (rdy, ws3, log, tevs) => SOME (BRound (ssnap rdy rs) ws3 log (evs ++ tevs))
        else
          case pf_tail lfd hw hs (w1, ps1) of
          | NONE => NONE
          | SOME (rdy, ws3, log, tevs) => SOME (BRound (ssnap rdy rs) ws3 log (evs ++ tevs))
End

Datatype:
  brun = BRun (((word64, sresp) snapshot) list) (l0world # l1p) (io_event list) (fetched list list)
         (* still running: the history, the state, the events, the fetch logs *)
       | BSlept (((word64, sresp) snapshot) list) (io_event list) (word8 list # word8 list)
         (* asleep: the history, the events before the final poll, its call *)
End

(* brounds lfd hw ifds bz m ws0 n: the run after n rounds; bz h: the server
   is busy after the history h *)
Definition brounds_def:
  brounds lfd hw ifds bz m ws0 0 = SOME (BRun [] ws0 [] []) ∧
  brounds lfd hw ifds bz m ws0 (SUC n) =
    case brounds lfd hw ifds bz m ws0 n of
    | NONE => NONE
    | SOME (BSlept h evs cb) => SOME (BSlept h evs cb)
    | SOME (BRun h ws evs logs) =>
        case bround lfd hw (¬bz h) (ifds h) ws (new_actions (log_of m) h) of
        | NONE => NONE
        | SOME (BAsleep revs cb) => SOME (BSlept h (evs ++ revs) cb)
        | SOME (BRound snap ws' log revs) =>
            SOME (BRun (h ++ [snap]) ws' (evs ++ revs) (logs ++ [log]))
End
