(*
  The blocking L1 (L3-09; design note L3-09 §1): honestL1PFModel's
  prefetching L1, with one change: a round with nothing to do polls
  BLOCKING (block flag 1) instead of non-blocking.

  A round is idle iff
   - the server's actions are [] and it is not busy (bz h: for a stateful
     server, a store query is pending; option C's busy test);
   - nothing is ready for the server (else the PF L1 would tell it so in
     every round);
   - L1 has nothing only the clock would end: the listener is not paused,
     every hung-up fd (D19's hups) is still held, with an empty outbox and
     a zero count, and every closing fd still has bytes to flush (none is
     due to be reaped).
  (D20: a poll has no size limit, so every poll set fits one call.)
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

(* MAIN: the PF tail is its (non-blocking) poll, then pf_after *)
Theorem pf_tail_after:
  pf_tail lfd hw hs (w, ps) =
    case l1_polls [pf_poll_set lfd hw ps hs] w of
    | NONE => NONE
    | SOME (rv, w1, pevs) => pf_after lfd hw hs ps (pf_poll_set lfd hw ps hs) (rv, w1, pevs)
Proof
  simp[pf_tail_def, pf_after_def] >> every_case_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   The blocking poll
   ------------------------------------------------------------------------ *)

(* A blocking poll (block flag 1) of (fd, events) entries; its buffer is
   the non-blocking poll's (poll_buf, D20) *)
Definition pollb_conf_def:
  pollb_conf = [1w : word8]
End

(* Its outcome: it returns (INL: the bytes, the world, the event), or it
   waits forever (INR: the configuration and buffer of the final, diverging
   call) *)
Definition sys_pollb_def:
  sys_pollb fes w =
    case l0_ffi_fn «sys_poll» pollb_conf (poll_buf fes) w of
    | SOME (FFIreturn out w') =>
        SOME (INL (out, w', IO_event (ExtCall «sys_poll») pollb_conf (ZIP (poll_buf fes, out))))
    | SOME FFIdiverge => SOME (INR (pollb_conf, poll_buf fes))
    | NONE => NONE
End

(* ------------------------------------------------------------------------
   Idle rounds, and the round
   ------------------------------------------------------------------------ *)

Definition pf_idle_def:
  pf_idle lfd hw ps hs ⇔
    ps.pause = 0 ∧ pf_ready lfd ps hs = [] ∧
    EVERY (λ(f, n). outbox_of ps.b f = [] ∧ n = 0 ∧
                    (MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing)) ps.hups ∧
    EVERY (λf. outbox_of ps.b f ≠ [] ∧ ¬MEM f ps.b.gone) ps.b.closing
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

(* ------------------------------------------------------------------------
   An idle round whose poll reports nothing changes nothing
   ------------------------------------------------------------------------ *)

Theorem l1_reap_idle[local]:
  ∀fs w b. EVERY (λf. outbox_of b f ≠ [] ∧ ¬MEM f b.gone) fs ⇒
           l1_reap fs (w, b) = SOME ((w, b), [])
Proof
  Induct >> simp[l1_reap_def]
QED

Theorem hup_step_idle[local]:
  EVERY (λ(f, n). outbox_of ps.b f = [] ∧ n = 0 ∧
                  (MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing)) ps.hups ⇒
  hup_step [] ob [] ps = ps
Proof
  rw[hup_step_def] >>
  ‘FILTER (λ(f,n). MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing) ps.hups = ps.hups’
    by (simp[FILTER_EQ_ID] >> fs[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  ‘MAP (λ(f,n). if outbox_of ps.b f = [] ∨ LENGTH (outbox_of ps.b f) < LENGTH (ob f)
                then (f,0) else (f,n + 1)) ps.hups = ps.hups’
    by (irule LIST_EQ >> rw[EL_MAP] >> Cases_on ‘EL x ps.hups’ >> simp[] >>
        fs[EVERY_EL] >> first_x_assum drule >> simp[]) >>
  simp[] >>
  ‘FILTER (λ(f,n). pf_hupwait ≤ n) ps.hups = []’
    by (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM, FORALL_PROD, pf_hupwait_def] >>
        metis_tac[DECIDE “¬(8n ≤ 0)”]) >>
  ‘FILTER (λ(f,n). n < pf_hupwait) ps.hups = ps.hups’
    by (simp[FILTER_EQ_ID] >> fs[EVERY_MEM, FORALL_PROD, pf_hupwait_def] >>
        metis_tac[DECIDE “0n < 8”]) >>
  simp[l1p_component_equality]
QED

(* MAIN: in an idle state, a poll that reports nothing leaves L1 as it was;
   the server is told nothing *)
Theorem pf_after_idle:
  pf_idle lfd hw ps hs ∧
  EVERY (λ(f, r). ¬r.rin ∧ ¬r.rout ∧ ¬r.rerr ∧ ¬r.rhup) rv ⇒
  pf_after lfd hw hs ps fes (rv, w1, pevs) = SOME ([], (w1, ps), [], pevs)
Proof
  rw[pf_idle_def, pf_after_def] >>
  ‘writable_fds rv = [] ∧ readable_fds rv = [] ∧ hup_fds rv = []’
    by (simp[writable_fds_def, readable_fds_def, hup_fds_def, FILTER_EQ_NIL] >>
        fs[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  simp[l1_flush_def, pf_fetch_def] >>
  ‘ps with b := ps.b = ps’ by simp[l1p_component_equality] >>
  simp[hup_step_idle, l1_reap_idle] >>
  ‘ps with <| b := ps.b; pause := 0 |> = ps’ by simp[l1p_component_equality] >>
  simp[]
QED
