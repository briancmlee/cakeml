(*
  A loop that carries a pending computation: echo with an idle deadline.

  The loop's parameter is the pending read (a computation, possibly the
  loser of an earlier choose) and the current deadline.  Each iteration races
  the pending read against the deadline:
   - the read wins: echo the data (or wait again on "would block", or stop
     at end of file), and start a fresh read;
   - the deadline wins: keep the *same* pending read (nothing is lost) and
     move the deadline on.

  The timeout branch recurses directly, without waiting or emitting first,
  so the basic recursion rule (guarded_bind) does not apply.  The split
  rule (guarded_bind_split) does: the deadline cannot pass before the first
  snapshot, so the timeout branch is only reachable after one.  The loop is
  well-formed and settled for every well-formed, settled pending read, via
  the relativized lemmas (wf_bind_on, settled_bind_on, choose_losers,
  wf_fix_on, settled_fix_on).
*)
Theory asyncIdle
Ancestors
  pair list rich_list arithmetic option pred_set string sum
  asyncCore asyncLevel1 asyncChoose asyncLoop asyncEcho
Libs
  BasicProvers

(* Finishes at the first snapshot at or after time t *)
Definition deadline_def:
  deadline t = wait (λs. if t ≤ s.now then SOME () else NONE)
End

(* Wait until fd is readable, then read it *)
Definition reader_def:
  reader fd = bind (readable fd) (λu. emit (Read fd))
End

Definition idle_body_def:
  idle_body d fd r (pend, t) =
    bind (choose pend (deadline t)) (λres.
      case res of
        INL (resp, timer) =>
          (case resp of
             Data s => bind (emit (Write fd s)) (λw. r (reader fd, t))
           | WouldBlock => bind (readable fd) (λu. r (reader fd, t))
           | Eof => return ()
           | Written => return ())
      | INR (pend', u) => r (pend', t + d))
End

(* If the pending read wins, the timer is dropped: it has no requests in
   flight, so nothing is lost. *)

Theorem deadline_needs_snapshot:
  (deadline t []).result = NONE
Proof
  simp[deadline_def, wait_needs_snapshot]
QED

(* MAIN: the idle loop is a well-defined recursive definition, by the split
   recursion rule *)
Theorem idle_body_contractive:
  contractive (idle_body d fd)
Proof
  rw[contractive_def] >> PairCases_on ‘p’ >> simp[idle_body_def]
  >> ho_match_mp_tac guarded_bind_split >> conj_tac
  (* every branch is non-expansive *)
  >- (Cases >> simp[]
      >- (PairCases_on ‘x’ >> Cases_on ‘x0’ >> simp[nonexpansive_const]
          >> ho_match_mp_tac nonexpansive_bind
          >> simp[nonexpansive_const, nonexpansive_call])
      >> PairCases_on ‘y’ >> simp[nonexpansive_call])
  (* the only results possible before any snapshot are the read's, and
     those branches are guarded *)
  >> rpt strip_tac
  >> drule_at (Pos last) choose_at_start >> simp[deadline_needs_snapshot]
  >> strip_tac >> gvs[]
  >> Cases_on ‘x’ >> simp[guarded_const]
  >> ho_match_mp_tac guarded_bind
  >> simp[emit_needs_snapshot, readable_def, wait_needs_snapshot, nonexpansive_call]
QED

Definition idle_def:
  idle d fd = fix (idle_body d fd)
End

(* MAIN: the idle loop satisfies its recursive equation *)
Theorem idle_unfold:
  idle d fd (pend, t) =
    bind (choose pend (deadline t)) (λres.
      case res of
        INL (resp, timer) =>
          (case resp of
             Data s => bind (emit (Write fd s)) (λw. idle d fd (reader fd, t))
           | WouldBlock => bind (readable fd) (λu. idle d fd (reader fd, t))
           | Eof => return ()
           | Written => return ())
      | INR (pend', u) => idle d fd (pend', t + d))
Proof
  simp[idle_def]
  >> simp[Once (MATCH_MP fix_unfold idle_body_contractive)]
  >> simp[idle_body_def]
QED

Theorem wf_reader:
  wf (reader fd)
Proof
  simp[reader_def] >> irule wf_bind >> simp[readable_def, wf_wait, wf_emit]
QED

Theorem settled_reader:
  settled (reader fd)
Proof
  simp[reader_def] >> irule settled_bind
  >> simp[readable_def, wf_wait, settled_wait, settled_emit]
QED

Theorem wf_deadline:
  wf (deadline t)
Proof
  simp[deadline_def, wf_wait]
QED

Theorem settled_deadline:
  settled (deadline t)
Proof
  simp[deadline_def, settled_wait]
QED

(* MAIN: the idle loop is well-formed whenever the pending read is *)
Theorem wf_idle:
  wf pend ⇒ wf (idle d fd (pend, t))
Proof
  strip_tac >> simp[idle_def]
  >> qspecl_then [‘idle_body d fd’, ‘λ(pend, t). wf pend’] mp_tac
       (Q.GENL [‘body’, ‘ok’] wf_fix_on)
  >> impl_tac
  >- (simp[idle_body_contractive] >> rpt strip_tac
      >> PairCases_on ‘p’ >> gvs[idle_body_def]
      >> irule wf_bind_on >> simp[wf_choose] >> rpt strip_tac
      >> drule_at (Pos last) choose_losers >> simp[wf_deadline] >> strip_tac
      >> Cases_on ‘x’
      >- (rename1 ‘INL xl’ >> PairCases_on ‘xl’ >> simp[]
          >> Cases_on ‘xl0’ >> simp[wf_return]
          >> irule wf_bind >> simp[wf_emit, readable_def, wf_wait]
          >> rpt strip_tac >> first_x_assum irule >> simp[wf_reader])
      >> rename1 ‘INR yl’ >> PairCases_on ‘yl’ >> simp[]
      >> first_x_assum irule >> simp[])
  >> disch_then (qspec_then ‘(pend, t)’ mp_tac) >> simp[]
QED

(* MAIN: the idle loop never loses a response, whenever the pending read is
   well-formed and settled *)
Theorem settled_idle:
  wf pend ∧ settled pend ⇒ settled (idle d fd (pend, t))
Proof
  strip_tac >> simp[idle_def]
  >> qspecl_then [‘idle_body d fd’, ‘λ(pend, t). wf pend ∧ settled pend’] mp_tac
       (Q.GENL [‘body’, ‘ok’] settled_fix_on)
  >> impl_tac
  >- (simp[idle_body_contractive] >> rpt strip_tac
      >> PairCases_on ‘p’ >> gvs[idle_body_def]
      >> irule settled_bind_on
      >> simp[wf_choose, settled_choose, settled_deadline] >> rpt strip_tac
      >> drule_at (Pos last) choose_losers >> simp[wf_deadline] >> strip_tac
      >> Cases_on ‘x’
      >- (rename1 ‘INL xl’ >> PairCases_on ‘xl’ >> simp[]
          >> Cases_on ‘xl0’ >> simp[settled_return]
          >> irule settled_bind
          >> simp[wf_emit, settled_emit, readable_def, wf_wait, settled_wait]
          >> rpt strip_tac >> first_x_assum irule
          >> simp[wf_reader, settled_reader])
      >> rename1 ‘INR yl’ >> PairCases_on ‘yl’ >> simp[]
      >> first_x_assum irule >> simp[])
  >> disch_then (qspec_then ‘(pend, t)’ mp_tac) >> simp[]
QED

(* Sanity check: the deadline passes before any data arrives, the loop keeps
   the pending read, and the data that arrives later is echoed *)
Definition snapt_def:
  snapt n rdy res = <| ready := rdy; now := n; results := res |>
End

Theorem example_idle_keeps_read:
  idle 5 0 (reader 0, 5)
    [snapt 6 {} []; snapt 7 {Readable 0} []; snapt 8 {} [Data "x"]] =
    <| actions := [Read 0; Write 0 "x"]; result := NONE |>
Proof
  EVAL_TAC
QED
