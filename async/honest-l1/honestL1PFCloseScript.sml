(*
  Close and Shutdown in the prefetching L1 ([R3](a); design note
  work/workers/r3-close/design-r3-close.md).  The server actions (sact)
  have neither, so nothing here changes honestL1PFModel's run: these are
  the semantics a layer with close actions (honestL1EPModel's EClose /
  EShut) performs on the PF state.

   - pf_close: the EOF closing path, for any handle.  The fd is closed at
     once if its outbox is empty or it is gone; otherwise it joins
     `closing`, and the round's reap closes it once it is flushed or gone
     (D23 times out a closing fd like any held fd, so the close always
     happens).  pdo's EOF branch is exactly pf_close (pdo_read_eof);
   - pf_shuts: the deferred half-close.  Each queued fd (with the caller's
     key for it) that has a handle,
     is not gone, and whose outbox is empty gets one sys_shutdown
     (SHUT_WR): success fires it; a transient error keeps it queued; any
     other error (ENOTCONN, a broken channel) drops its outbox (gone, as a
     hard send error does).  A gone fd is dropped from the queue with no
     call; an fd still flushing, or without a PF handle (a connect not yet
     up), stays queued.  So sys_shutdown is never called on a pending
     connect (D22).
*)
Theory honestL1PFClose
Ancestors
  honestL1PFInv honestL1PFModel honestL1Inv honestL1Model honestL0Rely honestL0World honestL0WorldProps
  honestL0 asyncCore asyncLevel1 asyncM3World alist
Libs
  preamble

Definition sys_shutdown_def:
  sys_shutdown f w = l0_do «sys_shutdown» (fd_bytes f) 13 w
End

(* L2 no longer sees handle h (of fd f): f's EOF mark goes with it *)
Definition pf_release_def:
  pf_release h f ps =
    ps with <| b := ps.b with tbl := ADELKEY h ps.b.tbl; eof := FILTER ($≠ f) ps.eof |>
End

Definition pf_close_def:
  pf_close f (w, ps) =
    if outbox_of ps.b f = [] ∨ MEM f ps.b.gone then
      OPTION_MAP (λ((w', b'), evs). ((w', ps with b := b'), evs)) (l1_close f (w, ps.b))
    else SOME ((w, ps with b := ps.b with closing := f :: ps.b.closing), [])
End

(* The queued shutdowns fs, each an fd with a key (the caller's name for
   it, e.g. its handle): the next state, the keys still queued, the keys
   shut, and the events *)
Definition pf_shuts_def:
  pf_shuts [] ws = SOME (ws, [], [], []) ∧
  pf_shuts ((k, f) :: fs) (w, ps) =
    if MEM f ps.b.gone then pf_shuts fs (w, ps)
    else if ¬MEM f (MAP SND ps.b.tbl) ∨ outbox_of ps.b f ≠ [] then
      OPTION_MAP (λ(ws, kp, sh, evs). (ws, k :: kp, sh, evs)) (pf_shuts fs (w, ps))
    else
      case sys_shutdown f w of
      | NONE => NONE
      | SOME (out, w1, ev) =>
          let (ps1, kp1, sh1) =
                case l0_res_of out of
                | Ok _ => (ps, [], [k])
                | Fail e _ => if l1_transient e then (ps, [k], [])
                              else (ps with b := drop_out ps.b f, [], [])
          in
            OPTION_MAP (λ(ws, kp, sh, evs). (ws, kp1 ++ kp, sh1 ++ sh, ev :: evs))
              (pf_shuts fs (w1, ps1))
End

(* ------------------------------------------------------------------------
   pdo's EOF branch is pf_close
   ------------------------------------------------------------------------ *)

Theorem pdo_read_eof:
  0 < n ∧ n < 256 ** 8 ∧ ALOOKUP ps.b.tbl h = SOME f ∧ inb_of ps f = [] ∧ MEM f ps.eof ⇒
  pdo lfd (w, ps) (Read h n) =
    OPTION_MAP (λ(ws, evs). (Got (SOME []), ws, evs)) (pf_close f (w, pf_release h f ps))
Proof
  strip_tac >>
  ‘outbox_of (ps.b with tbl := ADELKEY h ps.b.tbl) f = outbox_of ps.b f’
    by simp[outbox_of_def] >>
  simp[pdo_def, pf_close_def, pf_release_def] >> rw[] >> gvs[] >>
  Cases_on ‘l1_close f (w, ps.b with tbl := ADELKEY h ps.b.tbl)’ >> simp[] >>
  PairCases_on ‘x’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Totality and small fds (as honestL1PFInv)
   ------------------------------------------------------------------------ *)

Theorem sys_shutdown_ok:
  l0_rely w ∧ small f ⇒
  ∃out w' ev. sys_shutdown f w = SOME (out, w', ev) ∧ l0_rely w'
Proof
  rw[small_def, sys_shutdown_def] >>
  ‘l0_rely (l0_tick «sys_shutdown» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘∃out w1. l0_call «sys_shutdown» (fd_bytes f) (REPLICATE 13 0w)
              (l0_tick «sys_shutdown» w) = SOME (FFIreturn out w1)’
    by (simp[l0_call_def, l0_hdr_def, fd_ok_def] >> pairarg_tac >> simp[]) >>
  drule_all l0_do_SOME >> strip_tac >> simp[]
QED

Theorem psmall_release:
  psmall lfd ps ⇒ psmall lfd (pf_release h f ps)
Proof
  rw[psmall_def, pf_release_def] >> irule small_fds_tbl_del >> simp[]
QED

Theorem psmall_set_inb:
  psmall lfd ps ⇒ psmall lfd (set_inb f bs ps)
Proof
  rw[psmall_def, set_inb_def]
QED

Theorem small_fds_drop_out:
  small_fds lfd b ∧ small f ⇒ small_fds lfd (drop_out b f)
Proof
  rw[drop_out_def] >> irule small_fds_set_outbox >>
  gvs[small_fds_def, EVERY_FILTER_IMP]
QED

Theorem pf_close_ok:
  l0_rely w ∧ psmall lfd ps ∧ small f ⇒
  ∃w' ps' evs. pf_close f (w, ps) = SOME ((w', ps'), evs) ∧ l0_rely w' ∧ psmall lfd ps' ∧
               ps'.b.nxt = ps.b.nxt ∧ ps'.b.tbl = ps.b.tbl
Proof
  strip_tac >> ‘small_fds lfd ps.b’ by gvs[psmall_def] >>
  rw[pf_close_def]
  >- (drule_all l1_close_ok >> strip_tac >> simp[] >>
      gvs[psmall_def, l1_close_def, AllCaseEqs(), forget_def, set_outbox_def])
  >- (drule_all l1_close_ok >> strip_tac >> simp[] >>
      gvs[psmall_def, l1_close_def, AllCaseEqs(), forget_def, set_outbox_def])
  >> gvs[psmall_def, small_fds_def]
QED

Theorem pf_shuts_ok:
  ∀fs w ps.
    l0_rely w ∧ psmall lfd ps ⇒
    ∃w' ps' kp sh evs. pf_shuts fs (w, ps) = SOME ((w', ps'), kp, sh, evs) ∧
                       l0_rely w' ∧ psmall lfd ps' ∧
                       ps'.b.tbl = ps.b.tbl ∧ ps'.b.nxt = ps.b.nxt ∧
                       ps'.b.closing = ps.b.closing
Proof
  Induct >- simp[pf_shuts_def] >>
  rpt gen_tac >> strip_tac >> rename1 ‘kf :: fs’ >> PairCases_on ‘kf’ >> rename1 ‘(k, f) :: fs’ >>
  simp[Once pf_shuts_def] >>
  IF_CASES_TAC >- (first_x_assum irule >> simp[]) >>
  IF_CASES_TAC
  >- (first_x_assum (qspecl_then [‘w’, ‘ps’] mp_tac) >> simp[] >> strip_tac >> simp[]) >>
  ‘small f’
    by (gvs[psmall_def, small_fds_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all sys_shutdown_ok >> strip_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  ‘psmall lfd ps1 ∧ ps1.b.tbl = ps.b.tbl ∧ ps1.b.nxt = ps.b.nxt ∧
   ps1.b.closing = ps.b.closing’
    by (Cases_on ‘l0_res_of out’ >> gvs[] >>
        qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >>
        gvs[psmall_def] >> irule small_fds_drop_out >> simp[]) >>
  first_x_assum (qspecl_then [‘w'’, ‘ps1’] mp_tac) >> simp[] >> strip_tac >> simp[]
QED

(* What the queue keeps and fires is drawn from the queue *)
Theorem pf_shuts_sub:
  ∀fs w ps ws kp sh evs.
    pf_shuts fs (w, ps) = SOME (ws, kp, sh, evs) ⇒
    (∀k. MEM k kp ⇒ MEM k (MAP FST fs)) ∧ (∀k. MEM k sh ⇒ MEM k (MAP FST fs))
Proof
  Induct >- simp[pf_shuts_def] >>
  rpt gen_tac >> rename1 ‘kf :: fs’ >> PairCases_on ‘kf’ >> rename1 ‘(k, f) :: fs’ >>
  simp[Once pf_shuts_def] >>
  IF_CASES_TAC
  >- (strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >>
      first_x_assum drule >> metis_tac[]) >>
  Cases_on ‘sys_shutdown f w’ >> simp[] >>
  rename1 ‘sys_shutdown f w = SOME r’ >> PairCases_on ‘r’ >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  PairCases_on ‘z’ >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  ‘(∀g. MEM g kp1 ⇒ g = k) ∧ (∀g. MEM g sh1 ⇒ g = k)’
    by (qpat_x_assum ‘_ = (ps1, kp1, sh1)’ mp_tac >> rw[AllCaseEqs()] >> gvs[]) >>
  metis_tac[]
QED
