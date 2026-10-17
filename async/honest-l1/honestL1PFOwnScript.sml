(*
  L1 owns every fd it accepted and has made no close call on since: on the
  PF run, an fd returned by a successful accept on the run's trace, with no
  close call on it after that event, is in L1's handle table, its closing
  list, or its queue of prefetched connections.

  L1 gives an fd up only through l1_close, which makes the close call (the
  auto-close at EOF, the reap); so the property holds step by step.  The
  events are the run's own trace (revs); acc_ev and close_ev read them as
  honestEchoL0Spec.l0_event_accepted and honestL1BStmts.l0_close_call do.

  MAIN: run_acc_owned.
*)
Theory honestL1PFOwn
Ancestors
  honestL1PFLive honestL1PFInv honestL1PFModel honestL1Model honestL0World honestL0WorldProps
  asyncCore asyncLevel1 alist
Libs
  preamble

Definition acc_ev_def:
  acc_ev f (IO_event (ExtCall n) conf bytes) =
    (n = «sys_accept» ∧ LENGTH conf = 8 ∧
     ∃k. dec_res (MAP SND bytes) = SOME (Ok k) ∧ f = (n2w k : word64)) ∧
  acc_ev f _ = F
End

Definition close_ev_def:
  close_ev f (IO_event nm conf bs) ⇔
    nm = ExtCall «sys_close» ∧ LENGTH conf = 8 ∧ bytes_fd conf = f
End

Definition owned_def:
  owned (ps : l1p) f ⇔ MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ∨ MEM f ps.acq
End

(* The handles in the table are distinct issued ones *)
Definition hdist_def:
  hdist lfd (b : l1st) ⇔
    ALL_DISTINCT (MAP FST b.tbl) ∧
    ∀h. MEM h (MAP FST b.tbl) ⇒
        ∃i. i < b.nxt ∧ l1hdln (w2n lfd) i < dimword (:64) ∧ h = l1hdl lfd i
End

(* A step from ws to ws' with events E keeps what L1 owns unless E closes
   it, and owns what E accepts and does not close after *)
Definition ostep_def:
  ostep lfd (w, ps) E (w', ps') ⇔
    l0_rely w ∧ hdist lfd ps.b ⇒
    l0_rely w' ∧ hdist lfd ps'.b ∧
    (∀f. owned ps f ∧ ¬EXISTS (close_ev f) E ⇒ owned ps' f) ∧
    (∀f pre ev post. E = pre ++ [ev] ++ post ∧ acc_ev f ev ∧ ¬EXISTS (close_ev f) post ⇒
                     owned ps' f)
End

Theorem ostep_refl:
  ostep lfd ws [] ws
Proof
  PairCases_on ‘ws’ >> simp[ostep_def]
QED

Theorem split3[local]:
  ∀E1 E2 pre ev post. E1 ++ E2 = pre ++ [ev] ++ post ⇒
    (∃post1. E1 = pre ++ [ev] ++ post1 ∧ post = post1 ++ E2) ∨
    (∃pre2. E2 = pre2 ++ [ev] ++ post ∧ pre = E1 ++ pre2)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘pre’ >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem ostep_APPEND:
  ostep lfd ws E1 ws1 ∧ ostep lfd ws1 E2 ws2 ⇒ ostep lfd ws (E1 ++ E2) ws2
Proof
  PairCases_on ‘ws’ >> PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >>
  REWRITE_TAC [ostep_def] >> strip_tac >> strip_tac >>
  qpat_x_assum ‘_ ⇒ l0_rely ws10 ∧ _’ mp_tac >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum ‘l0_rely ws10 ∧ _ ⇒ _’ mp_tac >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> fs[])
  >> rpt strip_tac >> drule split3 >> strip_tac >> gvs[]
  >- (qpat_x_assum ‘∀f'. owned ws11 f' ∧ _ ⇒ _’ irule >> simp[] >>
      qpat_x_assum ‘∀f' pre' ev' post'. pre ++ [ev] ++ post1 = _ ∧ _ ⇒ _’
        (qspecl_then [‘f’, ‘pre’, ‘ev’, ‘post1’] mp_tac) >> simp[])
  >> qpat_x_assum ‘∀f' pre' ev' post'. pre2 ++ [ev] ++ post = _ ∧ _ ⇒ _’
       (qspecl_then [‘f’, ‘pre2’, ‘ev’, ‘post’] mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   Events of L0 calls
   ------------------------------------------------------------------------ *)

Theorem l0_do_ev:
  l0_rely w ∧ l0_do n conf alen w = SOME (out, w', ev) ⇒
  l0_rely w' ∧ ∃bs. ev = IO_event (ExtCall n) conf bs ∧ MAP SND bs = out
Proof
  rw[l0_do_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> rw[MAP_ZIP]
QED

Theorem l0_do_buf_ev:
  l0_rely w ∧ l0_do_buf n conf bytes w = SOME (out, w', ev) ⇒
  l0_rely w' ∧ ∃bs. ev = IO_event (ExtCall n) conf bs
Proof
  rw[l0_do_buf_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> rw[]
QED

Theorem acc_ev_name:
  n ≠ «sys_accept» ⇒ ¬acc_ev f (IO_event (ExtCall n) conf bs)
Proof
  simp[acc_ev_def]
QED

Theorem close_ev_name:
  n ≠ «sys_close» ⇒ ¬close_ev f (IO_event (ExtCall n) conf bs)
Proof
  simp[close_ev_def]
QED

Theorem close_ev_close:
  close_ev f (IO_event (ExtCall «sys_close») (fd_bytes g) bs) ⇔ f = g
Proof
  simp[close_ev_def] >> simp[ffiSpikeSocketFFITheory.fd_bytes_def] >> metis_tac[]
QED

Theorem acc_ev_accept:
  acc_ev f (IO_event (ExtCall «sys_accept») (fd_bytes l) bs) ⇔
  ∃k. dec_res (MAP SND bs) = SOME (Ok k) ∧ f = n2w k
Proof
  simp[acc_ev_def, ffiSpikeSocketFFITheory.fd_bytes_def]
QED

Theorem l1hdl_inj:
  l1hdln (w2n lfd) i < dimword (:64) ∧ l1hdln (w2n lfd) j < dimword (:64) ∧
  l1hdl lfd i = l1hdl lfd j ⇒ i = j
Proof
  rw[l1hdl_def] >> ‘l1hdln (w2n lfd) i = l1hdln (w2n lfd) j’ by gvs[LESS_MOD] >>
  fs[l1hdln_def] >> every_case_tac >> fs[]
QED

(* ------------------------------------------------------------------------
   L1's steps
   ------------------------------------------------------------------------ *)

Theorem l1_close_ev:
  l0_rely w ∧ l1_close f (w, b) = SOME ((w', b'), evs) ⇒
  l0_rely w' ∧ b' = forget f b ∧ (∀g. EXISTS (close_ev g) evs ⇔ g = f) ∧
  ∀g. ¬EXISTS (acc_ev g) evs
Proof
  rw[l1_close_def, AllCaseEqs(), sys_close_def] >> gvs[] >>
  drule_all l0_do_ev >> strip_tac >> gvs[close_ev_close, acc_ev_name]
QED

Theorem forget_fields[simp]:
  (forget f b).tbl = b.tbl ∧ (forget f b).closing = FILTER ($≠ f) b.closing ∧
  (forget f b).nxt = b.nxt
Proof
  simp[forget_def, set_outbox_def]
QED

Theorem set_outbox_fields[simp]:
  (set_outbox f bs b).tbl = b.tbl ∧ (set_outbox f bs b).closing = b.closing ∧
  (set_outbox f bs b).nxt = b.nxt
Proof
  simp[set_outbox_def]
QED

Theorem after_send_fields[simp]:
  (after_send f r b).tbl = b.tbl ∧ (after_send f r b).closing = b.closing ∧
  (after_send f r b).nxt = b.nxt
Proof
  simp[after_send_def] >> every_case_tac >> simp[]
QED

Theorem l1do_write_ev:
  l0_rely w ∧ l1do lfd (w, b) (Write h bs) = SOME (r, (w', b'), evs) ⇒
  l0_rely w' ∧ b'.tbl = b.tbl ∧ b'.closing = b.closing ∧ b'.nxt = b.nxt ∧
  (∀g. ¬EXISTS (close_ev g) evs) ∧ (∀g. ¬EXISTS (acc_ev g) evs)
Proof
  rw[l1do_def, AllCaseEqs(), sys_send_def] >> gvs[] >>
  drule_all l0_do_ev >> strip_tac >> gvs[close_ev_name, acc_ev_name]
QED

Theorem MAP_FST_FILTER[local]:
  ∀l. MAP FST (FILTER (λp. FST p ≠ h) l) = FILTER (λx. x ≠ h) (MAP FST l)
Proof
  Induct >> rw[]
QED

Theorem hdist_ADELKEY:
  hdist lfd b ⇒ hdist lfd (b with tbl := ADELKEY h b.tbl)
Proof
  rw[hdist_def, ADELKEY_def, MAP_FST_FILTER]
  >- (irule FILTER_ALL_DISTINCT >> fs[]) >>
  gvs[MEM_FILTER] >> res_tac >> metis_tac[]
QED

Theorem MEM_SND_ADELKEY_other:
  ALL_DISTINCT (MAP FST l) ∧ ALOOKUP l c = SOME f ∧ MEM g (MAP SND l) ∧ g ≠ f ⇒
  MEM g (MAP SND (ADELKEY c l))
Proof
  rw[MEM_MAP, ADELKEY_def, MEM_FILTER, EXISTS_PROD] >> rename1 ‘MEM (h, g) l’ >>
  qexists_tac ‘h’ >> simp[] >> strip_tac >> gvs[] >>
  drule_all ALOOKUP_ALL_DISTINCT_MEM >> fs[]
QED

Theorem hdist_closing[simp]:
  hdist lfd (b with closing := x) ⇔ hdist lfd b
Proof
  simp[hdist_def]
QED

Theorem pdo_ostep:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ ostep lfd (w, ps) evs (w', ps')
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac
  >- ((* Accept *)
      gvs[AllCaseEqs()] >> simp[ostep_def, owned_def] >> rpt strip_tac >> gvs[] >>
      fs[hdist_def] >> TRY (metis_tac[]) >>
      rpt strip_tac >>
      TRY (qexists_tac ‘ps.b.nxt’ >> simp[] >> NO_TAC) >>
      res_tac >> TRY (qexists_tac ‘i’ >> simp[] >> NO_TAC) >>
      qspecl_then [‘c’, ‘ps.b.nxt’, ‘i’] mp_tac (Q.GENL [‘lfd’, ‘i’, ‘j’] l1hdl_inj) >> simp[])
  >- ((* Read *)
      gvs[AllCaseEqs()] >> TRY (simp[ostep_def, owned_def, set_inb_def] >> NO_TAC)
      >- (PairCases_on ‘z’ >> gvs[] >> simp[ostep_def, owned_def] >> strip_tac >>
        drule_all l1_close_ev >> strip_tac >> gvs[] >>
        ‘hdist lfd (ps.b with tbl := ADELKEY c ps.b.tbl)’
          by (irule hdist_ADELKEY >> first_assum ACCEPT_TAC) >>
        ‘hdist lfd (forget f (ps.b with tbl := ADELKEY c ps.b.tbl))’ by fs[hdist_def] >>
        simp[] >> rpt strip_tac >>
        TRY (‘f' ≠ f’ by (strip_tac >>
                           qpat_x_assum ‘∀g. EXISTS _ evs ⇔ _’ (qspec_then ‘f'’ mp_tac) >>
                           qpat_x_assum ‘EVERY _ evs’ mp_tac >>
                           REWRITE_TAC [GSYM NOT_EXISTS, combinTheory.o_DEF] >>
                           BETA_TAC >> REWRITE_TAC [ETA_AX] >> asm_rewrite_tac [])) >>
        gvs[MEM_FILTER] >>
        TRY (disj1_tac >> irule MEM_SND_ADELKEY_other >> fs[hdist_def] >> metis_tac[] >> NO_TAC) >>
        fs[EXISTS_MEM, EVERY_MEM] >> metis_tac[MEM_APPEND, MEM])
      >- (PairCases_on ‘z’ >> gvs[] >> simp[ostep_def, owned_def] >> strip_tac >>
        drule_all l1_close_ev >> strip_tac >> gvs[] >>
        ‘hdist lfd (ps.b with tbl := ADELKEY c ps.b.tbl)’
          by (irule hdist_ADELKEY >> first_assum ACCEPT_TAC) >>
        ‘hdist lfd (forget f (ps.b with tbl := ADELKEY c ps.b.tbl))’ by fs[hdist_def] >>
        simp[] >> rpt strip_tac >>
        TRY (‘f' ≠ f’ by (strip_tac >>
                           qpat_x_assum ‘∀g. EXISTS _ evs ⇔ _’ (qspec_then ‘f'’ mp_tac) >>
                           qpat_x_assum ‘EVERY _ evs’ mp_tac >>
                           REWRITE_TAC [GSYM NOT_EXISTS, combinTheory.o_DEF] >>
                           BETA_TAC >> REWRITE_TAC [ETA_AX] >> asm_rewrite_tac [])) >>
        gvs[MEM_FILTER] >>
        TRY (disj1_tac >> irule MEM_SND_ADELKEY_other >> fs[hdist_def] >> metis_tac[] >> NO_TAC) >>
        fs[EXISTS_MEM, EVERY_MEM] >> metis_tac[MEM_APPEND, MEM])
      >> (simp[ostep_def, owned_def] >> strip_tac >>
        conj_tac
        >- (‘hdist lfd (ps.b with tbl := ADELKEY c ps.b.tbl)’
              by (irule hdist_ADELKEY >> first_assum ACCEPT_TAC) >> fs[hdist_def]) >>
        rpt strip_tac >> Cases_on ‘f' = f’ >> simp[] >> disj1_tac >>
        irule MEM_SND_ADELKEY_other >> fs[hdist_def] >> metis_tac[]))
  >> (* Write *)
  Cases_on ‘l1do lfd (w, ps.b) (Write c l)’ >> fs[] >> PairCases_on ‘x’ >> gvs[] >>
  simp[ostep_def, owned_def] >> strip_tac >> drule_all l1do_write_ev >> strip_tac >>
  fs[hdist_def] >> rpt strip_tac >> fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[MEM_APPEND, MEM]
QED

Theorem pacts_ostep:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒ ostep lfd (w, ps) evs (w', ps')
Proof
  Induct >- simp[pacts_def, ostep_refl] >>
  rw[pacts_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  irule ostep_APPEND >> qexists_tac ‘(ws10, ws11)’ >>
  conj_tac >- (irule pdo_ostep >> metis_tac[]) >> first_x_assum irule >> metis_tac[]
QED

(* A step that keeps L1's tables and makes neither accepts nor closes *)
Theorem ostep_quiet:
  (l0_rely w ⇒ l0_rely w' ∧ (∀g. ¬EXISTS (close_ev g) evs) ∧ (∀g. ¬EXISTS (acc_ev g) evs)) ∧
  ps'.b.tbl = ps.b.tbl ∧ ps'.b.closing = ps.b.closing ∧
  ps'.b.nxt = ps.b.nxt ∧ ps'.acq = ps.acq ⇒
  ostep lfd (w, ps) evs (w', ps')
Proof
  rw[ostep_def, owned_def, hdist_def] >> fs[EVERY_MEM, EXISTS_MEM] >>
  metis_tac[MEM_APPEND, MEM]
QED

Theorem l1_polls_ev:
  ∀fess w rv w' evs. l0_rely w ∧ l1_polls fess w = SOME (rv, w', evs) ⇒
    l0_rely w' ∧ (∀g. ¬EXISTS (close_ev g) evs) ∧ (∀g. ¬EXISTS (acc_ev g) evs)
Proof
  Induct >- simp[l1_polls_def] >> rpt gen_tac >>
  simp[Once l1_polls_def, AllCaseEqs(), sys_poll_def] >> strip_tac >> gvs[] >>
  drule_all l0_do_buf_ev >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[close_ev_name, acc_ev_name]
QED

Theorem l1_flush_ev:
  ∀fs w b w' b' evs. l0_rely w ∧ l1_flush fs (w, b) = SOME ((w', b'), evs) ⇒
    l0_rely w' ∧ b'.tbl = b.tbl ∧ b'.closing = b.closing ∧ b'.nxt = b.nxt ∧
    (∀g. ¬EXISTS (close_ev g) evs) ∧ (∀g. ¬EXISTS (acc_ev g) evs)
Proof
  Induct >- simp[l1_flush_def] >> rpt gen_tac >>
  simp[Once l1_flush_def] >> IF_CASES_TAC
  >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  simp[AllCaseEqs(), sys_send_def] >> strip_tac >> gvs[] >>
  drule_all l0_do_ev >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[close_ev_name, acc_ev_name]
QED

Theorem l1_flush_b:
  ∀fs w b w' b' evs. l1_flush fs (w, b) = SOME ((w', b'), evs) ⇒
    b'.tbl = b.tbl ∧ b'.closing = b.closing ∧ b'.nxt = b.nxt
Proof
  Induct >- simp[l1_flush_def] >> rpt gen_tac >>
  simp[Once l1_flush_def] >> IF_CASES_TAC
  >- (strip_tac >> first_x_assum drule >> simp[]) >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem drop_out_fields[simp]:
  ∀l b. (FOLDL drop_out b l).tbl = b.tbl ∧ (FOLDL drop_out b l).closing = b.closing ∧
        (FOLDL drop_out b l).nxt = b.nxt
Proof
  Induct >> simp[drop_out_def]
QED

Theorem stall_step_fields[simp]:
  (stall_step hfs ob log ps).b.tbl = ps.b.tbl ∧
  (stall_step hfs ob log ps).b.closing = ps.b.closing ∧
  (stall_step hfs ob log ps).b.nxt = ps.b.nxt ∧
  (stall_step hfs ob log ps).acq = ps.acq
Proof
  simp[stall_step_def]
QED

Theorem l1_reap_ev:
  ∀fs w b w' b' evs. l0_rely w ∧ l1_reap fs (w, b) = SOME ((w', b'), evs) ⇒
    l0_rely w' ∧ b'.tbl = b.tbl ∧ b'.nxt = b.nxt ∧
    (∀f. MEM f b.closing ∧ ¬EXISTS (close_ev f) evs ⇒ MEM f b'.closing) ∧
    (∀g. ¬EXISTS (acc_ev g) evs)
Proof
  Induct >- simp[l1_reap_def] >> rpt gen_tac >>
  simp[Once l1_reap_def] >> IF_CASES_TAC
  >- (simp[AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws’ >> gvs[] >>
      drule_all l1_close_ev >> strip_tac >> gvs[] >>
      first_x_assum drule_all >> strip_tac >> simp[] >> rpt strip_tac >>
      ‘f ≠ h’ by (strip_tac >>
                  qpat_x_assum ‘∀g. EXISTS _ evs' ⇔ _’ (qspec_then ‘f’ mp_tac) >>
                  qpat_x_assum ‘EVERY _ evs'’ mp_tac >>
                  REWRITE_TAC [GSYM NOT_EXISTS, combinTheory.o_DEF] >>
                  BETA_TAC >> REWRITE_TAC [ETA_AX] >> asm_rewrite_tac []) >>
      qpat_x_assum ‘∀f. MEM f (forget h b).closing ∧ _ ⇒ _’ irule >> simp[MEM_FILTER]) >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem pf_fetch_ev:
  ∀fs w ps w' ps' log evs. l0_rely w ∧ pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒
    l0_rely w' ∧ ps'.b.tbl = ps.b.tbl ∧ ps'.b.closing = ps.b.closing ∧ ps'.b.nxt = ps.b.nxt ∧
    (∀f. MEM f ps.acq ⇒ MEM f ps'.acq) ∧ (∀f. EXISTS (acc_ev f) evs ⇒ MEM f ps'.acq) ∧
    (∀g. ¬EXISTS (close_ev g) evs)
Proof
  Induct >- simp[pf_fetch_def] >> rpt gen_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (simp[AllCaseEqs(), sys_accept_def] >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
      drule_all l0_do_ev >> strip_tac >> gvs[] >>
      ‘ps1.b = ps.b ∧ (∀f. MEM f ps.acq ⇒ MEM f ps1.acq) ∧
       (∀f. (∃k. dec_res (MAP SND bs) = SOME (Ok k) ∧ f = n2w k) ⇒ MEM f ps1.acq)’
        by (every_case_tac >> gvs[] >> rpt strip_tac >> gvs[l0_res_of_def]) >>
      qpat_x_assum ‘(case pf_fetch _ _ _ _ of NONE => _ | SOME _ => _) = _’ mp_tac >>
      CASE_TAC >> simp[] >> PairCases_on ‘x’ >> strip_tac >> gvs[] >>
      first_x_assum drule_all >> strip_tac >> gvs[close_ev_name, acc_ev_accept] >>
      metis_tac[]) >>
  simp[AllCaseEqs(), sys_recv_def] >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  drule_all l0_do_ev >> strip_tac >> gvs[] >>
  ‘ps1.b = ps.b ∧ ps1.acq = ps.acq’ by (every_case_tac >> gvs[set_inb_def]) >>
  qpat_x_assum ‘(case pf_fetch _ _ _ _ of NONE => _ | SOME _ => _) = _’ mp_tac >>
  CASE_TAC >> simp[] >> PairCases_on ‘x’ >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[close_ev_name, acc_ev_name]
QED

Theorem pf_fetch_ostep:
  pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ ostep lfd (w, ps) evs (w', ps')
Proof
  rw[ostep_def] >> drule_all pf_fetch_ev >> strip_tac >> fs[hdist_def, owned_def] >>
  rpt strip_tac >> fs[] >> first_x_assum irule >> simp[EXISTS_APPEND]
QED

Theorem l1_reap_ostep:
  l1_reap fs (w, ps.b) = SOME ((w', b'), evs) ⇒
  ostep lfd (w, ps) evs (w', ps with <| b := b'; pause := x |>)
Proof
  rw[ostep_def] >> drule_all l1_reap_ev >> strip_tac >> fs[hdist_def, owned_def] >>
  rpt strip_tac >> fs[EXISTS_MEM, EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]
QED

Theorem pf_tail_ostep:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ⇒ ostep lfd (w, ps) evs (w', ps')
Proof
  rw[pf_tail_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 ‘l1_flush _ (w1, ps.b) = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ (w2, ps with b := b2) = SOME ((w3, ps3), log, gevs)’ >>
  irule ostep_APPEND >> qexists_tac ‘(w3, stall_step (pf_held ps3) (outbox_of ps.b) log ps3)’ >>
  reverse conj_tac >- (irule l1_reap_ostep >> qexists_tac ‘ps3.b.closing’ >> first_assum ACCEPT_TAC) >>
  ‘ostep lfd (w, ps) ((pevs ++ fevs ++ gevs) ++ [])
     (w3, stall_step (pf_held ps3) (outbox_of ps.b) log ps3)’ suffices_by simp[] >>
  irule ostep_APPEND >> qexists_tac ‘(w3, ps3)’ >>
  reverse conj_tac >- (irule ostep_quiet >> simp[]) >>
  irule ostep_APPEND >> qexists_tac ‘(w2, ps with b := b2)’ >>
  reverse conj_tac >- (irule pf_fetch_ostep >> metis_tac[]) >>
  irule ostep_APPEND >> qexists_tac ‘(w1, ps)’ >> conj_tac
  >- (irule ostep_quiet >> simp[] >> strip_tac >> drule_all l1_polls_ev >> simp[]) >>
  irule ostep_quiet >> drule l1_flush_b >> strip_tac >> simp[] >>
  strip_tac >> drule_all l1_flush_ev >> simp[]
QED

Theorem pround_ostep:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ⇒
  ostep lfd (w, ps) evs (w', ps')
Proof
  rw[pround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  irule ostep_APPEND >> qexists_tac ‘(ws10, ws11)’ >> conj_tac
  >- (irule pacts_ostep >> metis_tac[])
  >> irule pf_tail_ostep >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Theorem run_own_inv:
  run_ok lfd pol ifds m w0 ⇒
  ∀n. l0_rely (rworld lfd pol ifds m w0 n) ∧ hdist lfd (rstate lfd pol ifds m w0 n).b ∧
      ∀f pre ev post. revs lfd pol ifds m w0 n = pre ++ [ev] ++ post ∧ acc_ev f ev ∧
                      ¬EXISTS (close_ev f) post ⇒ owned (rstate lfd pol ifds m w0 n) f
Proof
  strip_tac >> Induct
  >- (simp[rworld_def, rstate_def, revs_def, prun_0, pinit_def, hdist_def, l1init_def] >>
      fs[run_ok_def]) >>
  drule prun_round >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule pround_ostep >> simp[ostep_def] >> strip_tac >> fs[] >>
  rpt strip_tac >>
  qpat_x_assum ‘revs _ _ _ _ _ (SUC n) = _’ (fn th => fs[th]) >>
  drule split3 >> strip_tac >> gvs[]
  >- (qpat_x_assum ‘∀f. owned (rstate _ _ _ _ _ n) f ∧ _ ⇒ _’ irule >> fs[] >>
      qpat_x_assum ‘∀f' pre' ev' post'. _ ++ [ev] ++ post1 = _ ∧ _ ⇒ _’ (qspecl_then [‘f’, ‘pre’, ‘ev’, ‘post1’] mp_tac) >>
      simp[])
  >> qpat_x_assum ‘∀f pre ev post. rev = _ ∧ _ ⇒ _’ irule >>
  qexistsl_tac [‘ev’, ‘post’, ‘pre2’] >> simp[]
QED

(* MAIN: an fd accepted on the run's trace, with no close call on it since,
   is L1's: in its table, its closing list, or its prefetched connections *)
Theorem run_acc_owned:
  run_ok lfd pol ifds m w0 ⇒
  ∀n f pre ev post.
    revs lfd pol ifds m w0 n = pre ++ [ev] ++ post ∧ acc_ev f ev ∧
    ¬EXISTS (close_ev f) post ⇒
    MEM f (MAP SND (rstate lfd pol ifds m w0 n).b.tbl) ∨
    MEM f (rstate lfd pol ifds m w0 n).b.closing ∨ MEM f (rstate lfd pol ifds m w0 n).acq
Proof
  rpt strip_tac >> drule run_own_inv >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  REWRITE_TAC [GSYM owned_def] >> first_x_assum irule >> metis_tac[]
QED
