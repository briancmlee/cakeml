(*
  A read of an fd at end-of-file takes it out of L1's table, for good
  (once nothing waits to be handed out and nothing more is fetched):
  pdo's auto-close (honestL1PFModel: an empty inbox at EOF closes, or
  starts flushing, and forgets the handle).  The read may come some rounds
  later: until then f stays at EOF with an empty inbox under its handle,
  or has already gone.

  For SQ's drain (honestL1BQuietDrain.pf_drain, its end-of-file premise),
  with a read-soon fact such as async-spike's echo_read_soon_eof.

  MAIN: round_eof_jnv, read_eof_gone.
*)
Theory honestL1BEofClose
Ancestors
  alist honestL0 honestL0World honestL1Model honestL1PFModel honestL1PFLive
  honestL1PFConnRun honestL1PFRefine honestL1PFRound honestL1PFS4w honestL1BFetchStop
  honestL1BQuietDrain
Libs
  preamble

(* f, at EOF with an empty inbox, under h; or gone *)
Definition jnv_def:
  jnv h f ps ⇔
    ALOOKUP ps.b.tbl h = SOME f ∧ MEM f ps.eof ∧ inb_of ps f = [] ∧
    ALL_DISTINCT (MAP SND ps.b.tbl) ∧ ALL_DISTINCT (MAP FST ps.b.tbl) ∧ ps.acq = []
End

Definition gonef_def:
  gonef f ps ⇔ ¬MEM f (MAP SND ps.b.tbl) ∧ ps.acq = [] ∧ ALL_DISTINCT (MAP SND ps.b.tbl)
End

(* ------------------------------------------------------------------------
   ADELKEY on a table with distinct keys and values
   ------------------------------------------------------------------------ *)

Theorem MAP_ADELKEY_sub[local]:
  ∀l. (MEM x (MAP SND (ADELKEY k l)) ⇒ MEM x (MAP SND l)) ∧
      (ALL_DISTINCT (MAP SND l) ⇒ ALL_DISTINCT (MAP SND (ADELKEY k l))) ∧
      (ALL_DISTINCT (MAP FST l) ⇒ ALL_DISTINCT (MAP FST (ADELKEY k l)))
Proof
  Induct >> simp[ADELKEY_def, FORALL_PROD] >> rw[] >> gvs[] >>
  gvs[MEM_MAP, MEM_FILTER, ADELKEY_def, EXISTS_PROD] >> metis_tac[]
QED

Theorem ADELKEY_gone[local]:
  ∀l. ALOOKUP l h = SOME f ∧ ALL_DISTINCT (MAP SND l) ⇒ ¬MEM f (MAP SND (ADELKEY h l))
Proof
  Induct >> simp[FORALL_PROD, ADELKEY_def] >> rpt gen_tac >> rw[] >> gvs[]
  >- (strip_tac >> fs[GSYM ADELKEY_def] >> metis_tac[MAP_ADELKEY_sub])
  >> fs[GSYM ADELKEY_def] >> strip_tac >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> metis_tac[SND]
QED

Theorem ALOOKUP_same_val[local]:
  ∀l. ALOOKUP l h = SOME f ∧ ALOOKUP l h' = SOME f ∧ ALL_DISTINCT (MAP SND l) ⇒ h = h'
Proof
  Induct >> simp[FORALL_PROD] >> rpt gen_tac >> rw[] >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> metis_tac[SND]
QED

Theorem l1do_write_tbl[local]:
  l1do lfd (w, st) (Write h bs) = SOME (r, (w', st'), evs) ⇒ st'.tbl = st.tbl
Proof
  rw[l1do_def, AllCaseEqs()] >> simp[set_outbox_def, after_send_def] >>
  every_case_tac >> simp[set_outbox_def]
QED

Theorem forget_tbl'[local,simp]:
  (forget f st).tbl = st.tbl
Proof
  simp[forget_def, set_outbox_def]
QED

(* ------------------------------------------------------------------------
   One action
   ------------------------------------------------------------------------ *)

Theorem pdo_gonef:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ gonef f ps ⇒ gonef f ps'
Proof
  rw[gonef_def] >> drule_all pdo_noeof >> metis_tac[]
QED

Theorem pdo_jnv:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ jnv h f ps ⇒
  (jnv h f ps' ∨ gonef f ps') ∧ ((∃k. a = Read h k) ⇒ gonef f ps')
Proof
  Cases_on ‘a’ >> simp[pdo_def]
  >- ((* Accept: nothing waits *)
      rw[] >> gvs[jnv_def, gonef_def, AllCaseEqs()])
  >- ((* Read c n *)
      strip_tac >> Cases_on ‘ALOOKUP ps.b.tbl c’ >> fs[]
      >- (gvs[jnv_def, gonef_def] >> rw[] >> gvs[]) >>
      rename1 ‘ALOOKUP ps.b.tbl c = SOME g’ >>
      Cases_on ‘inb_of ps g ≠ []’ >> fs[]
      >- ((* data: f's state is untouched *)
          ‘g ≠ f’ by (strip_tac >> gvs[jnv_def]) >>
          ‘c ≠ h’ by (strip_tac >> gvs[jnv_def]) >>
          gvs[jnv_def, inb_of_set_inb] >> gvs[set_inb_def]) >>
      reverse (Cases_on ‘MEM g ps.eof’) >> fs[]
      >- (‘c ≠ h’ by (strip_tac >> gvs[jnv_def]) >> gvs[]) >>
      (* end-of-file: g's handle c goes *)
      ‘ps'.b.tbl = ADELKEY c ps.b.tbl ∧ ps'.eof = FILTER (λy. g ≠ y) ps.eof ∧
       ps'.inb = ps.inb ∧ ps'.acq = ps.acq’
        by (gvs[AllCaseEqs(), l1_close_def] >> TRY (PairCases_on ‘z’) >> gvs[] >>
            gvs[l1_close_def, AllCaseEqs()]) >>
      gvs[jnv_def, gonef_def, inb_of_def] >>
      Cases_on ‘c = h’ >> gvs[]
      >- metis_tac[ADELKEY_gone, MAP_ADELKEY_sub] >>
      ‘g ≠ f’ by metis_tac[ALOOKUP_same_val] >>
      simp[ALOOKUP_ADELKEY, MEM_FILTER] >> metis_tac[MAP_ADELKEY_sub])
  >> (* Write: only the outboxes change *)
  strip_tac >> PairCases_on ‘z’ >> gvs[] >> drule l1do_write_tbl >> strip_tac >>
  gvs[jnv_def, gonef_def, inb_of_def]
QED

Theorem pacts_jnv:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒
    (gonef f ps ⇒ gonef f ps') ∧
    (jnv h f ps ⇒ (jnv h f ps' ∨ gonef f ps') ∧ ((∃k. MEM (Read h k) acts) ⇒ gonef f ps'))
Proof
  Induct >> simp[pacts_def, AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> first_x_assum drule >> strip_tac >>
  conj_tac >- metis_tac[pdo_gonef] >>
  strip_tac >> drule_all pdo_jnv >> strip_tac >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The round's tail, without fetches
   ------------------------------------------------------------------------ *)

Theorem fetch_acq_nil:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ log = [] ⇒ ps'.acq = ps.acq
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >> gvs[AllCaseEqs()]
  >> TRY (res_tac >> NO_TAC)
  >> Cases_on ‘l0_res_of out’ >> gvs[AllCaseEqs()]
  >> TRY (qpat_x_assum ‘(λ(ps1,fl). _) _ = _’ mp_tac >> rw[] >> gvs[AllCaseEqs()])
  >> TRY (Cases_on ‘e = E_MFILE’) >> gvs[] >> res_tac >> fs[]
QED

Theorem tail_jnv:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ log = [] ⇒
  (gonef f ps ⇒ gonef f ps') ∧ (jnv h f ps ⇒ jnv h f ps')
Proof
  strip_tac >> drule tail_noeof >> strip_tac >>
  ‘ps'.acq = ps.acq ∧ (∀g. MEM g ps.eof ⇒ MEM g ps'.eof) ∧
   (inb_of ps f = [] ⇒ inb_of ps' f = [])’
    by (qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >> rw[pf_tail_def, AllCaseEqs()] >>
        gvs[] >> drule fetch_eof >> drule fetch_acq_nil >> simp[] >> rpt strip_tac >>
        TRY (metis_tac[]) >>
        drule fetch_inb_nil >> simp[] >> disch_then irule >> fs[inb_of_def]) >>
  gvs[jnv_def, gonef_def]
QED

(* ------------------------------------------------------------------------
   Along the run
   ------------------------------------------------------------------------ *)

Theorem round_split2[local]:
  run_ok lfd pol ifds m w0 ⇒
  ∃rs evs w1 ps1 rdy tevs.
    pacts lfd (rworld lfd pol ifds m w0 k, rstate lfd pol ifds m w0 k)
      (new_actions (log_of m) (rhist lfd pol ifds m w0 k)) = SOME (rs, evs, (w1, ps1)) ∧
    pf_tail lfd pol (ifds (rhist lfd pol ifds m w0 k)) (w1, ps1) =
      SOME (rdy, (rworld lfd pol ifds m w0 (SUC k), rstate lfd pol ifds m w0 (SUC k)),
            rlog lfd pol ifds m w0 k, tevs)
Proof
  strip_tac >> drule prun_round' >>
  disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  gvs[pround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >> metis_tac[]
QED

Theorem round_eof_jnv:
  run_ok lfd pol ifds m w0 ∧ rlog lfd pol ifds m w0 k = [] ⇒
  (gonef f (rstate lfd pol ifds m w0 k) ⇒ gonef f (rstate lfd pol ifds m w0 (SUC k))) ∧
  (jnv h f (rstate lfd pol ifds m w0 k) ⇒
   (jnv h f (rstate lfd pol ifds m w0 (SUC k)) ∨ gonef f (rstate lfd pol ifds m w0 (SUC k))) ∧
   ((∃kk. MEM (Read h kk) (new_actions (log_of m) (rhist lfd pol ifds m w0 k))) ⇒
    gonef f (rstate lfd pol ifds m w0 (SUC k))))
Proof
  strip_tac >> drule (Q.GEN ‘k’ round_split2) >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  gvs[] >> drule pacts_jnv >> strip_tac >> drule tail_jnv >> simp[] >> strip_tac >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* MAIN: a read of f's handle soon, while nothing is fetched, takes f out
   of L1's table *)
Theorem read_eof_gone:
  run_ok lfd pol ifds m w0 ∧ (∀k. n ≤ k ⇒ rlog lfd pol ifds m w0 k = []) ∧
  jnv h f (rstate lfd pol ifds m w0 n) ∧
  MEM (Read h kk) (new_actions (log_of m) (rhist lfd pol ifds m w0 (n + i))) ⇒
  ∃n'. n ≤ n' ∧ ¬MEM f (MAP SND (rstate lfd pol ifds m w0 n').b.tbl)
Proof
  strip_tac >>
  ‘∀d. d ≤ i ⇒ jnv h f (rstate lfd pol ifds m w0 (n + d)) ∨
               gonef f (rstate lfd pol ifds m w0 (n + d))’
    by (Induct >> simp[] >> strip_tac >>
        ‘jnv h f (rstate lfd pol ifds m w0 (n + d)) ∨
         gonef f (rstate lfd pol ifds m w0 (n + d))’ by fs[] >>
        qspecl_then [‘n + d’, ‘h’, ‘f’] mp_tac (Q.GENL [‘k’, ‘h’, ‘f’] round_eof_jnv) >>
        impl_tac >- fs[] >>
        ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC >> strip_tac >> fs[]) >>
  first_x_assum (qspec_then ‘i’ mp_tac) >> simp[] >> strip_tac
  >- (qspecl_then [‘n + i’, ‘h’, ‘f’] mp_tac (Q.GENL [‘k’, ‘h’, ‘f’] round_eof_jnv) >>
      impl_tac >- fs[] >> strip_tac >> qexists_tac ‘SUC (n + i)’ >> simp[] >>
      ‘gonef f (rstate lfd pol ifds m w0 (SUC (n + i)))’
        by (‘i + n = n + i’ by simp[] >> fs[] >> metis_tac[]) >> fs[gonef_def])
  >> qexists_tac ‘n + i’ >> fs[gonef_def]
QED

(* MAIN: the drain (pf_drain), with its end-of-file premise as a read-soon
   fact on the run (async-spike's echo_read_soon_eof's shape) *)
Theorem pf_drain_read:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  S2 lfd pol ifds m w0 ∧ S3w lfd pol ifds m w0 ∧
  (∀n h f. n0 ≤ n ∧ ALOOKUP (rstate lfd pol ifds m w0 n).b.tbl h = SOME f ∧
           MEM f (rstate lfd pol ifds m w0 n).eof ⇒
           ∃i kk. MEM (Read h kk) (new_actions (log_of m) (rhist lfd pol ifds m w0 (n + i)))) ∧
  (∀n. n0 ≤ n ⇒ rlog lfd pol ifds m w0 n = []) ⇒
  ∃n1. ∀n. n1 ≤ n ⇒
       (rstate lfd pol ifds m w0 n).acq = [] ∧
       ∀h f. ALOOKUP (rstate lfd pol ifds m w0 n).b.tbl h = SOME f ⇒
             inb_of (rstate lfd pol ifds m w0 n) f = [] ∧ ¬MEM f (rstate lfd pol ifds m w0 n).eof
Proof
  strip_tac >> irule pf_drain >> simp[] >> qexists_tac ‘n0’ >> simp[] >>
  rpt strip_tac >>
  drule_all round_facts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘ALL_DISTINCT (MAP SND (rstate lfd pol ifds m w0 n).b.tbl) ∧
   ALL_DISTINCT (MAP FST (rstate lfd pol ifds m w0 n).b.tbl)’
    by fs[pown_def, ALL_DISTINCT_APPEND] >>
  ‘∃h. ALOOKUP (rstate lfd pol ifds m w0 n).b.tbl h = SOME f’
    by (fs[MEM_MAP] >> rename1 ‘MEM y _’ >> PairCases_on ‘y’ >> gvs[] >>
        metis_tac[ALOOKUP_ALL_DISTINCT_MEM]) >>
  ‘jnv h f (rstate lfd pol ifds m w0 n)’ by fs[jnv_def] >>
  first_x_assum (qspecl_then [‘n’, ‘h’, ‘f’] mp_tac) >> simp[] >> strip_tac >>
  irule read_eof_gone >> simp[] >> qexistsl [‘h’, ‘i’, ‘kk’] >> simp[]
QED
