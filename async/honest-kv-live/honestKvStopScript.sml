(*
  KV stops writing on an fd whose inbox stays empty (honest-ffi's
  S4w_of_stop premise, for the PF KV run): the M4 side is
  honestKvWritesStopM's kv_m4_writes_stop_all, over every handle that ever
  names f.

  Such a handle's M4 connection has no input once f's inbox stays empty:
  a connection with input is a handle L1 holds on an fd with that input
  (honestEchoL0Stop's conn_input_held), and a handle that names f at some
  round names f at every round where L1 holds it (tbl_ext, run_fresh).

  KV has no global S3w (an invalid request stops KV reading), so S4w at f
  is conditioned on f's inbox emptying once f is no longer fetched (S3f's
  premise, which honestKvPeerValid's kv_S3w_conn gives for a valid peer).

  MAIN: kv_writes_stop, kv_S4w_f.
*)
Theory honestKvStop
Ancestors
  honestKvWritesStopM honestKvReadSoonPF honestL0GenS2 honestKvL0Obl
  honestEchoL0Stop honestL1PFS4w honestL1PFOutLive honestL1PFFlush honestL1PFObl
  honestL1PFLive honestL1PFRefine honestL1PFModel
  asyncHLSimWorld asyncHLModel asyncM4GTrans asyncM4GRounds asyncCore
Libs
  preamble

Overload KV1[local] = “v1of (n2w lfdn) (psk (n2w lfdn) pol KI KS w0)”
Overload KPSK[local] = “psk (n2w lfdn) pol KI KS w0”

(* A handle that names f at round k' names f at every round where L1
   holds it *)
Theorem tbl_same_fd:
  run_ok lfd pol ifds m w0 ∧ run_hyp lfd pol ifds m w0 ∧
  ALOOKUP (rstate lfd pol ifds m w0 k').b.tbl h = SOME f ∧
  ALOOKUP (rstate lfd pol ifds m w0 k).b.tbl h = SOME g ⇒ g = f
Proof
  strip_tac >>
  Cases_on ‘k ≤ k'’
  >- (drule run_tbl_ext >> disch_then (qspecl_then [‘k' − k’, ‘k’] mp_tac) >>
      ‘k + (k' − k) = k'’ by simp[] >> pop_assum SUBST1_TAC >>
      rewrite_tac[tbl_ext_def] >> strip_tac >>
      first_x_assum (qspecl_then [‘h’, ‘f’] mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac
      >- (qpat_x_assum ‘ALOOKUP _ h = SOME g’ mp_tac >>
          qpat_x_assum ‘ALOOKUP _ h = SOME f’ mp_tac >> simp[]) >>
      qpat_x_assum ‘ALOOKUP (rstate _ _ _ _ _ k).b.tbl h = SOME g’ assume_tac >>
      metis_tac[run_fresh]) >>
  drule run_tbl_ext >> disch_then (qspecl_then [‘k − k'’, ‘k'’] mp_tac) >>
  ‘k' + (k − k') = k’ by simp[] >> pop_assum SUBST1_TAC >>
  rewrite_tac[tbl_ext_def] >> strip_tac >>
  first_x_assum (qspecl_then [‘h’, ‘g’] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac
  >- (qpat_x_assum ‘ALOOKUP _ h = SOME g’ mp_tac >>
      qpat_x_assum ‘ALOOKUP _ h = SOME f’ mp_tac >> simp[]) >>
  qpat_x_assum ‘ALOOKUP (rstate _ _ _ _ _ k').b.tbl h = SOME f’ assume_tac >>
  metis_tac[run_fresh]
QED

(* Once f's inbox stays empty, the M4 connection behind any handle that
   ever names f has no input *)
Theorem kv_conn_quiet:
  kv_run lfdn pol w0 ∧
  (∀k. n1 ≤ k ⇒ inb_of (rstate (n2w lfdn) pol KI KS w0 k) f = []) ∧
  ALOOKUP (rstate (n2w lfdn) pol KI KS w0 k').b.tbl h = SOME f ∧
  n1 ≤ k ∧ ALOOKUP (gstate KI KS KV1 k).conns h = SOME cn ⇒
  cn.incoming = []
Proof
  rpt strip_tac >> CCONTR_TAC >>
  ‘run_ok (n2w lfdn) pol KI KS w0’ by fs[kv_run_def] >>
  ‘run_hyp (n2w lfdn) pol KI KS w0’ by metis_tac[kv_run_hyp] >>
  drule kv_gen_run >> strip_tac >>
  drule_then (qspec_then ‘k’ strip_assume_tac) gen_sim >>
  Cases_on ‘hst (n2w lfdn) KI KS KPSK k’ >> rename1 ‘_ = (s2, hs)’ >>
  ‘hs = hs_of (rstate (n2w lfdn) pol KI KS w0 k)’ by fs[] >>
  ‘hsim0 (n2w lfdn) (gstate KI KS KV1 k) (s2, hs_of (rstate (n2w lfdn) pol KI KS w0 k))’
    by fs[hsim_def] >>
  ‘pv_rel (n2w lfdn) (FST (pcm (n2w lfdn) pol KI KS w0 k)) (rstate (n2w lfdn) pol KI KS w0 k) s2’
    by fs[] >>
  drule_all conn_input_held >> strip_tac >>
  ‘g = f’ by metis_tac[tbl_same_fd] >>
  qpat_x_assum ‘g = f’ SUBST_ALL_TAC >>
  qpat_x_assum ‘inb_of _ f ≠ []’ mp_tac >> simp[]
QED

(* MAIN: once f's inbox stays empty, KV eventually writes no bytes on any
   handle naming f (honest-ffi's S4w_of_stop premise) *)
Theorem kv_writes_stop:
  kv_run lfdn pol w0 ∧
  (∀k. n1 ≤ k ⇒ inb_of (rstate (n2w lfdn) pol KI KS w0 k) f = []) ⇒
  ∃n0. ∀k h bs. n0 ≤ k ∧ MEM (Write h bs) (racts (n2w lfdn) pol KI KS w0 k) ∧
         (ALOOKUP (rstate (n2w lfdn) pol KI KS w0 k).b.tbl h = SOME f ∨
          ALOOKUP (rstate (n2w lfdn) pol KI KS w0 (SUC k)).b.tbl h = SOME f) ⇒
         bs = []
Proof
  strip_tac >>
  ‘KV1.listeners = [(n2w lfdn, [])] ∧ KV1.conns = []’ by metis_tac[kv_v1_world] >>
  qspecl_then [‘λh. ∃k'. ALOOKUP (rstate (n2w lfdn) pol KI KS w0 k').b.tbl h = SOME f’,
               ‘KI’, ‘n1’, ‘lfdn’, ‘KV1’] mp_tac
    (Q.GENL [‘P’, ‘ifds’, ‘k0’, ‘lfdn’, ‘s0’] kv_m4_writes_stop_all) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> BETA_TAC >> rpt strip_tac >>
      irule kv_conn_quiet >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      metis_tac[]) >>
  BETA_TAC >> strip_tac >> qexists_tac ‘n0’ >> rpt strip_tac >>
  drule kv_gen_run >> strip_tac >>
  drule_then (qspec_then ‘k’ strip_assume_tac) gen_sim >>
  ‘MEM (Write h bs) (gacts KI KS KV1 k)’
    by (qpat_x_assum ‘MEM _ (racts _ _ _ _ _ _)’ mp_tac >>
        rewrite_tac[gacts_def, racts_def] >>
        qpat_x_assum ‘rhist _ _ _ _ _ k = _’ (fn th => rewrite_tac[th])) >>
  first_x_assum irule >> metis_tac[]
QED

(* MAIN: S4w at f, if f's inbox empties once f is no longer fetched *)
Theorem kv_S4w_f:
  kv_run lfdn pol w0 ∧ qfresh w0 ∧
  (∀n. (∀k. n ≤ k ⇒ ¬fetched_at (n2w lfdn) pol KI KS w0 k f) ⇒
       ∃n'. n ≤ n' ∧ inb_of (rstate (n2w lfdn) pol KI KS w0 n') f = []) ⇒
  S4w (n2w lfdn) pol hw KI KS w0 f
Proof
  strip_tac >>
  ‘run_ok (n2w lfdn) pol KI KS w0’ by fs[kv_run_def] >>
  irule S4w_of_stop >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum ‘∀n. (∀k. _) ⇒ _’ (qspec_then ‘n’ mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
      strip_tac >>
      ‘∀k. n' ≤ k ⇒ inb_of (rstate (n2w lfdn) pol KI KS w0 k) f = []’
        by (rpt strip_tac >> drule run_inb_drop >>
            disch_then (qspecl_then [‘n'’, ‘f’, ‘k − n'’] mp_tac) >>
            impl_tac >- (rpt strip_tac >> qpat_x_assum ‘fetched_at _ _ _ _ _ _ _’ mp_tac >>
                         qpat_x_assum ‘∀k. n ≤ k ⇒ ¬_’ (qspec_then ‘k'’ mp_tac) >>
                         impl_tac >- decide_tac >> simp[]) >>
            strip_tac >> ‘n' + (k − n') = k’ by simp[] >> fs[]) >>
      qspecl_then [‘f’, ‘lfdn’, ‘n'’, ‘pol’, ‘w0’] mp_tac
        (Q.GENL [‘f’, ‘lfdn’, ‘n1’, ‘pol’, ‘w0’] kv_writes_stop) >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
      qexists_tac ‘MAX n n0’ >> simp[] >> rpt strip_tac >>
      first_x_assum irule >> fs[MAX_LE] >> metis_tac[]) >>
  fs[oassm_def, kv_run_def]
QED
