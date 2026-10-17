(*
  The echo stops writing on an fd that is no longer fetched (design/47 D,
  step 3's premise; honest-ffi's S4w_of_stop takes it): once nothing more
  is fetched on f, from some round on every Write on f's handle carries no
  bytes.

  The echo writes in round k + 1 exactly what it read in round k (M4's
  echo_rounds_written_read, per round); a read takes bytes only from a
  connection with input at the round's start (sock_acts_noread); and the
  connection behind f's handle has input only if f's inbox does, which
  stays empty once S3w has emptied it.

  MAIN: echo_writes_stop, and with honest-ffi's S4w_of_stop, echo_S4w.
*)
Theory honestEchoL0Stop
Ancestors
  honestEchoL0Obl honestL1PFObl honestL1PFS4w honestL1PFOutLive honestL1PFFlush honestL1PFLive honestL1PFRefine honestL1PFModel
  honestL1Steps honestL1Model asyncHLSimWorld asyncHLModel asyncM4EchoSafe
  asyncM4Account asyncM4LiveWorld asyncM4GTrans asyncM4GRounds asyncM4EchoRunOk
  asyncM3World ffiSpikeSocketFFI asyncCore
Libs
  preamble

(* ------------------------------------------------------------------------
   L1's handle table: an entry keeps its fd, new entries are fresh
   ------------------------------------------------------------------------ *)

Definition tbl_ext_def:
  tbl_ext lfd ps ps' ⇔
    ps.b.nxt ≤ ps'.b.nxt ∧
    ∀h f. ALOOKUP ps'.b.tbl h = SOME f ⇒
          ALOOKUP ps.b.tbl h = SOME f ∨
          ∃i. ps.b.nxt ≤ i ∧ l1hdln (w2n lfd) i < dimword (:64) ∧ h = l1hdl lfd i
End

Theorem tbl_ext_refl[simp]:
  tbl_ext lfd ps ps
Proof
  simp[tbl_ext_def]
QED

Theorem tbl_ext_trans:
  tbl_ext lfd ps1 ps2 ∧ tbl_ext lfd ps2 ps3 ⇒ tbl_ext lfd ps1 ps3
Proof
  rw[tbl_ext_def] >> res_tac >> fs[] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem tbl_ext_same:
  ps'.b.tbl = ps.b.tbl ∧ ps'.b.nxt = ps.b.nxt ⇒ tbl_ext lfd ps ps'
Proof
  simp[tbl_ext_def]
QED

Theorem ALOOKUP_ADELKEY_SOME[local]:
  ALOOKUP (ADELKEY k l) h = SOME v ⇒ ALOOKUP l h = SOME v
Proof
  simp[ALOOKUP_ADELKEY] >> rw[]
QED

Theorem pdo_tbl_ext:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ tbl_ext lfd ps ps'
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’ >> gvs[]) >>
  TRY (drule l1_close_b >> strip_tac) >>
  TRY (drule l1do_write_tbl >> strip_tac) >>
  gvs[tbl_ext_def, set_inb_def] >> rw[] >>
  gvs[AllCaseEqs()] >> metis_tac[ALOOKUP_ADELKEY_SOME, LESS_EQ_REFL]
QED

Theorem pacts_tbl_ext:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒ tbl_ext lfd ps ps'
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >>
  gvs[] >> PairCases_on ‘ws1’ >> drule pdo_tbl_ext >> strip_tac >>
  first_x_assum drule >> metis_tac[tbl_ext_trans]
QED

Theorem pround_tbl_ext:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ⇒ tbl_ext lfd ps ps'
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> gvs[] >> PairCases_on ‘ws1’ >>
  drule pacts_tbl_ext >> strip_tac >>
  drule pf_tail_tbl >> strip_tac >>
  metis_tac[tbl_ext_trans, tbl_ext_same]
QED

Theorem run_tbl_ext:
  run_ok lfd pol ifds m w0 ⇒
  ∀d k. tbl_ext lfd (rstate lfd pol ifds m w0 k) (rstate lfd pol ifds m w0 (k + d))
Proof
  strip_tac >> Induct >> simp[] >> gen_tac >>
  first_x_assum (qspec_then ‘k’ assume_tac) >>
  drule_then (qspec_then ‘k + d’ strip_assume_tac) prun_step >>
  drule pround_tbl_ext >> strip_tac >>
  ‘k + SUC d = SUC (k + d)’ by simp[] >> metis_tac[tbl_ext_trans]
QED

(* ------------------------------------------------------------------------
   M4: a read takes bytes only from a connection with input
   ------------------------------------------------------------------------ *)

Theorem sock_do_conns_none:
  sock_do s a = SOME (r, s') ∧ ALOOKUP s.conns c = NONE ⇒ ALOOKUP s'.conns c = NONE
Proof
  Cases_on ‘a’ >>
  rw[sock_do_def, sock_accept_def, sock_read_def, sock_write_def, AllCaseEqs()] >>
  gvs[AFUPDKEY_ALOOKUP]
QED

Theorem sock_acts_noread:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ∧
    (∀cn. ALOOKUP s.conns c = SOME cn ⇒ cn.incoming = []) ⇒
    pread_all c (ZIP (acts, rs)) = []
Proof
  Induct >> simp[sock_acts_def] >> rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >>
  gvs[] >> conj_tac
  >- (Cases_on ‘h’ >> simp[pread_def] >> Cases_on ‘r’ >> simp[pread_def] >>
      rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[pread_def] >> rw[] >>
      gvs[sock_do_def, sock_read_def, AllCaseEqs()]) >>
  first_x_assum irule >> qexistsl_tac [‘evs'’, ‘s1’, ‘s'’] >> simp[] >>
  rpt strip_tac >>
  Cases_on ‘ALOOKUP s.conns c’
  >- (drule_all sock_do_conns_none >> simp[]) >>
  drule_all sock_do_conn >> strip_tac >> gvs[] >>
  Cases_on ‘∃k. h = Read c k’ >> gvs[]
QED

Theorem pwritten_all_mem:
  ∀acts rs. MEM (Write c bs) acts ∧ LENGTH rs = LENGTH acts ⇒
            ∃p q. pwritten_all c (ZIP (acts, rs)) = p ++ bs ++ q
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘rs’ >> simp[] >> strip_tac >> gvs[]
  >- (simp[pwritten_def] >> qexistsl_tac [‘[]’, ‘pwritten_all c (ZIP (acts, t))’] >>
      simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [‘pwritten c (h, h') ++ p’, ‘q’] >> simp[]
QED

Theorem hdl_inj_lt:
  hdl lfd i = hdl lfd j ∧ hdln (w2n lfd) i < dimword (:64) ∧
  hdln (w2n lfd) j < dimword (:64) ⇒ i = j
Proof
  rw[hdl_def] >> gvs[hdln_def] >> rw[] >> gvs[] >> every_case_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   The echo, per round: written in round k + 1 = read in round k
   ------------------------------------------------------------------------ *)

Theorem append_cancel[local]:
  a ++ b = d ⇒ a ++ b ++ c = d ++ e ⇒ c = e
Proof
  rw[] >> fs[]
QED

Theorem echo_round_written_read:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  pwritten_all c (ZIP (gacts ifds (srelabel (server lfdn)) s0 (SUC k),
                       gres ifds (srelabel (server lfdn)) s0 (SUC k))) =
  pread_all c (ZIP (gacts ifds (srelabel (server lfdn)) s0 k,
                    gres ifds (srelabel (server lfdn)) s0 k))
Proof
  strip_tac >>
  ‘grun_ok ifds (srelabel (server lfdn)) s0’ by metis_tac[echo_grun_ok] >>
  ‘∀n. pwritten_all c (gperf ifds (srelabel (server lfdn)) s0 (SUC n)) =
       pread_all c (gperf ifds (srelabel (server lfdn)) s0 n)’
    by (gen_tac >>
        ‘bytes_written_to c (FLAT (GENLIST (grounds_events ifds (srelabel (server lfdn)) s0)
                                     (SUC n))) =
         bytes_read_from c (FLAT (GENLIST (grounds_events ifds (srelabel (server lfdn)) s0) n))’
          by metis_tac[echo_rounds_written_read] >>
        gvs[bytes_written_to_rounds, bytes_read_from_rounds]) >>
  first_assum (qspec_then ‘SUC k’ mp_tac) >>
  first_x_assum (qspec_then ‘k’ mp_tac) >>
  simp[gperf_SUC, MAP_APPEND, FLAT_APPEND] >>
  metis_tac[append_cancel]
QED

(* ------------------------------------------------------------------------
   The PF echo
   ------------------------------------------------------------------------ *)

(* Through the simulation: an M4 connection with input is a handle L1
   holds, on an fd whose inbox is that input *)
Theorem conn_input_held:
  hsim0 lfd s1 (s2, hs_of ps) ∧ pv_rel lfd cm ps s2 ∧
  ALOOKUP s1.conns h = SOME cn ∧ cn.incoming ≠ [] ⇒
  ∃g. ALOOKUP ps.b.tbl h = SOME g ∧ inb_of ps g ≠ []
Proof
  rw[hsim0_def] >> gvs[hs_of_def] >>
  ‘MEM h (MAP FST s1.conns)’
    by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  gvs[MEM_GENLIST] >> rename1 ‘j < LENGTH s2.clients’ >>
  ‘(EL j s2.clients).incoming ≠ []’ by (res_tac >> gvs[]) >>
  ‘LENGTH s2.clients + 1 < dimword (:64)’ by gvs[] >>
  ‘∀i. i < LENGTH s2.clients ⇒ hdln (w2n lfd) i < dimword (:64)’
    by (rpt strip_tac >> qpat_x_assum ‘LENGTH s2.clients + 1 < _’ mp_tac >>
        qpat_x_assum ‘i < _’ mp_tac >> rpt (pop_assum kall_tac) >> rw[hdln_def]) >>
  Cases_on ‘ALOOKUP ps.b.tbl (hdl lfd j)’ >> simp[]
  >- (Cases_on ‘j < ps.b.nxt’ >- (res_tac >> gvs[]) >>
      gvs[pv_rel_def] >>
      ‘MEM j (MAP (cl cm) ps.acq)’
        by (qpat_x_assum ‘_ = MAP (cl cm) ps.acq’ (SUBST1_TAC o SYM) >>
            simp[MEM_GENLIST] >> qexists_tac ‘j − ps.b.nxt’ >> simp[]) >>
      gvs[MEM_MAP] >> res_tac >> gvs[]) >>
  rename1 ‘ALOOKUP ps.b.tbl (hdl lfd j) = SOME g’ >>
  qpat_assum ‘∀h' f. ALOOKUP ps.b.tbl h' = SOME f ⇔ _’ (drule o iffLR) >> strip_tac >>
  ‘j' < LENGTH s2.clients’ by simp[] >>
  ‘j' = j’ by (irule hdl_inj_lt >> qexists_tac ‘lfd’ >> simp[]) >>
  qpat_x_assum ‘j' = j’ SUBST_ALL_TAC >>
  qexists_tac ‘g’ >> conj_tac >- (qexists_tac ‘j’ >> simp[]) >>
  drule_all pv_rel_tbl >> strip_tac >>
  ‘cl cm g = j’ by fs[] >> fs[]
QED

(* At a round whose start has f's inbox empty, the M4 connection behind a
   handle that holds f then or later has no input *)
Theorem echo_conn_quiet:
  echo_run lfdn pol w0 ∧
  inb_of (rstate (n2w lfdn) pol EI ES w0 k) f = [] ∧ k ≤ k' ∧
  ALOOKUP (rstate (n2w lfdn) pol EI ES w0 k').b.tbl h = SOME f ⇒
  ∀cn. ALOOKUP (gstate EI ES V1 k).conns h = SOME cn ⇒ cn.incoming = []
Proof
  rpt strip_tac >> CCONTR_TAC >>
  drule_then (qspec_then ‘k’ strip_assume_tac) echo_sim >>
  ‘run_ok (n2w lfdn) pol EI ES w0’ by fs[echo_run_def] >>
  ‘run_hyp (n2w lfdn) pol EI ES w0’ by metis_tac[echo_run_hyp] >>
  Cases_on ‘hst (n2w lfdn) EI ES PSK k’ >> rename1 ‘_ = (s2, hs)’ >>
  ‘hs = hs_of (rstate (n2w lfdn) pol EI ES w0 k)’ by fs[] >>
  ‘hsim0 (n2w lfdn) (gstate EI ES V1 k) (s2, hs_of (rstate (n2w lfdn) pol EI ES w0 k))’
    by fs[hsim_def] >>
  ‘pv_rel (n2w lfdn) (FST (pcm (n2w lfdn) pol EI ES w0 k)) (rstate (n2w lfdn) pol EI ES w0 k) s2’
    by fs[] >>
  drule_all conn_input_held >> strip_tac >>
  ‘tbl_ext (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 k) (rstate (n2w lfdn) pol EI ES w0 k')’
    by (drule run_tbl_ext >> disch_then (qspecl_then [‘k' − k’, ‘k’] mp_tac) >> simp[]) >>
  pop_assum (strip_assume_tac o REWRITE_RULE [tbl_ext_def]) >>
  qpat_x_assum ‘ALOOKUP (rstate _ _ _ _ _ k').b.tbl h = SOME f’
    (fn th => first_x_assum (strip_assume_tac o C MATCH_MP th))
  >- (‘g = f’ by (qpat_x_assum ‘ALOOKUP (rstate _ _ _ _ _ k).b.tbl h = SOME g’ mp_tac >>
                  qpat_x_assum ‘ALOOKUP (rstate _ _ _ _ _ k).b.tbl h = SOME f’ mp_tac >>
                  rpt (pop_assum kall_tac) >> simp[]) >>
      qpat_x_assum ‘g = f’ SUBST_ALL_TAC >>
      qpat_x_assum ‘inb_of _ f ≠ []’ mp_tac >>
      qpat_x_assum ‘inb_of _ f = []’ (fn th => REWRITE_TAC [th])) >>
  qpat_x_assum ‘h = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  drule_all run_fresh >> simp[]
QED

(* MAIN: once f is no longer fetched, the echo eventually writes no bytes
   on f's handle (honest-ffi's S4w_of_stop premise: a handle naming f at
   the round's start or end) *)
Theorem echo_writes_stop:
  echo_run lfdn pol w0 ∧
  (∀k. n ≤ k ⇒ ¬fetched_at (n2w lfdn) pol EI ES w0 k f) ⇒
  ∃n0. n ≤ n0 ∧
       ∀k h bs. n0 ≤ k ∧ MEM (Write h bs) (racts (n2w lfdn) pol EI ES w0 k) ∧
         (ALOOKUP (rstate (n2w lfdn) pol EI ES w0 k).b.tbl h = SOME f ∨
          ALOOKUP (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.tbl h = SOME f) ⇒
         bs = []
Proof
  strip_tac >> drule echo_S3w >> simp[S3w_def, GSYM fetched_at_def] >>
  disch_then (qspecl_then [‘n’, ‘f’] mp_tac) >> simp[] >> strip_tac >>
  rename1 ‘inb_of (rstate _ _ _ _ _ n1) f = []’ >>
  ‘run_ok (n2w lfdn) pol EI ES w0’ by fs[echo_run_def] >>
  ‘∀k. n1 ≤ k ⇒ inb_of (rstate (n2w lfdn) pol EI ES w0 k) f = []’
    by (rpt strip_tac >> drule run_inb_drop >>
        disch_then (qspecl_then [‘n1’, ‘f’, ‘k − n1’] mp_tac) >> simp[]) >>
  qexists_tac ‘SUC n1’ >> simp[] >> rpt gen_tac >> strip_tac >>
  ‘∃k0. k = SUC k0 ∧ n1 ≤ k0’ by (qexists_tac ‘k − 1’ >> simp[]) >>
  qpat_x_assum ‘k = SUC k0’ SUBST_ALL_TAC >>
  ‘inb_of (rstate (n2w lfdn) pol EI ES w0 k0) f = []’ by simp[] >>
  ‘∃k'. k0 ≤ k' ∧ ALOOKUP (rstate (n2w lfdn) pol EI ES w0 k').b.tbl h = SOME f’
    by (first_assum (irule_at Any) >> simp[]) >>
  ‘∀cn. ALOOKUP (gstate EI ES V1 k0).conns h = SOME cn ⇒ cn.incoming = []’
    by metis_tac[echo_conn_quiet] >>
  ‘lfdn < dimword (:64)’ by fs[echo_run_def] >>
  ‘V1.listeners = [(n2w lfdn, [])] ∧ V1.conns = []’ by simp[v1of_def] >>
  ‘grun_ok EI ES V1’ by (irule echo_grun_ok >> simp[]) >>
  drule_then (qspec_then ‘SUC k0’ strip_assume_tac) echo_sim >>
  ‘MEM (Write h bs) (gacts EI ES V1 (SUC k0))’ by gvs[gacts_def, racts_def] >>
  drule_then (qspec_then ‘SUC k0’ assume_tac) LENGTH_gres >>
  drule_all pwritten_all_mem >> strip_tac >>
  drule_then (qspec_then ‘k0’ strip_assume_tac) grun_ok_sock_acts >>
  ‘pread_all h (ZIP (gacts EI ES V1 k0, gres EI ES V1 k0)) = []’
    by metis_tac[sock_acts_noread] >>
  ‘pwritten_all h (ZIP (gacts EI ES V1 (SUC k0), gres EI ES V1 (SUC k0))) =
   pread_all h (ZIP (gacts EI ES V1 k0, gres EI ES V1 k0))’
    by (irule echo_round_written_read >> simp[]) >>
  gvs[]
QED

(* MAIN: the PF echo meets S4w on every fd (honest-ffi's S4w_of_stop) *)
Theorem echo_S4w:
  echo_run lfdn pol w0 ∧ qfresh w0 ⇒ S4w (n2w lfdn) pol hw EI ES w0 f
Proof
  strip_tac >> irule S4w_of_stop >> conj_tac
  >- (rpt strip_tac >> drule_all echo_writes_stop >> simp[])
  >> fs[oassm_def, echo_run_def]
QED
