(*
  The proxy's L1 run never fails and its channel count stays below
  2^64 - 1 (proxy_l1_total): the run hypotheses of e1_start's divergence
  (proxy_main_div_spec) and of the claim, from honestL1EPTotal's
  conditions on each action, as moonshotClientTotal does for the client.

  Unlike the client, the proxy polls its listener, so L1 accepts
  connections and the channel count is not the handle count.  The
  connect accounting is one lemma (ecm_round): the channel count is the
  handles issued plus the accepted fds not yet handed out (at most one).
  A failed connect (EConnected NONE) takes no handle and no channel.

  At each round's start (pinv): the handles issued are one per pair plus
  one per pair with a backend; the pairs stay within cbound / 2, so the
  handles within cbound; each pair's handles were issued, its front has
  no connect entry, its backend none once it has answered a read, and
  bytes for the backend wait only once it has; a ready handle with a
  connect entry was refused.  So its writes go to handles L1 holds, and
  the accept guard (2 * pairs + 2 ≤ cbound) bounds the handles.
*)
Theory proxyTotal
Ancestors
  moonshotProxy moonshotClientSpec honestL1EPTotal honestL1EPRefine honestL1EPModel
  honestL1PFModel honestL1Model endpointHLModel asyncCore asyncHLModel asyncM3World
  honestL1PFRefine honestL0Rely
Libs
  preamble

(* ------------------------------------------------------------------------
   E1: the handles a round issues and its channel count
   ------------------------------------------------------------------------ *)

(* A result's new handle: an accept's or a connect's *)
Definition rhdl_def:
  rhdl (EAccepted (SOME h)) = [h : word64] ∧
  rhdl (EConnected (SOME h)) = [h] ∧
  rhdl (EAccepted NONE) = [] ∧
  rhdl (EConnected NONE) = [] ∧
  rhdl (EGot x) = [] ∧
  rhdl (EWrote k) = [] ∧
  rhdl ERefused = [] ∧
  rhdl (ELvl l) = []
End

(* The result's constructor follows the action's *)
Definition rkind_def:
  rkind (EAccept l) r = (∃x. r = EAccepted x) ∧
  rkind (EConnect p) r = (∃x. r = EConnected x) ∧
  rkind (ERead h n) r = ((∃x. r = EGot x) ∨ r = ERefused) ∧
  rkind (EWrite h bs) r = (∃k. r = EWrote k) ∧
  rkind (ELevel h) r = (∃l. r = ELvl l)
End

Theorem edo_rkind:
  edo lfd pol (wl, es) act = SOME (r, ws', evs) ⇒ rkind act r
Proof
  Cases_on ‘act’ >> simp[edo_def, AllCaseEqs()] >> rw[] >> gvs[rkind_def] >>
  TRY (PairCases_on ‘z’) >> gvs[rkind_def] >> every_case_tac >> simp[]
QED

Theorem rhdl_conn:
  (∀x. r ≠ EAccepted x) ⇒ rhdl r = conn_hdls [r]
Proof
  Cases_on ‘r’ >> simp[rhdl_def, conn_hdls_def] >> Cases_on ‘o'’ >> simp[rhdl_def, conn_hdls_def]
QED

(* Only an accept hands out an accepted fd *)
Theorem edo_acq_same:
  edo lfd pol (wl, es) act = SOME (r, (wl', es'), evs) ∧ (∀l. act ≠ EAccept l) ⇒
  es'.p.acq = es.p.acq
Proof
  Cases_on ‘act’ >> simp[edo_def, AllCaseEqs()] >> rw[] >> gvs[ec_del_def] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  rpt (qpat_x_assum ‘pdo _ _ _ = _’ mp_tac) >>
  simp[pdo_def, AllCaseEqs()] >> rw[] >> gvs[] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >> gvs[]
QED

(* An action's handles, and the handles issued plus the accepted fds
   waiting: a connect's handle adds one, an accept moves one fd from the
   queue to a handle *)
Theorem edo_hdls:
  edo lfd pol (wl, es) act = SOME (r, (wl', es'), evs) ⇒
  es'.p.b.nxt = es.p.b.nxt + LENGTH (rhdl r) ∧
  (∀hd. MEM hd (rhdl r) ⇒ hd = hdl lfd es.p.b.nxt) ∧
  es'.p.b.nxt + LENGTH es'.p.acq = es.p.b.nxt + LENGTH es.p.acq + LENGTH (conn_hdls [r])
Proof
  strip_tac >> Cases_on ‘∃l. act = EAccept l’
  >- (gvs[edo_def] >> PairCases_on ‘z’ >> gvs[pdo_def, AllCaseEqs()] >>
      simp[rhdl_def, conn_hdls_def, l1hdl_hdl]) >>
  ‘rhdl r = conn_hdls [r]’
    by (irule rhdl_conn >> drule edo_rkind >> rpt strip_tac >> Cases_on ‘act’ >> gvs[rkind_def]) >>
  ‘∀l. act ≠ EAccept l’ by metis_tac[] >>
  drule_all edo_nxt >> drule_all edo_acq_same >> simp[]
QED

Theorem eacts_hdls:
  ∀acts wl es rs evs wl' es'.
    eacts lfd pol (wl, es) acts = SOME (rs, evs, (wl', es')) ⇒
    es'.p.b.nxt = es.p.b.nxt + LENGTH (FLAT (MAP rhdl rs)) ∧
    (∀hd. MEM hd (FLAT (MAP rhdl rs)) ⇒ ∃j. es.p.b.nxt ≤ j ∧ j < es'.p.b.nxt ∧ hd = hdl lfd j) ∧
    es'.p.b.nxt + LENGTH es'.p.acq = es.p.b.nxt + LENGTH es.p.acq + LENGTH (conn_hdls rs)
Proof
  Induct >> simp[eacts_def, conn_hdls_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rename1 ‘edo _ _ _ _ = SOME (r, ws1, _)’ >>
  PairCases_on ‘ws1’ >> drule edo_hdls >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  ONCE_REWRITE_TAC[conn_hdls_cons] >> simp[] >> rw[]
  >- (first_x_assum drule >> strip_tac >> qexists_tac ‘es.p.b.nxt’ >> simp[] >>
      Cases_on ‘rhdl r’ >> gvs[])
  >> first_x_assum drule >> strip_tac >> qexists_tac ‘j’ >> simp[]
QED

(* The fetch queues one fd per accepted connection, and only while the
   queue is empty *)
Theorem pf_fetch_acqn:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒
    LENGTH ps'.acq = LENGTH ps.acq + LENGTH (FILTER (λx. ∃g. x = FConn g) log) ∧
    (LENGTH ps.acq ≤ 1 ⇒ LENGTH ps'.acq ≤ 1)
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[]
  >- (first_x_assum drule >> simp[])
  >- (first_x_assum drule >> simp[]) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  gvs[AllCaseEqs(), wants_input_def, set_inb_def] >> every_case_tac >> gvs[]
QED

Theorem settle_fds_p:
  ∀fs w es w' es' evs. settle_fds fs (w, es) = SOME ((w', es'), evs) ⇒ es'.p = es.p
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >> rw[AllCaseEqs()] >>
  first_x_assum drule >> every_case_tac >> simp[]
QED

Theorem etail_acqn:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, evs) ⇒
  LENGTH es'.p.acq = LENGTH es.p.acq + LENGTH (FILTER (λx. ∃g. x = FConn g) log) ∧
  (LENGTH es.p.acq ≤ 1 ⇒ LENGTH es'.p.acq ≤ 1)
Proof
  simp[etail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule settle_fds_p >> drule pf_fetch_acqn >>
  simp[promote_def, apply_early_def]
QED

(* The connect accounting: the channel count is the handles issued plus
   the accepted fds not yet handed out.  A round adds a channel per
   connect handle and per accepted fd; an accept moves an fd from the
   queue to a handle *)
Theorem ecm_round:
  erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ∧
  eacts lfd pol ws (new_actions (log_of m) h) = SOME (rs, aevs, ws1) ∧
  etail lfd pol (ifds h) ws1 = SOME (rdy, ws2, log, tevs) ∧
  (SND ws2).p.b.nxt = (SND ws1).p.b.nxt ∧
  SND (ecm lfd pol ifds m w0 n) = (SND ws).p.b.nxt + LENGTH (SND ws).p.acq ⇒
  SND (ecm lfd pol ifds m w0 (SUC n)) = (SND ws2).p.b.nxt + LENGTH (SND ws2).p.acq
Proof
  strip_tac >>
  ‘erounds lfd pol ifds m (w0, einit) (SUC n) =
     SOME (h ++ [ssnap rdy rs], ws2, evs ++ (aevs ++ tevs), logs ++ [log])’
    by simp[erounds_def, eround_def] >>
  drule erounds_logs >> strip_tac >>
  ‘LENGTH logs = n’ by gvs[] >>
  ‘elog lfd pol ifds m w0 n = log’
    by (qpat_x_assum ‘erounds _ _ _ _ _ (SUC n) = _’ mp_tac >>
        simp[elog_def, EL_APPEND2]) >>
  ‘econ lfd pol ifds m w0 n = rfds (SND ws1) rs’ by simp[econ_def, eacts_of_def] >>
  PairCases_on ‘ws’ >> PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >> fs[] >>
  drule eacts_hdls >> strip_tac >> drule etail_acqn >> strip_tac >>
  simp[ecm_SUC, ecm1_def] >> pairarg_tac >> fs[] >>
  Cases_on ‘arrs lfd (cnew k (rfds ws11 rs) ++ cm, k + LENGTH (rfds ws11 rs)) log’ >>
  PairCases_on ‘r’ >> drule arrs_count >> fs[rfds_length] >> strip_tac >> gvs[]
QED

Theorem conn_hdls_le:
  ∀rs. LENGTH (conn_hdls rs) ≤ LENGTH (FLAT (MAP rhdl rs))
Proof
  Induct >> simp[conn_hdls_def] >> gen_tac >> ONCE_REWRITE_TAC[conn_hdls_cons] >>
  Cases_on ‘h’ >> simp[conn_hdls_def, rhdl_def] >>
  Cases_on ‘o'’ >> simp[conn_hdls_def, rhdl_def]
QED

(* The accepted fds not yet handed out: at most one *)
Theorem erounds_acq:
  ∀n h ws evs logs.
    erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒ LENGTH (SND ws).p.acq ≤ 1
Proof
  Induct >- simp[erounds_def, einit_def, pinit_def] >>
  simp[erounds_def, eround_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  PairCases_on ‘ws'’ >> PairCases_on ‘ws1’ >> PairCases_on ‘ws’ >> gvs[] >>
  drule eacts_hdls >> strip_tac >>
  ‘LENGTH ws11.p.acq ≤ 1’ suffices_by (strip_tac >> drule etail_acqn >> simp[]) >>
  qspec_then ‘rs’ assume_tac conn_hdls_le >> gvs[]
QED

Theorem edo_accept_ctbl:
  edo lfd pol (wl, es) (EAccept l) = SOME (r, (wl', es'), evs) ⇒ es'.ctbl = es.ctbl
Proof
  simp[edo_def] >> strip_tac >> PairCases_on ‘z’ >> gvs[]
QED

(* An accepted handle is new and has no connect entry at the actions' end *)
Theorem eacts_accepted:
  ∀acts wl es rs evs wl' es'.
    ebund lfd wl es ∧ eacts lfd pol (wl, es) acts = SOME (rs, evs, (wl', es')) ∧
    es'.p.b.nxt + 1 < dimword (:64) ⇒
    ∀hd. MEM (EAccepted (SOME hd)) rs ⇒ ALOOKUP es'.ctbl hd = NONE
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rename1 ‘edo _ _ _ act = SOME (r, ws1, _)’ >> PairCases_on ‘ws1’ >>
  ‘ebund lfd ws10 ws11’ by (irule edo_ebund >> rpt (first_assum (irule_at Any))) >>
  drule edo_hdls >> strip_tac >>
  drule eacts_hdls >> strip_tac >>
  rpt strip_tac >> gvs[]
  >- (‘∃l. act = EAccept l’
        by (drule edo_rkind >> Cases_on ‘act’ >> simp[rkind_def]) >>
      ‘hd = hdl lfd es.p.b.nxt ∧ ws11.p.b.nxt = es.p.b.nxt + 1’
        by (qpat_x_assum ‘∀hd'. MEM hd' (rhdl _) ⇒ _’ (qspec_then ‘hd’ mp_tac) >>
            qpat_x_assum ‘ws11.p.b.nxt = _’ mp_tac >> simp[rhdl_def]) >>
      ‘es.p.b.nxt + 1 < dimword (:64)’
        by (qpat_x_assum ‘_ < 18446744073709551616’ mp_tac >> simp[rhdl_def]) >>
      ‘ws11.ctbl = es.ctbl’
        by (qpat_x_assum ‘act = _’ SUBST_ALL_TAC >> drule edo_accept_ctbl >> simp[]) >>
      ‘eown lfd es’ by (qpat_x_assum ‘ebund lfd wl es’ mp_tac >> simp[ebund_def] >> strip_tac) >>
      ‘ALOOKUP ws11.ctbl (hdl lfd es.p.b.nxt) = NONE’
        by (qpat_x_assum ‘ws11.ctbl = _’ SUBST1_TAC >>
            Cases_on ‘ALOOKUP es.ctbl (hdl lfd es.p.b.nxt)’ >> simp[] >>
            drule eown_ciss >> rewrite_tac[ciss_def] >> disch_then drule >> strip_tac >>
            ‘i = es.p.b.nxt’ by (irule hdl_11 >> simp[] >> qexists_tac ‘lfd’ >> simp[]) >>
            qpat_x_assum ‘i < es.p.b.nxt’ mp_tac >> simp[]) >>
      qpat_x_assum ‘hd = _’ SUBST_ALL_TAC >>
      irule eacts_ctbl_none >>
      qexistsl [‘acts’, ‘ws11’, ‘evs'’, ‘pol’, ‘rs'’, ‘ws10’, ‘wl'’] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  first_x_assum (qspecl_then [‘ws10’, ‘ws11’, ‘rs'’, ‘evs'’, ‘wl'’, ‘es'’] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_x_assum ‘es'.p.b.nxt = _’ SUBST1_TAC >>
      qpat_x_assum ‘_ < 18446744073709551616’ mp_tac >> simp[]) >>
  disch_then drule >> simp[]
QED

(* ------------------------------------------------------------------------
   The proxy's pairs
   ------------------------------------------------------------------------ *)

(* The handles a pair holds: its front and, once connected, its backend *)
Definition pcnt_def:
  pcnt p = if p.bh = NONE then 1n else 2
End

Definition pcount_def:
  pcount pc = SUM (MAP pcnt pc)
End

(* Pair p's handles were issued (Kp); its front has no connect entry (Gp),
   nor its backend once it has answered a read; bytes wait for the backend
   only once it has *)
Definition pok_def:
  pok (Kp : word64 -> bool) (Gp : word64 -> bool) p ⇔
    Kp p.fh ∧ Gp p.fh ∧
    (∀c. p.bh = SOME c ⇒ Kp c ∧ c ≠ p.fh ∧ (p.bup ⇒ Gp c)) ∧
    (p.bh = NONE ⇒ ¬p.bup) ∧ (p.fq ≠ [] ⇒ p.bup)
End

(* A pair's actions after the Levels (pone), as the update needs them *)
Definition pact1_def:
  pact1 b (R : word64 -> bool) p0 x ⇔
    (x = EConnect b ∧ p0.bh = NONE) ∨
    (∃bs. x = EWrite p0.fh bs) ∨
    (∃c bs. x = EWrite c bs ∧ p0.bh = SOME c ∧ p0.fq ≠ []) ∨
    (x = ERead p0.fh pread ∧ p0.bup ∧ p0.bh ≠ NONE) ∨
    (∃c. x = ERead c pread ∧ p0.bh = SOME c ∧ c ∈ R)
End

Definition pact_def:
  pact lfd b R pc i x ⇔
    x = EAccept lfd ∨
    i < LENGTH pc ∧ ((∃h. x = ELevel h) ∨ pact1 b R (EL i pc) x)
End

Theorem pacts_mem:
  MEM (i, x) (pacts lfd b hw st R) ⇒ pact lfd b R st.pc i x
Proof
  simp[moonshotProxyTheory.pacts_def, pall_def, MEM_FLAT, MEM_GENLIST, PULL_EXISTS, MEM_MAP] >>
  rw[] >>
  gvs[pact_def, pact1_def, plevels_def, MEM_MAP, pone_def, pconnects_def, pwrites_def,
      preads_def, AllCaseEqs()] >>
  every_case_tac >> gvs[]
QED

(* What a result of x tells the update (K0: the handles issued at the
   round's start; K', G': at its end) *)
Definition rok_def:
  rok (K0 : word64 -> bool) K' G' (R : word64 -> bool) x r ⇔
    rkind x r ∧
    (∀hd. MEM hd (rhdl r) ⇒ K' hd ∧ ¬K0 hd) ∧
    (∀hd. r = EAccepted (SOME hd) ⇒ G' hd) ∧
    (∀hd n y. x = ERead hd n ∧ r = EGot y ∧ K0 hd ∧ hd ∈ R ⇒ G' hd)
End

(* One result on its pair: p is pair p0 of the round's start, updated *)
Theorem pres_ok:
  pok K' G' p ∧ pok K0 G0 p0 ∧ pact1 b R p0 x ∧ rok K0 K' G' R x r ∧
  p.fh = p0.fh ∧ (p0.bup ⇒ p.bup) ∧ (∀c. p0.bh = SOME c ⇒ p.bh = SOME c) ∧
  (∀a. x = EConnect a ⇒ p.bh = NONE) ⇒
  pok K' G' (pres p x r) ∧ pcnt (pres p x r) = pcnt p + LENGTH (rhdl r) ∧
  (pres p x r).fh = p0.fh ∧ (p0.bup ⇒ (pres p x r).bup) ∧
  (∀c. p0.bh = SOME c ⇒ (pres p x r).bh = SOME c) ∧
  ((∀a. x ≠ EConnect a) ⇒ (pres p x r).bh = p.bh)
Proof
  strip_tac >>
  qpat_x_assum ‘rok _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [rok_def]) >>
  qpat_x_assum ‘pact1 _ _ _ _’ (strip_assume_tac o REWRITE_RULE [pact1_def]) >>
  gvs[rkind_def]
  >- (rename1 ‘EConnected oc’ >> Cases_on ‘oc’ >>
      gvs[pres_def, rhdl_def, pcnt_def, pok_def] >> CCONTR_TAC >> gvs[])
  >- gvs[pres_def, rhdl_def, pcnt_def, pok_def]
  >- (‘c ≠ p.fh’ by (gvs[pok_def] >> metis_tac[]) >>
      gvs[pres_def, rhdl_def, pcnt_def, pok_def] >> Cases_on ‘p.fq’ >> gvs[])
  >- (gvs[pres_def, rhdl_def, pcnt_def, pok_def] >> every_case_tac >> gvs[rhdl_def])
  >- gvs[pres_def, rhdl_def, pcnt_def, pok_def]
  >- (‘c ≠ p.fh’ by (gvs[pok_def] >> metis_tac[]) >>
      gvs[pres_def, rhdl_def, pcnt_def, pok_def] >> every_case_tac >> gvs[rhdl_def]) >>
  ‘c ≠ p.fh’ by (gvs[pok_def] >> metis_tac[]) >>
  gvs[pres_def, rhdl_def, pcnt_def, pok_def]
QED

(* One step of pupd *)
Definition pupd1_def:
  pupd1 st (i : num, x) r =
    case (x, r) of
    | (ELevel h, ELvl l) => st with lv := (h, l) :: st.lv
    | (EAccept _, EAccepted (SOME hd)) => st with pc := st.pc ++ [pnew hd]
    | (EAccept _, _) => st
    | _ => st with pc := LUPDATE (pres (EL i st.pc) x r) i st.pc
End

Theorem pupd_cons:
  pupd st ((i, x) :: xs) (r :: rs) = pupd (pupd1 st (i, x) r) xs rs
Proof
  simp[pupd_def, pupd1_def]
QED

Theorem pupd1_pact1:
  pact1 b R p0 x ⇒ pupd1 st (i, x) r = st with pc := LUPDATE (pres (EL i st.pc) x r) i st.pc
Proof
  rw[pact1_def] >> Cases_on ‘r’ >> simp[pupd1_def]
QED

Theorem pcount_APPEND[simp]:
  pcount (l1 ++ l2) = pcount l1 + pcount l2
Proof
  simp[pcount_def, SUM_APPEND]
QED

Theorem pcount_LUPDATE:
  ∀pc i q. i < LENGTH pc ⇒ pcount (LUPDATE q i pc) + pcnt (EL i pc) = pcount pc + pcnt q
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘i’ >> simp[LUPDATE_def, pcount_def] >>
  strip_tac >> first_x_assum (qspecl_then [‘n’, ‘q’] mp_tac) >> simp[pcount_def]
QED

Theorem EVERY_LUPDATE_IMP:
  EVERY P l ∧ (i < LENGTH l ⇒ P x) ⇒ EVERY P (LUPDATE x i l)
Proof
  rw[EVERY_EL, EL_LUPDATE] >> rw[] >> gvs[]
QED

(* Pair p at a round's end against p0 at its start *)
Definition prel1_def:
  prel1 p0 p ⇔ p.fh = p0.fh ∧ (p0.bup ⇒ p.bup) ∧ ∀c. p0.bh = SOME c ⇒ p.bh = SOME c
End

Definition prel_def:
  prel pc0 pc ⇔ LENGTH pc0 ≤ LENGTH pc ∧ ∀j. j < LENGTH pc0 ⇒ prel1 (EL j pc0) (EL j pc)
End

(* One result on the state: the handle count, the pairs, and pair i's
   relation to the round's start *)
Theorem pupd1_step:
  pact lfd b R pc0 i x ∧ rok K0 K' G' R x r ∧ EVERY (pok K0 G0) pc0 ∧
  LENGTH pc0 ≤ LENGTH st.pc ∧ EVERY (pok K' G') st.pc ∧
  (i < LENGTH pc0 ⇒ prel1 (EL i pc0) (EL i st.pc)) ∧
  (∀a. x = EConnect a ⇒ (EL i st.pc).bh = NONE) ⇒
  pcount (pupd1 st (i, x) r).pc = pcount st.pc + LENGTH (rhdl r) ∧
  LENGTH st.pc ≤ LENGTH (pupd1 st (i, x) r).pc ∧
  LENGTH (pupd1 st (i, x) r).pc ≤ LENGTH st.pc + (if ∃l. x = EAccept l then 1 else 0) ∧
  EVERY (pok K' G') (pupd1 st (i, x) r).pc ∧
  (∀j. j < LENGTH st.pc ∧ j ≠ i ⇒ EL j (pupd1 st (i, x) r).pc = EL j st.pc) ∧
  (i < LENGTH pc0 ⇒ prel1 (EL i pc0) (EL i (pupd1 st (i, x) r).pc)) ∧
  ((∀a. x ≠ EConnect a) ∧ i < LENGTH st.pc ⇒ (EL i (pupd1 st (i, x) r).pc).bh = (EL i st.pc).bh)
Proof
  REWRITE_TAC [prel1_def] >> strip_tac >>
  qpat_x_assum ‘pact _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [pact_def])
  >- (* the accept *)
     (gvs[rok_def, rkind_def, rhdl_def] >> rename1 ‘EAccepted oh’ >> Cases_on ‘oh’ >>
      simp[pupd1_def, rhdl_def] >>
      simp[pcount_def, pcnt_def, pnew_def, EL_APPEND1, pok_def] >> rw[EL_APPEND1] >>
      gvs[rhdl_def])
  >- (* a Level *)
     (gvs[rok_def, rkind_def] >> simp[pupd1_def, rhdl_def]) >>
  (* a pair's action *)
  drule_then (fn th => REWRITE_TAC [th]) pupd1_pact1 >> simp[] >>
  ‘i < LENGTH st.pc’ by simp[] >>
  ‘pok K' G' (EL i st.pc) ∧ pok K0 G0 (EL i pc0)’ by gvs[EVERY_EL] >>
  mp_tac (Q.INST [‘p’ |-> ‘EL i st.pc’, ‘p0’ |-> ‘EL i pc0’] (SPEC_ALL pres_ok)) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_then (qspec_then ‘pres (EL i st.pc) x r’ assume_tac) pcount_LUPDATE >>
  rpt conj_tac >>
  FIRST [simp[] >> NO_TAC, irule EVERY_LUPDATE_IMP >> simp[] >> NO_TAC,
         Cases_on ‘∃l. x = EAccept l’ >> simp[] >> NO_TAC, simp[EL_LUPDATE]]
QED

(* The pairs a round's remaining actions connect, and how many accepts it has *)
Definition cidx_def:
  cidx (xs : (num # eact) list) = MAP FST (FILTER (λjx. ∃a. SND jx = EConnect a) xs)
End

Definition nacc_def:
  nacc (xs : (num # eact) list) = LENGTH (FILTER (λjx. ∃l. SND jx = EAccept l) xs)
End

Theorem prel_step:
  prel pc0 pc ∧ LENGTH pc ≤ LENGTH pc' ∧ (∀j. j < LENGTH pc ∧ j ≠ i ⇒ EL j pc' = EL j pc) ∧
  (i < LENGTH pc0 ⇒ prel1 (EL i pc0) (EL i pc')) ⇒
  prel pc0 pc'
Proof
  rw[prel_def] >> Cases_on ‘j = i’ >> gvs[]
QED

Theorem cidx_step:
  (∀j. MEM j (cidx ((i, x) :: xs)) ⇒ (EL j pc).bh = NONE) ∧ ALL_DISTINCT (cidx ((i, x) :: xs)) ∧
  (∀j a. MEM (j, EConnect a) xs ⇒ j < LENGTH pc) ∧
  (∀j. j < LENGTH pc ∧ j ≠ i ⇒ EL j pc' = EL j pc) ∧
  ((∀a. x ≠ EConnect a) ∧ i < LENGTH pc ⇒ (EL i pc').bh = (EL i pc).bh) ⇒
  ALL_DISTINCT (cidx xs) ∧ ∀j. MEM j (cidx xs) ⇒ (EL j pc').bh = NONE
Proof
  strip_tac >> conj_asm1_tac
  >- (Cases_on ‘∃a. x = EConnect a’ >> gvs[cidx_def]) >>
  rpt strip_tac >>
  ‘∃a. MEM (j, EConnect a) xs’ by (gvs[cidx_def, MEM_MAP, MEM_FILTER] >> Cases_on ‘y’ >> gvs[] >> metis_tac[]) >>
  ‘j < LENGTH pc’ by metis_tac[] >>
  ‘(EL j pc).bh = NONE’ by (first_x_assum irule >> Cases_on ‘∃a. x = EConnect a’ >> gvs[cidx_def]) >>
  Cases_on ‘j = i’ >> gvs[] >>
  ‘∀a. x ≠ EConnect a’ by (rpt strip_tac >> gvs[cidx_def]) >>
  gvs[]
QED

(* A round's results on the pairs: pupd adds the handles the results
   return to pcount, at most one pair per accept, and keeps pok *)
Theorem pupd_inv:
  ∀xs rs st.
    LENGTH rs = LENGTH xs ∧ EVERY (pok K0 G0) pc0 ∧ prel pc0 st.pc ∧ EVERY (pok K' G') st.pc ∧
    ALL_DISTINCT (cidx xs) ∧ (∀j. MEM j (cidx xs) ⇒ (EL j st.pc).bh = NONE) ∧
    (∀j y. MEM (j, y) xs ⇒ pact lfd b R pc0 j y) ∧
    (∀k. k < LENGTH xs ⇒ rok K0 K' G' R (SND (EL k xs)) (EL k rs)) ⇒
    pcount (pupd st xs rs).pc = pcount st.pc + LENGTH (FLAT (MAP rhdl rs)) ∧
    LENGTH (pupd st xs rs).pc ≤ LENGTH st.pc + nacc xs ∧
    EVERY (pok K' G') (pupd st xs rs).pc
Proof
  Induct >- (Cases >> simp[pupd_def, nacc_def]) >>
  qx_gen_tac ‘ix’ >> PairCases_on ‘ix’ >> rename1 ‘(i, x) :: xs’ >>
  Cases >- simp[] >> rename1 ‘r :: rs’ >> qx_gen_tac ‘st’ >> strip_tac >>
  REWRITE_TAC [pupd_cons] >>
  ‘pact lfd b R pc0 i x’
    by (qpat_assum ‘∀j y. MEM _ _ ⇒ _’ (qspecl_then [‘i’, ‘x’] mp_tac) >> simp[]) >>
  ‘rok K0 K' G' R x r’
    by (qpat_assum ‘∀k. k < LENGTH ((i, x) :: xs) ⇒ _’ (qspec_then ‘0’ mp_tac) >>
        REWRITE_TAC [LENGTH, EL, HD, SND, prim_recTheory.LESS_0] >> disch_then ACCEPT_TAC) >>
  ‘∀a. x = EConnect a ⇒ (EL i st.pc).bh = NONE’
    by (rpt strip_tac >> qpat_assum ‘∀j. MEM j (cidx _) ⇒ _’ irule >> simp[cidx_def]) >>
  ‘LENGTH pc0 ≤ LENGTH st.pc ∧ (i < LENGTH pc0 ⇒ prel1 (EL i pc0) (EL i st.pc))’
    by gvs[prel_def] >>
  mp_tac (SPEC_ALL pupd1_step) >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac ‘st1 = pupd1 st (i, x) r’ >> strip_tac >>
  ‘∀j a. MEM (j, EConnect a) xs ⇒ j < LENGTH st.pc’
    by (rpt strip_tac >>
        qpat_assum ‘∀j y. MEM _ _ ⇒ _’ (qspecl_then [‘j’, ‘EConnect a’] mp_tac) >>
        impl_tac >- (qpat_x_assum ‘MEM (j, EConnect a) xs’ mp_tac >> simp[]) >>
        REWRITE_TAC [pact_def] >> simp[] >> strip_tac >>
        qpat_x_assum ‘LENGTH pc0 ≤ LENGTH st.pc’ mp_tac >>
        qpat_x_assum ‘j < LENGTH pc0’ mp_tac >> DECIDE_TAC) >>
  ‘ALL_DISTINCT (cidx xs) ∧ ∀j. MEM j (cidx xs) ⇒ (EL j st1.pc).bh = NONE’
    by (irule cidx_step >> qexistsl [‘i’, ‘st.pc’, ‘x’] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ‘prel pc0 st1.pc’ by (irule prel_step >> qexistsl [‘i’, ‘st.pc’] >> simp[]) >>
  qpat_x_assum ‘∀rs st. _’ (qspecl_then [‘rs’, ‘st1’] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC,
             qpat_x_assum ‘LENGTH (r :: rs) = _’ mp_tac >> simp[] >> NO_TAC,
             rpt strip_tac >> qpat_assum ‘∀j y. MEM _ _ ⇒ _’ irule >>
             qpat_x_assum ‘MEM (_, _) xs’ mp_tac >> simp[] >> NO_TAC,
             rpt strip_tac >>
             qpat_assum ‘∀k. k < LENGTH ((i, x) :: xs) ⇒ _’ (qspec_then ‘SUC k’ mp_tac) >>
             REWRITE_TAC [LENGTH, EL, TL, LESS_MONO_EQ] >> disch_then irule >>
             first_assum ACCEPT_TAC]) >>
  strip_tac >> simp[nacc_def] >>
  Cases_on ‘∃l. x = EAccept l’ >> gvs[nacc_def]
QED

(* ------------------------------------------------------------------------
   A round's actions: its accepts, its connects and its handles
   ------------------------------------------------------------------------ *)

Theorem cidx_APPEND[simp]:
  cidx (l1 ++ l2) = cidx l1 ++ cidx l2
Proof
  simp[cidx_def, FILTER_APPEND]
QED

Theorem cidx_MAP_pair:
  ∀l. cidx (MAP (λx. (i, x)) l) = REPLICATE (LENGTH (FILTER (λx. ∃a. x = EConnect a) l)) i
Proof
  Induct >> rw[cidx_def] >> gvs[cidx_def]
QED

Theorem cidx_pall:
  (∀p. LENGTH (FILTER (λx. ∃a. x = EConnect a) (f p)) = if P p then 1 else 0) ⇒
  cidx (pall f ps) = FILTER (λi. P (EL i ps)) (GENLIST I (LENGTH ps))
Proof
  strip_tac >> simp[pall_def] >> qspec_tac (‘LENGTH ps’, ‘n’) >>
  Induct >> simp[cidx_def] >>
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND, FILTER_APPEND] >>
  fs[cidx_def] >> simp[GSYM cidx_def, cidx_MAP_pair] >>
  first_x_assum (qspec_then ‘EL n ps’ mp_tac) >> rw[] >> EVAL_TAC
QED

Theorem pwrites_conns:
  FILTER (λx. ∃a. x = EConnect a) (pwrites p) = []
Proof
  rw[pwrites_def] >> every_case_tac >> simp[]
QED

Theorem preads_conns:
  FILTER (λx. ∃a. x = EConnect a) (preads hw lvs lw nw rdy p) = []
Proof
  rw[preads_def] >> every_case_tac >> rw[]
QED

Theorem cidx_pacts:
  cidx (pacts lfd b hw st R) = FILTER (λi. (EL i st.pc).bh = NONE) (GENLIST I (LENGTH st.pc))
Proof
  ‘cidx (pall plevels st.pc) = FILTER (λi. (λp. F) (EL i st.pc)) (GENLIST I (LENGTH st.pc))’
    by (irule cidx_pall >> simp[plevels_def, FILTER_EQ_NIL, EVERY_MEM, MEM_MAP, PULL_EXISTS]) >>
  ‘cidx (pall (pone b hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) R) st.pc) =
   FILTER (λi. (λp. p.bh = NONE) (EL i st.pc)) (GENLIST I (LENGTH st.pc))’
    by (irule cidx_pall >> rw[pone_def, pconnects_def, FILTER_APPEND, pwrites_conns, preads_conns]) >>
  simp[moonshotProxyTheory.pacts_def] >> rw[cidx_def]
QED

Theorem LENGTH_FILTER_EL:
  ∀P ps. LENGTH (FILTER (λi. P (EL i ps)) (GENLIST I (LENGTH ps))) = LENGTH (FILTER P ps)
Proof
  rpt gen_tac >> ‘ps = MAP (λi. EL i ps) (GENLIST I (LENGTH ps))’ by simp[MAP_GENLIST, GENLIST_ID] >>
  pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[FILTER_MAP, combinTheory.o_DEF]
QED

(* The pairs a round connects: each at most once, and only one without a backend *)
Theorem cidx_pacts_props:
  ALL_DISTINCT (cidx (pacts lfd b hw st R)) ∧
  (∀j. MEM j (cidx (pacts lfd b hw st R)) ⇒ j < LENGTH st.pc ∧ (EL j st.pc).bh = NONE) ∧
  LENGTH (cidx (pacts lfd b hw st R)) = LENGTH (FILTER (λp. p.bh = NONE) st.pc)
Proof
  simp[cidx_pacts] >> rpt conj_tac
  >- (irule FILTER_ALL_DISTINCT >> simp[ALL_DISTINCT_GENLIST])
  >- simp[MEM_FILTER, MEM_GENLIST] >>
  qspecl_then [‘λp. p.bh = NONE’, ‘st.pc’] mp_tac LENGTH_FILTER_EL >> simp[]
QED

Theorem nacc_SND:
  nacc xs = LENGTH (FILTER (λx. ∃l. x = EAccept l) (MAP SND xs))
Proof
  simp[nacc_def, FILTER_MAP, combinTheory.o_DEF]
QED

Theorem cidx_SND:
  LENGTH (cidx xs) = LENGTH (FILTER (λx. ∃a. x = EConnect a) (MAP SND xs))
Proof
  simp[cidx_def, FILTER_MAP, combinTheory.o_DEF]
QED

Theorem nacc_pacts:
  nacc (pacts lfd b hw st R) = if 2 * LENGTH st.pc + 2 ≤ cbound then 1 else 0
Proof
  simp[nacc_SND] >> ONCE_REWRITE_TAC [pacts_SND] >>
  ‘FILTER (λx. ∃l. x = EAccept l) (FLAT (MAP plevels st.pc)) = []’
    by simp[FILTER_EQ_NIL, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS, plevels_def] >>
  ‘FILTER (λx. ∃l. x = EAccept l)
     (FLAT (MAP (pone b hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) R) st.pc)) = []’
    by (rw[FILTER_EQ_NIL, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        gvs[pone_def, pconnects_def, pwrites_def, preads_def, AllCaseEqs()] >>
        every_case_tac >> gvs[]) >>
  rw[FILTER_APPEND]
QED

Theorem nhdls_FILTER:
  ∀l. nhdls l = LENGTH (FILTER (λx. ∃l. x = EAccept l) l) + LENGTH (FILTER (λx. ∃a. x = EConnect a) l)
Proof
  Induct >> simp[nhdls_def] >> Cases >> rw[nhdls_def]
QED

Theorem pcount_FILTER:
  ∀pc. pcount pc + LENGTH (FILTER (λp. p.bh = NONE) pc) = 2 * LENGTH pc
Proof
  Induct >> rw[pcount_def, pcnt_def] >> fs[pcount_def]
QED

(* The handles a round's actions may take, with the pairs' handles *)
Theorem pacts_hdls:
  pcount st.pc + nhdls (MAP SND (pacts lfd b hw st R)) =
  2 * LENGTH st.pc + if 2 * LENGTH st.pc + 2 ≤ cbound then 1 else 0
Proof
  simp[nhdls_FILTER, GSYM nacc_SND, GSYM cidx_SND, nacc_pacts, cidx_pacts_props] >>
  mp_tac (Q.SPEC ‘st.pc’ pcount_FILTER) >> rw[]
QED

(* ------------------------------------------------------------------------
   The invariant at a round's start
   ------------------------------------------------------------------------ *)

(* The ready handles the state's last actions saw (as moonshotClientTotal's) *)
Definition cready_def:
  cready (h : (word64, eresp) snapshot list) = if h = [] then ∅ else (LAST h).ready
End

Theorem cready_SNOC[simp]:
  cready (h ++ [s]) = s.ready
Proof
  simp[cready_def]
QED

(* The state's last actions are the round's, from a state with its pairs *)
Theorem pstate_last:
  ∃st'. st'.pc = (pstate lfd b hw h).pc ∧ (pstate lfd b hw h).last = pacts lfd b hw st' (cready h)
Proof
  Cases_on ‘h’ using SNOC_CASES
  >- (simp[pstate_def, moonshotProxyTheory.pinit_def, cready_def] >>
      qexists_tac ‘<| pc := []; last := []; lv := [] |>’ >> simp[]) >>
  simp[SNOC_APPEND, pstate_SNOC, pstep_def] >>
  qmatch_goalsub_abbrev_tac ‘pacts lfd b hw st1 _’ >> qexists_tac ‘st1’ >> simp[]
QED

Theorem pok_mono:
  (∀hd. Kp hd ⇒ Kp' hd) ∧ (∀hd. Kp hd ∧ Gp hd ⇒ Gp' hd) ∧ pok Kp Gp p ⇒ pok Kp' Gp' p
Proof
  rw[pok_def] >> metis_tac[]
QED

Theorem prel_refl[simp]:
  prel pc pc
Proof
  simp[prel_def, prel1_def]
QED

Definition pinv_def:
  pinv lfd pc es (R : word64 -> bool) ⇔
    es.p.b.nxt = pcount pc ∧ 2 * LENGTH pc ≤ cbound ∧
    EVERY (pok (λhd. ∃j. j < es.p.b.nxt ∧ hd = hdl lfd j) (λhd. ALOOKUP es.ctbl hd = NONE)) pc ∧
    (∀hd f. hd ∈ R ∧ ALOOKUP es.ctbl hd = SOME f ⇒ cstat_of es f = CRefused)
End

(* The round's actions take at most cbound handles with the pairs' *)
Theorem proxy_nhdls:
  pinv lfd st.pc es R' ⇒ es.p.b.nxt + nhdls (MAP SND (pacts lfd b hw st R)) ≤ cbound
Proof
  strip_tac >>
  ‘es.p.b.nxt = pcount st.pc ∧ 2 * LENGTH st.pc ≤ cbound’ by gvs[pinv_def] >>
  mp_tac pacts_hdls >> rw[]
QED

Theorem cbound_lt:
  cbound + 2 < dimword (:64)
Proof
  simp[cbound_def]
QED

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

Theorem eacts_rkind:
  ∀acts ws rs evs ws'.
    eacts lfd pol ws acts = SOME (rs, evs, ws') ⇒
    LENGTH rs = LENGTH acts ∧ ∀k. k < LENGTH acts ⇒ rkind (EL k acts) (EL k rs)
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws’ >> drule edo_rkind >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >> Cases >> simp[]
QED

(* A write's handle was issued with no connect entry: it has none after
   the earlier actions *)
Theorem write_ok:
  ebund lfd w es ∧ eacts lfd pol (w, es) acts = SOME (rs, evs, (wi, esi)) ∧
  j < es.p.b.nxt ∧ ALOOKUP es.ctbl (hdl lfd j) = NONE ⇒
  ∀f. ALOOKUP esi.ctbl (hdl lfd j) = SOME f ⇒ cstat_of esi f = CRefused
Proof
  strip_tac >> ‘ALOOKUP esi.ctbl (hdl lfd j) = NONE’ by metis_tac[eacts_ctbl_none] >> simp[]
QED

Theorem write_pok:
  pok (λhd. ∃j. j < es.p.b.nxt ∧ hd = hdl lfd j) (λhd. ALOOKUP es.ctbl hd = NONE) p ⇒
  ebund lfd w es ⇒ eacts lfd pol (w, es) acts = SOME (rs, evs, (wi, esi)) ⇒
  ALOOKUP esi.ctbl h = SOME f ⇒ (h = p.fh ∨ p.bh = SOME h ∧ p.fq ≠ []) ⇒
  cstat_of esi f = CRefused
Proof
  rpt disch_tac >>
  ‘∃j. j < es.p.b.nxt ∧ h = hdl lfd j ∧ ALOOKUP es.ctbl h = NONE’ by (gvs[pok_def] >> metis_tac[]) >>
  gvs[] >> metis_tac[write_ok]
QED

(* Each action is one L1 accepts, in the state the earlier ones left *)
Theorem proxy_acts_ok:
  b < 65536 ∧ pinv lfd st.pc es R ∧ ebund lfd w es ∧ i < LENGTH (pacts lfd b hw st R) ∧
  eacts lfd pol (w, es) (TAKE i (MAP SND (pacts lfd b hw st R))) = SOME (rs0, evs0, (wi, esi)) ⇒
  eact_ok lfd esi (EL i (MAP SND (pacts lfd b hw st R)))
Proof
  strip_tac >> simp[EL_MAP] >>
  ‘MEM (EL i (pacts lfd b hw st R)) (pacts lfd b hw st R)’ by simp[EL_MEM] >>
  Cases_on ‘EL i (pacts lfd b hw st R)’ >> rename1 ‘(j, x)’ >> simp[] >>
  ‘MEM x (MAP SND (pacts lfd b hw st R))’
    by (drule (Q.ISPEC ‘SND : num # eact -> eact’ MEM_MAP_f) >> simp[]) >>
  ‘pact lfd b R st.pc j x’ by (drule pacts_mem >> simp[]) >>
  drule MEM_pacts >> strip_tac >>
  qpat_x_assum ‘pact _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [pact_def])
  >- simp[eact_ok_def]
  >- simp[eact_ok_def] >>
  ‘pok (λhd. ∃j. j < es.p.b.nxt ∧ hd = hdl lfd j) (λhd. ALOOKUP es.ctbl hd = NONE) (EL j st.pc)’
    by (qpat_x_assum ‘pinv _ _ _ _’ mp_tac >> simp[pinv_def, EVERY_EL]) >>
  qpat_x_assum ‘pact1 _ _ _ _’ (strip_assume_tac o REWRITE_RULE [pact1_def]) >>
  qpat_x_assum ‘x = _’ SUBST_ALL_TAC >> simp[eact_ok_def, pread_def] >>
  rpt strip_tac >>
  qpat_x_assum ‘pok _ _ _’ (fn th => drule (MATCH_MP write_pok th)) >>
  disch_then drule >> disch_then drule >> disch_then match_mp_tac >>
  FIRST [disj1_tac >> REFL_TAC, disj2_tac >> conj_tac >> first_assum ACCEPT_TAC]
QED

(* Each result is one the pairs' update keeps the invariant with *)
Theorem proxy_res_ok:
  ebund lfd w es ∧ k < LENGTH acts ∧
  (∀hd f. hd ∈ R ∧ ALOOKUP es.ctbl hd = SOME f ⇒ cstat_of es f = CRefused) ∧
  eacts lfd pol (w, es) acts = SOME (rs, evs, (w1, es1)) ∧ es1.p.b.nxt + 1 < dimword (:64) ∧
  etail lfd pol hs (w1, es1) = SOME (rdy, (w2, es2), log, tevs) ∧ es2.p.b.nxt = es1.p.b.nxt ⇒
  rok (λhd. ∃j. j < es.p.b.nxt ∧ hd = hdl lfd j) (λhd. ∃j. j < es2.p.b.nxt ∧ hd = hdl lfd j)
      (λhd. ALOOKUP es2.ctbl hd = NONE) R (EL k acts) (EL k rs)
Proof
  strip_tac >>
  drule eacts_rkind >> strip_tac >>
  drule eacts_hdls >> strip_tac >>
  REWRITE_TAC [rok_def] >> BETA_TAC >> rpt conj_tac
  >- (first_x_assum irule >> first_assum ACCEPT_TAC)
  >- (gen_tac >> strip_tac >>
      ‘MEM hd (FLAT (MAP rhdl rs))’ by (simp[MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM]) >>
      qpat_x_assum ‘∀hd. MEM hd (FLAT _) ⇒ _’ drule >> strip_tac >> conj_tac
      >- (qexists_tac ‘j’ >> qpat_x_assum ‘es2.p.b.nxt = _’ (fn th => REWRITE_TAC [th]) >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      rpt strip_tac >> rename1 ‘j' < es.p.b.nxt’ >>
      ‘j + 1 < dimword (:64) ∧ j' + 1 < dimword (:64)’
        by (qpat_x_assum ‘es1.p.b.nxt + 1 < _’ mp_tac >> qpat_x_assum ‘j < es1.p.b.nxt’ mp_tac >>
            qpat_x_assum ‘j' < es.p.b.nxt’ mp_tac >> qpat_x_assum ‘es1.p.b.nxt = _’ mp_tac >>
            simp[]) >>
      ‘j = j'’ by metis_tac[hdl_11] >>
      qpat_x_assum ‘es.p.b.nxt ≤ j’ mp_tac >> qpat_x_assum ‘j' < es.p.b.nxt’ mp_tac >> simp[])
  >- (rpt strip_tac >>
      ‘ALOOKUP es1.ctbl hd = NONE’
        by (qpat_assum ‘eacts _ _ _ _ = _’ (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
              (ONCE_REWRITE_RULE [CONJ_COMM] (SPEC_ALL eacts_accepted)))) >>
            impl_tac >- first_assum ACCEPT_TAC >> impl_tac >- first_assum ACCEPT_TAC >>
            disch_then irule >> qpat_x_assum ‘EL k rs = _’ (SUBST1_TAC o SYM) >>
            irule EL_MEM >> qpat_x_assum ‘LENGTH rs = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      drule_all etail_ctbl >> simp[]) >>
  rpt strip_tac >> qpat_x_assum ‘hd = hdl lfd j’ SUBST_ALL_TAC >>
  ‘ALOOKUP es1.ctbl (hdl lfd j) = NONE’
    by (drule_at (Pos (el 2)) eacts_ctbl_gone >>
        disch_then (qspecl_then [‘k’, ‘hdl lfd j’, ‘n’, ‘y’, ‘j’] mp_tac) >>
        disch_then irule >> rpt conj_tac >>
        FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC,
               rpt strip_tac >> qpat_x_assum ‘∀hd f. _’ (qspecl_then [‘hdl lfd j’, ‘f’] mp_tac) >>
               impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[]]) >>
  drule_all etail_ctbl >> simp[]
QED

(* A handle without a connect entry keeps none through the round *)
Theorem proxy_ctbl_none:
  ebund lfd w es ∧ eacts lfd pol (w, es) acts = SOME (rs, evs, (w1, es1)) ∧
  etail lfd pol hs (w1, es1) = SOME (rdy, (w2, es2), log, tevs) ∧
  j < es.p.b.nxt ∧ ALOOKUP es.ctbl (hdl lfd j) = NONE ⇒
  ALOOKUP es2.ctbl (hdl lfd j) = NONE
Proof
  strip_tac >>
  ‘ALOOKUP es1.ctbl (hdl lfd j) = NONE’ by metis_tac[eacts_ctbl_none] >>
  metis_tac[etail_ctbl]
QED

(* One round from a state with the invariant's pairs (st0: the state the
   results update; st: the state the actions came from) *)
Theorem proxy_round:
  ∀st st0 es w R hs.
    b < 65536 ∧ st0.pc = st.pc ∧ pinv lfd st.pc es R ∧ ebund lfd w es ∧ esmall lfd es ⇒
    ∃rs aevs w1 es1 rdy w2 es2 log tevs.
      eacts lfd pol (w, es) (MAP SND (pacts lfd b hw st R)) = SOME (rs, aevs, (w1, es1)) ∧
      etail lfd pol hs (w1, es1) = SOME (rdy, (w2, es2), log, tevs) ∧
      esmall lfd es2 ∧ es2.p.b.nxt = es1.p.b.nxt ∧
      pinv lfd (pupd st0 (pacts lfd b hw st R) rs).pc es2 (set rdy)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [‘R'’ |-> ‘R’] (SPEC_ALL proxy_nhdls)) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  assume_tac cbound_lt >>
  ‘l0_rely w’ by (qpat_x_assum ‘ebund _ _ _’ mp_tac >> simp[ebund_def]) >>
  ‘∃rs aevs w1 es1.
     eacts lfd pol (w, es) (MAP SND (pacts lfd b hw st R)) = SOME (rs, aevs, (w1, es1)) ∧
     l0_rely w1 ∧ esmall lfd es1 ∧ es1.p.b.nxt ≤ es.p.b.nxt + nhdls (MAP SND (pacts lfd b hw st R))’
    by (irule eacts_ok >> rpt conj_tac >>
        FIRST [first_assum ACCEPT_TAC,
               qpat_x_assum ‘_ + nhdls _ ≤ cbound’ mp_tac >> qpat_x_assum ‘cbound + 2 < _’ mp_tac >>
               rpt (pop_assum kall_tac) >> simp[] >> NO_TAC,
               rpt strip_tac >> drule_at (Pos last) proxy_acts_ok >>
               disch_then irule >> rpt conj_tac >>
               FIRST [first_assum ACCEPT_TAC, qpat_x_assum ‘i < LENGTH _’ mp_tac >> simp[]]]) >>
  ‘∃rdy w2 es2 log tevs.
     etail lfd pol hs (w1, es1) = SOME (rdy, (w2, es2), log, tevs) ∧
     l0_rely w2 ∧ esmall lfd es2 ∧ es2.p.b.nxt = es1.p.b.nxt’
    by (irule etail_ok >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [‘rs’, ‘aevs’, ‘w1’, ‘es1’, ‘rdy’, ‘w2’, ‘es2’, ‘log’, ‘tevs’] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  drule eacts_rkind >> strip_tac >>
  drule eacts_hdls >> strip_tac >>
  qpat_assum ‘pinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [pinv_def]) >>
  strip_assume_tac cidx_pacts_props >>
  ‘es1.p.b.nxt + 1 < dimword (:64)’
    by (qpat_x_assum ‘es1.p.b.nxt ≤ _’ mp_tac >> qpat_x_assum ‘_ + nhdls _ ≤ cbound’ mp_tac >>
        qpat_x_assum ‘cbound + 2 < _’ mp_tac >> rpt (pop_assum kall_tac) >> simp[]) >>
  ‘es.p.b.nxt ≤ es2.p.b.nxt’
    by (qpat_x_assum ‘es2.p.b.nxt = _’ mp_tac >> qpat_x_assum ‘es1.p.b.nxt = es.p.b.nxt + _’ mp_tac >>
        rpt (pop_assum kall_tac) >> simp[]) >>
  (* the pairs' handles stay issued and without a connect entry *)
  ‘EVERY (pok (λhd. ∃j. j < es2.p.b.nxt ∧ hd = hdl lfd j) (λhd. ALOOKUP es2.ctbl hd = NONE)) st.pc’
    by (irule MONO_EVERY >>
        qexists_tac ‘pok (λhd. ∃j. j < es.p.b.nxt ∧ hd = hdl lfd j) (λhd. ALOOKUP es.ctbl hd = NONE)’ >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        rpt strip_tac >> irule pok_mono >> first_assum (irule_at Any) >>
        BETA_TAC >> rpt conj_tac >> rpt strip_tac >>
        FIRST [qexists_tac ‘j’ >> conj_tac
               >- (qpat_x_assum ‘j < es.p.b.nxt’ mp_tac >> qpat_x_assum ‘es.p.b.nxt ≤ es2.p.b.nxt’ mp_tac >>
                   rpt (pop_assum kall_tac) >> simp[]) >>
               first_assum ACCEPT_TAC,
               TRY (qpat_x_assum ‘hd = _’ SUBST_ALL_TAC) >> drule_all proxy_ctbl_none >>
               disch_then ACCEPT_TAC]) >>
  (* each result *)
  ‘∀k. k < LENGTH (pacts lfd b hw st R) ⇒
       rok (λhd. ∃j. j < es.p.b.nxt ∧ hd = hdl lfd j) (λhd. ∃j. j < es2.p.b.nxt ∧ hd = hdl lfd j)
           (λhd. ALOOKUP es2.ctbl hd = NONE) R (SND (EL k (pacts lfd b hw st R))) (EL k rs)’
    by (rpt strip_tac >>
        ‘EL k (MAP SND (pacts lfd b hw st R)) = SND (EL k (pacts lfd b hw st R))’
          by (irule EL_MAP >> first_assum ACCEPT_TAC) >>
        pop_assum (fn th => REWRITE_TAC [GSYM th]) >>
        mp_tac (Q.INST [‘evs’ |-> ‘aevs’, ‘acts’ |-> ‘MAP SND (pacts lfd b hw st R)’]
                  (SPEC_ALL proxy_res_ok)) >>
        impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, qpat_x_assum ‘k < _’ mp_tac >> simp[]]) >>
        disch_then ACCEPT_TAC) >>
  mp_tac (Q.INST [‘K0’ |-> ‘λhd. ∃j. j < es.p.b.nxt ∧ hd = hdl lfd j’,
                  ‘G0’ |-> ‘λhd. ALOOKUP es.ctbl hd = NONE’,
                  ‘K'’ |-> ‘λhd. ∃j. j < es2.p.b.nxt ∧ hd = hdl lfd j’,
                  ‘G'’ |-> ‘λhd. ALOOKUP es2.ctbl hd = NONE’, ‘pc0’ |-> ‘st.pc’] pupd_inv) >>
  disch_then (qspecl_then [‘pacts lfd b hw st R’, ‘rs’, ‘st0’] mp_tac) >>
  impl_tac
  >- (qpat_x_assum ‘st0.pc = st.pc’ (fn th => REWRITE_TAC [th]) >> rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, REWRITE_TAC [prel_refl] >> NO_TAC,
             qpat_x_assum ‘LENGTH rs = _’ mp_tac >> REWRITE_TAC [LENGTH_MAP] >> NO_TAC,
             rpt strip_tac >> qpat_x_assum ‘∀j. MEM j (cidx _) ⇒ _’ drule >> simp[] >> NO_TAC,
             rpt strip_tac >> drule pacts_mem >> disch_then ACCEPT_TAC]) >>
  strip_tac >> REWRITE_TAC [pinv_def] >> rpt conj_tac
  >| [qpat_x_assum ‘pcount (pupd _ _ _).pc = _’ (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum ‘st0.pc = st.pc’ (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum ‘es2.p.b.nxt = _’ (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum ‘es1.p.b.nxt = es.p.b.nxt + _’ (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum ‘es.p.b.nxt = pcount st.pc’ (fn th => REWRITE_TAC [th]),
      qpat_x_assum ‘LENGTH (pupd _ _ _).pc ≤ _’ mp_tac >>
      qpat_x_assum ‘st0.pc = st.pc’ (fn th => REWRITE_TAC [th, nacc_pacts]) >>
      qpat_x_assum ‘2 * LENGTH st.pc ≤ cbound’ mp_tac >>
      rpt (pop_assum kall_tac) >> IF_CASES_TAC >> rpt strip_tac >> fs[],
      first_assum ACCEPT_TAC,
      rpt strip_tac >> drule_all etail_rdy_ctbl >> disch_then ACCEPT_TAC]
QED

(* ------------------------------------------------------------------------
   Every round
   ------------------------------------------------------------------------ *)

Theorem small_lfd:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ⇒ small lfd
Proof
  strip_tac >>
  ‘w2n lfd < w0.fd_limit’
    by (qpat_x_assum ‘fds_lt _’ mp_tac >> simp[honestL0WorldPropsTheory.fds_lt_def] >>
        disch_then drule >> simp[]) >>
  ‘w0.fd_limit ≤ 2147483648’ by gvs[l0_rely_def] >>
  simp[honestL1InvTheory.small_def]
QED

(* L1's bundle at each round's start, from the refinement *)
Theorem erounds_ebund:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n'. n' ≤ n ⇒ SND (ecm lfd pol ifds m w0 n') + 1 < dimword (:64)) ∧
  erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
  ebund lfd (FST ws) (SND ws)
Proof
  strip_tac >>
  mp_tac (INST [“N:num” |-> “n:num”] l1ep_refines_ehl_upto) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [‘n’, ‘h’, ‘ws’, ‘evs’, ‘logs’] mp_tac) >>
  simp[ebund_def] >> strip_tac >> metis_tac[]
QED

Theorem proxy_rounds:
  b < 65536 ∧ l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ⇒
  ∀n. ∃h ws evs logs.
    erounds lfd pol (pifds lfd b hw) (pprog lfd b hw) (w0, einit) n = SOME (h, ws, evs, logs) ∧
    pinv lfd (pstate lfd b hw h).pc (SND ws) (cready h) ∧ esmall lfd (SND ws) ∧
    SND (ecm lfd pol (pifds lfd b hw) (pprog lfd b hw) w0 n) =
      (SND ws).p.b.nxt + LENGTH (SND ws).p.acq ∧
    ∀n'. n' ≤ n ⇒ SND (ecm lfd pol (pifds lfd b hw) (pprog lfd b hw) w0 n') + 1 < dimword (:64)
Proof
  strip_tac >> Induct
  >- (simp[erounds_def, ecm_def] >> rpt conj_tac >>
      FIRST [irule esmall_einit >> metis_tac[small_lfd],
             simp[pinv_def, pstate_def, moonshotProxyTheory.pinit_def, pcount_def, cready_def, einit_def,
                  honestL1PFModelTheory.pinit_def, honestL1ModelTheory.l1init_def, cbound_def] >> NO_TAC,
             simp[einit_def, honestL1PFModelTheory.pinit_def, honestL1ModelTheory.l1init_def] >> NO_TAC]) >>
  pop_assum strip_assume_tac >> PairCases_on ‘ws’ >>
  RULE_ASSUM_TAC (REWRITE_RULE [pairTheory.FST, pairTheory.SND]) >>
  ‘ebund lfd ws0 ws1’
    by (drule_at (Pos last) erounds_ebund >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  strip_assume_tac pstate_last >>
  qspecl_then [‘st'’, ‘pstate lfd b hw h with lv := []’, ‘ws1’, ‘ws0’, ‘cready h’,
               ‘pifds lfd b hw h’] mp_tac proxy_round >>
  impl_tac
  >- (rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC,
             qpat_x_assum ‘pinv _ _ _ _’ mp_tac >> qpat_x_assum ‘st'.pc = _’ (fn th => REWRITE_TAC [th]) >>
             NO_TAC,
             simp[] >> qpat_x_assum ‘st'.pc = _’ (ACCEPT_TAC o SYM)]) >>
  strip_tac >>
  ‘SND (ecm lfd pol (pifds lfd b hw) (pprog lfd b hw) w0 (SUC n)) = es2.p.b.nxt + LENGTH es2.p.acq’
    by (‘eacts lfd pol (ws0, ws1) (new_actions (log_of (pprog lfd b hw)) h) = SOME (rs, aevs, (w1, es1))’
          by simp[pprog_new_actions] >>
        ‘(SND (w2, es2)).p.b.nxt = (SND (w1, es1)).p.b.nxt’ by simp[] >>
        ‘SND (ecm lfd pol (pifds lfd b hw) (pprog lfd b hw) w0 n) =
           (SND (ws0, ws1)).p.b.nxt + LENGTH (SND (ws0, ws1)).p.acq’ by simp[] >>
        drule_all ecm_round >> simp[]) >>
  ‘erounds lfd pol (pifds lfd b hw) (pprog lfd b hw) (w0, einit) (SUC n) =
     SOME (h ++ [ssnap rdy rs], (w2, es2), evs ++ (aevs ++ tevs), logs ++ [log])’
    by simp[erounds_def, eround_def, pprog_new_actions] >>
  ‘LENGTH es2.p.acq ≤ 1’
    by (qpat_assum ‘erounds _ _ _ _ _ (SUC n) = _’ (mp_tac o MATCH_MP erounds_acq) >> simp[]) >>
  qabbrev_tac ‘pc' = (pupd (pstate lfd b hw h with lv := []) (pacts lfd b hw st' (cready h)) rs).pc’ >>
  ‘es2.p.b.nxt = pcount pc' ∧ 2 * LENGTH pc' ≤ cbound’
    by (qpat_x_assum ‘pinv _ pc' _ _’ mp_tac >> simp[pinv_def]) >>
  qexistsl_tac [‘h ++ [ssnap rdy rs]’, ‘(w2, es2)’, ‘evs ++ (aevs ++ tevs)’, ‘logs ++ [log]’] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qpat_x_assum ‘pinv _ pc' _ _’ mp_tac >>
      simp[pstate_SNOC, pstep_def, asyncM3WorldTheory.ssnap_def, Abbr ‘pc'’])
  >- simp[]
  >- simp[] >>
  rpt strip_tac >> Cases_on ‘n' ≤ n’ >- simp[] >>
  ‘n' = SUC n’ by simp[] >> qpat_x_assum ‘n' = _’ SUBST1_TAC >>
  qpat_x_assum ‘SND (ecm _ _ _ _ _ (SUC n)) = _’ SUBST1_TAC >>
  qspec_then ‘pc'’ assume_tac pcount_FILTER >>
  qpat_x_assum ‘LENGTH es2.p.acq ≤ 1’ mp_tac >> qpat_x_assum ‘es2.p.b.nxt = pcount pc'’ mp_tac >>
  qpat_x_assum ‘2 * LENGTH pc' ≤ cbound’ mp_tac >> qpat_x_assum ‘pcount pc' + _ = _’ mp_tac >>
  assume_tac cbound_lt >> qpat_x_assum ‘cbound + 2 < _’ mp_tac >>
  rpt (pop_assum kall_tac) >> simp[]
QED

(* The run hypotheses: the proxy's L1 run never fails and its channel
   count stays below 2^64 - 1 *)
Theorem proxy_l1_total:
  b < 65536 ∧ l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ⇒
  (∀n. erounds lfd pol (pifds lfd b hw) (pprog lfd b hw) (w0, einit) n ≠ NONE) ∧
  (∀n. SND (ecm lfd pol (pifds lfd b hw) (pprog lfd b hw) w0 n) + 1 < dimword (:64))
Proof
  strip_tac >> mp_tac (SPEC_ALL proxy_rounds) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >> conj_tac >> gen_tac
  >- (first_x_assum (qspec_then ‘n’ strip_assume_tac) >> simp[]) >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]
QED
