(*
  The client's L1 run never fails and its channel count stays below
  2^64 - 1: the hypotheses (i) and (ii) of client_l1_claim (C1), from
  honestL1EPTotal's conditions on each action.

  At each round's start (cinv): the client counts the handles L1 issued;
  its open handles are among them; an up connection's handle has no
  connect entry; and a ready handle with a connect entry was refused.
  So its writes go to handles L1 holds, it connects at most N times a
  round and only below cbound handles, and L1 accepts no connection (the
  client polls no listener), so the channel count is the handle count.
*)
Theory moonshotClientTotal
Ancestors
  moonshotClient moonshotClientSpec honestL1EPBund honestL1EPTotal honestL1EPRefine honestL1EPModel
  endpointHLModel asyncCore honestL0Rely
Libs
  preamble

(* ------------------------------------------------------------------------
   The client's actions
   ------------------------------------------------------------------------ *)

(* The ready handles the state's last actions saw *)
Definition cready_def:
  cready (h : (word64, eresp) snapshot list) = if h = [] then ∅ else (LAST h).ready
End

Theorem cacts_last[simp]:
  cacts a (st with last := l) R = cacts a st R
Proof
  simp[cacts_def]
QED

Theorem cstate_last:
  (cstate a N rqs h).last = cacts a (cstate a N rqs h) (cready h)
Proof
  Cases_on ‘h’ using SNOC_CASES
  >- simp[cstate_def, cinit_def, cready_def, cacts_def] >>
  simp[SNOC_APPEND, cstate_SNOC, cstep_def, cready_def]
QED

Theorem cacts_mem:
  MEM (i, x) (cacts a st R) ⇒ i < LENGTH st.cs ∧ MEM x (cact1 a st.nh (EL i st.cs) R)
Proof
  simp[cacts_def, MEM_FLAT, MEM_GENLIST, MEM_MAP, PULL_EXISTS] >> rw[] >> gvs[]
QED

Theorem cacts_no_accept:
  EVERY (λx. ∀l. x ≠ EAccept l) (MAP SND (cacts a st R))
Proof
  simp[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rpt strip_tac >>
  drule cacts_mem >> strip_tac >> gvs[cact1_def] >> every_case_tac >> gvs[]
QED

(* nor closes or shuts one (E1's noclose) *)
Theorem cacts_noclose:
  EVERY noclose (MAP SND (cacts a st R))
Proof
  simp[EVERY_MEM, MEM_cacts] >> rpt strip_tac >>
  rename1 ‘MEM x (cact1 _ _ (EL i st.cs) _)’ >>
  Cases_on ‘EL i st.cs’ >> gvs[cact1_def, AllCaseEqs(), noclose_def] >>
  rpt (pop_assum mp_tac) >> rw[] >> simp[]
QED

Theorem cacts_noshut:
  EVERY noshut (MAP SND (cacts a st R))
Proof
  irule EVERY_noclose_noshut >> simp[cacts_noclose]
QED

Theorem nhdls_APPEND:
  nhdls (l1 ++ l2) = nhdls l1 + nhdls l2
Proof
  Induct_on ‘l1’ >> simp[nhdls_def] >> rpt strip_tac >>
  ONCE_REWRITE_TAC[nhdls_cons] >> simp[]
QED

Theorem nhdls_cact1:
  nhdls (cact1 a nh c R) ≤ if nh < cbound then 1 else 0
Proof
  Cases_on ‘c’ >> rw[cact1_def, nhdls_def]
QED

Theorem nhdls_cacts:
  nhdls (MAP SND (cacts a st R)) ≤ if st.nh < cbound then LENGTH st.cs else 0
Proof
  simp[cacts_def, MAP_FLAT, MAP_GENLIST, combinTheory.o_DEF, MAP_MAP_o] >>
  qspec_tac (‘LENGTH st.cs’, ‘n’) >> Induct >> simp[nhdls_def] >>
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND, nhdls_APPEND] >>
  ‘nhdls (cact1 a st.nh (EL n st.cs) R) ≤ if st.nh < cbound then 1 else 0’
    by simp[nhdls_cact1] >>
  Cases_on ‘st.nh < cbound’ >> gvs[]
QED

(* ------------------------------------------------------------------------
   The results' update
   ------------------------------------------------------------------------ *)

(* A connection's state, with its handle among Kp and an up one's in Gp *)
Definition cok1_def:
  cok1 (Kp : word64 -> bool) (Gp : word64 -> bool) c ⇔
    (∀hd. c = CPend hd ⇒ Kp hd) ∧ (∀hd rest. c = CUp hd rest ⇒ Kp hd ∧ Gp hd)
End

(* A result: a new handle is among Kp, a read with data of a handle is of
   one among Kp and Gp *)
Definition cres_ok_def:
  cres_ok (Kp : word64 -> bool) (Gp : word64 -> bool) x r ⇔
    (∀hd. r = EConnected (SOME hd) ⇒ Kp hd) ∧
    (∀hd n y. x = ERead hd n ∧ r = EGot y ⇒ Kp hd ∧ Gp hd)
End

Theorem cres_cok1:
  cok1 Kp Gp c ∧ cres_ok Kp Gp x r ⇒ cok1 Kp Gp (cres b c x r)
Proof
  rw[cok1_def, cres_ok_def, cres_def] >> every_case_tac >> gvs[]
QED

Theorem EVERY_LUPDATE_IMP:
  ∀l i. EVERY P l ∧ (i < LENGTH l ⇒ P x) ⇒ EVERY P (LUPDATE x i l)
Proof
  Induct >> simp[LUPDATE_def] >> Cases_on ‘i’ >> simp[LUPDATE_def]
QED

Theorem cupd_props:
  ∀Kp Gp xs rs st.
    LENGTH xs = LENGTH rs ⇒
    LENGTH (cupd rqs st xs rs).cs = LENGTH st.cs ∧
    (cupd rqs st xs rs).nh = st.nh + LENGTH (conn_hdls rs) ∧
    (EVERY (cok1 Kp Gp) st.cs ∧ (∀k. k < LENGTH xs ⇒ cres_ok Kp Gp (SND (EL k xs)) (EL k rs)) ⇒
     EVERY (cok1 Kp Gp) (cupd rqs st xs rs).cs)
Proof
  ntac 2 gen_tac >> Induct >- simp[cupd_def, conn_hdls_def] >>
  rpt gen_tac >> Cases_on ‘rs’ >> simp[] >> strip_tac >> PairCases_on ‘h’ >>
  simp[cupd_def] >> first_x_assum drule >>
  qmatch_goalsub_abbrev_tac ‘cupd rqs st1 xs t’ >>
  disch_then (qspec_then ‘st1’ strip_assume_tac) >> simp[] >>
  ONCE_REWRITE_TAC[conn_hdls_cons] >> rpt conj_tac
  >- (simp[Abbr ‘st1’] >> rename1 ‘new_hd r’ >> Cases_on ‘r’ >> simp[new_hd_def, conn_hdls_def] >>
      rename1 ‘EConnected oo’ >> Cases_on ‘oo’ >> simp[new_hd_def, conn_hdls_def])
  >> strip_tac >> first_x_assum irule >> rpt conj_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then ‘SUC k’ mp_tac) >> simp[])
  >> simp[Abbr ‘st1’] >> irule EVERY_LUPDATE_IMP >> simp[] >> strip_tac >>
  irule cres_cok1 >> conj_tac >>
  FIRST [gvs[EVERY_EL] >> NO_TAC, first_x_assum (qspec_then ‘0’ mp_tac) >> simp[] >> NO_TAC]
QED

Theorem EL_conn_hdls:
  ∀rs k. k < LENGTH rs ∧ EL k rs = EConnected (SOME hd) ⇒ MEM hd (conn_hdls rs)
Proof
  Induct >> simp[] >> rpt gen_tac >> ONCE_REWRITE_TAC[conn_hdls_cons] >>
  Cases_on ‘k’ >> simp[] >> strip_tac >> gvs[conn_hdls_def] >> metis_tac[]
QED

Theorem cok1_mono:
  (∀hd. Kp hd ⇒ Kp' hd) ∧ (∀hd. Kp hd ∧ Gp hd ⇒ Gp' hd) ∧ cok1 Kp Gp c ⇒ cok1 Kp' Gp' c
Proof
  rw[cok1_def] >> metis_tac[]
QED

Theorem cres_ok_mono:
  (∀hd. Kp hd ⇒ Kp' hd) ∧ (∀hd. Kp hd ∧ Gp hd ⇒ Gp' hd) ∧ cres_ok Kp Gp x r ⇒ cres_ok Kp' Gp' x r
Proof
  rw[cres_ok_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The invariant at a round's start
   ------------------------------------------------------------------------ *)

Definition cinv_def:
  cinv lfd N st es (R : word64 -> bool) ⇔
    LENGTH st.cs = N ∧ st.nh = es.p.b.nxt ∧
    EVERY (cok1 (λhd. ∃j. j < es.p.b.nxt ∧ hd = hdl lfd j) (λhd. ALOOKUP es.ctbl hd = NONE))
          st.cs ∧
    (∀hd f. hd ∈ R ∧ ALOOKUP es.ctbl hd = SOME f ⇒ cstat_of es f = CRefused)
End

Theorem cinv_conn:
  cinv lfd N st es R ∧ i < LENGTH st.cs ⇒
  (∀hd. EL i st.cs = CPend hd ⇒ ∃j. j < es.p.b.nxt ∧ hd = hdl lfd j) ∧
  (∀hd rest. EL i st.cs = CUp hd rest ⇒
             (∃j. j < es.p.b.nxt ∧ hd = hdl lfd j) ∧ ALOOKUP es.ctbl hd = NONE)
Proof
  rw[cinv_def, EVERY_EL] >> first_x_assum drule >> simp[cok1_def]
QED

Theorem cinv_not_lfd:
  cinv lfd N st es R ∧ es.p.b.nxt < dimword (:64) ⇒ ¬MEM lfd (FLAT (MAP chd st.cs))
Proof
  rpt strip_tac >> gvs[MEM_FLAT, MEM_MAP, MEM_EL] >>
  rename1 ‘EL m (chd (EL i st.cs))’ >>
  drule_all cinv_conn >> strip_tac >>
  Cases_on ‘EL i st.cs’ >> gvs[chd_def] >>
  ‘j + 1 < dimword (:64)’ by simp[] >> metis_tac[hdl_not_lfd]
QED

Theorem cacts_read:
  MEM (i, ERead hd n) (cacts a st R) ⇒
  i < LENGTH st.cs ∧ hd ∈ R ∧ ∃rest. EL i st.cs = CPend hd ∨ EL i st.cs = CUp hd rest
Proof
  strip_tac >> drule cacts_mem >> strip_tac >> simp[] >>
  Cases_on ‘EL i st.cs’ >> gvs[cact1_def] >> every_case_tac >> gvs[]
QED

(* Each action is one L1 accepts, in the state the earlier ones left *)
Theorem client_acts_ok:
  a < 65536 ∧ cinv lfd N st es R ∧ ebund lfd w es ∧ i < LENGTH (cacts a st R) ∧
  eacts lfd pol (w, es) (TAKE i (MAP SND (cacts a st R))) = SOME (rs0, evs0, (wi, esi)) ⇒
  eact_ok lfd esi (EL i (MAP SND (cacts a st R)))
Proof
  strip_tac >> simp[EL_MAP] >>
  ‘MEM (EL i (cacts a st R)) (cacts a st R)’ by simp[EL_MEM] >>
  Cases_on ‘EL i (cacts a st R)’ >> gvs[] >> rename1 ‘MEM (ci, x) _’ >>
  drule cacts_mem >> strip_tac >>
  Cases_on ‘EL ci st.cs’ >> gvs[cact1_def] >> every_case_tac >> gvs[eact_ok_def] >>
  rename1 ‘EL ci st.cs = CUp hd rest’ >>
  drule_all cinv_conn >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  ‘EVERY noshut (TAKE i (MAP SND (cacts a st R)))’
    by (irule EVERY_TAKE >> simp[cacts_noshut]) >>
  ‘ALOOKUP esi.ctbl (hdl lfd j) = NONE’ by metis_tac[eacts_ctbl_none] >>
  simp[]
QED

(* Each result is one the update keeps the invariant with, at the actions' end *)
Theorem client_res_ok:
  cinv lfd N st es R ∧ ebund lfd w es ∧ k < LENGTH (cacts a st R) ∧
  EVERY (λx. ∀l. x ≠ EAccept l) (MAP SND (cacts a st R)) ∧
  eacts lfd pol (w, es) (MAP SND (cacts a st R)) = SOME (rs, evs, (w1, es1)) ⇒
  cres_ok (λhd. ∃j. j < es1.p.b.nxt ∧ hd = hdl lfd j) (λhd. ALOOKUP es1.ctbl hd = NONE)
          (SND (EL k (cacts a st R))) (EL k rs)
Proof
  strip_tac >>
  drule_all eacts_nxt >> strip_tac >>
  ‘LENGTH rs = LENGTH (cacts a st R)’ by (drule eacts_length >> simp[]) >>
  simp[cres_ok_def] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pos last) EL_conn_hdls >> simp[] >> strip_tac >>
      first_x_assum drule >> strip_tac >> qexists_tac ‘j’ >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  ‘MEM (EL k (cacts a st R)) (cacts a st R)’ by simp[EL_MEM] >>
  Cases_on ‘EL k (cacts a st R)’ >> gvs[] >>
  drule cacts_read >> strip_tac >>
  drule_all cinv_conn >> strip_tac >>
  ‘∃j. j < es.p.b.nxt ∧ hd = hdl lfd j’ by metis_tac[] >>
  ‘∀f. ALOOKUP es.ctbl hd = SOME f ⇒ cstat_of es f = CRefused’
    by (rpt strip_tac >> qpat_x_assum ‘cinv _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE[cinv_def]) >>
        first_x_assum (qspecl_then [‘hd’, ‘f’] mp_tac) >> simp[]) >>
  conj_tac >> TRY (qexists_tac ‘j’ >> simp[] >> NO_TAC) >>
  assume_tac (Q.GENL [‘a’, ‘st’, ‘R’] cacts_noshut) >>
  qspecl_then [‘MAP SND (cacts a st R)’, ‘w’, ‘es’, ‘rs’, ‘evs’, ‘w1’, ‘es1’, ‘k’, ‘hd’, ‘n’, ‘y’, ‘j’]
    mp_tac eacts_ctbl_gone >>
  ASM_SIMP_TAC (srw_ss()) [EL_MAP]
QED

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

Theorem cbound_dimword:
  N < cbound ⇒ cbound + N < dimword (:64)
Proof
  simp[cbound_def]
QED

(* The round's connects stay below cbound + N handles *)
Theorem client_nhdls:
  cinv lfd N st es R ∧ es.p.b.nxt < cbound + N ⇒
  es.p.b.nxt + nhdls (MAP SND (cacts a st R)) < cbound + N
Proof
  strip_tac >>
  ‘nhdls (MAP SND (cacts a st R)) ≤ if st.nh < cbound then LENGTH st.cs else 0’
    by simp[nhdls_cacts] >>
  gvs[cinv_def] >> Cases_on ‘es.p.b.nxt < cbound’ >> gvs[]
QED

(* A handle without a connect entry keeps none through the round *)
Theorem round_ctbl_none:
  ebund lfd w es ∧ eacts lfd pol (w, es) acts = SOME (rs, evs, (w1, es1)) ∧
  EVERY noshut acts ∧
  etail lfd pol hs (w1, es1) = SOME (rdy, (w2, es2), log, tevs) ∧
  j < es.p.b.nxt ∧ ALOOKUP es.ctbl (hdl lfd j) = NONE ⇒
  ALOOKUP es2.ctbl (hdl lfd j) = NONE
Proof
  strip_tac >>
  ‘ALOOKUP es1.ctbl (hdl lfd j) = NONE’ by metis_tac[eacts_ctbl_none] >>
  metis_tac[etail_ctbl]
QED

Theorem client_round:
  ∀st es w R.
  a < 65536 ∧ N < cbound ∧ cinv lfd N st es R ∧ ebund lfd w es ∧ esmall lfd es ∧
  es.p.b.nxt < cbound + N ⇒
  ∃rs aevs w1 es1 rdy w2 es2 log tevs.
    eacts lfd (pol : l1p -> word64 -> bool) (w, es) (MAP SND (cacts a st R)) = SOME (rs, aevs, (w1, es1)) ∧
    etail lfd pol (FLAT (MAP chd st.cs)) (w1, es1) = SOME (rdy, (w2, es2), log, tevs) ∧
    esmall lfd es2 ∧ es2.shq = [] ∧ es2.p.b.nxt = es.p.b.nxt + LENGTH (conn_hdls rs) ∧
    es2.p.b.nxt < cbound + N ∧ (∀g. ¬MEM (FConn g) log) ∧
    cinv lfd N (cupd rqs st (cacts a st R) rs) es2 (set rdy)
Proof
  rpt gen_tac >> strip_tac >>
  ‘es.p.b.nxt + nhdls (MAP SND (cacts a st R)) < cbound + N’ by metis_tac[client_nhdls] >>
  ‘cbound + N < dimword (:64)’ by simp[cbound_dimword] >>
  ‘l0_rely w’ by gvs[ebund_def] >>
  ‘es.p.b.nxt + nhdls (MAP SND (cacts a st R)) < dimword (:64)’
    by (qpat_x_assum ‘_ + nhdls _ < _’ mp_tac >> qpat_x_assum ‘N < cbound’ mp_tac >>
        simp[cbound_def]) >>
  ‘∃rs aevs w1 es1.
     eacts lfd pol (w, es) (MAP SND (cacts a st R)) = SOME (rs, aevs, (w1, es1)) ∧
     l0_rely w1 ∧ esmall lfd es1 ∧ es1.p.b.nxt ≤ es.p.b.nxt + nhdls (MAP SND (cacts a st R))’
    by (irule eacts_ok >> simp[] >> rpt strip_tac >> metis_tac[client_acts_ok]) >>
  ‘∃rdy w2 es2 log tevs.
     etail lfd pol (FLAT (MAP chd st.cs)) (w1, es1) = SOME (rdy, (w2, es2), log, tevs) ∧
     l0_rely w2 ∧ esmall lfd es2 ∧ es2.p.b.nxt = es1.p.b.nxt’ by (irule etail_ok >> simp[]) >>
  qexistsl_tac [‘rs’, ‘aevs’, ‘w1’, ‘es1’, ‘rdy’, ‘w2’, ‘es2’, ‘log’, ‘tevs’] >>
  ‘EVERY (λx. ∀l. x ≠ EAccept l) (MAP SND (cacts a st R))’ by simp[cacts_no_accept] >>
  ‘es1.p.b.nxt = es.p.b.nxt + LENGTH (conn_hdls rs)’ by metis_tac[eacts_nxt] >>
  ‘EVERY noshut (MAP SND (cacts a st R))’ by simp[cacts_noshut] >>
  ‘ebund lfd w1 es1’ by metis_tac[eacts_ebund] >>
  ‘es2.shq = []’
    by (qpat_x_assum ‘etail _ _ _ _ = _’ (mp_tac o MATCH_MP etail_shq) >>
        qpat_x_assum ‘ebund lfd w1 es1’ mp_tac >> simp[ebund_def, eown_def]) >>
  ‘LENGTH rs = LENGTH (cacts a st R)’ by (drule eacts_length >> simp[]) >>
  simp[] >> conj_tac
  >- (* no connection accepted *)
     (‘eown lfd es1’ by (qpat_x_assum ‘ebund lfd w1 es1’ mp_tac >> simp[ebund_def]) >>
      ‘es.p.b.nxt < dimword (:64)’
        by (qpat_x_assum ‘es.p.b.nxt < cbound + N’ mp_tac >> qpat_x_assum ‘N < cbound’ mp_tac >>
            simp[cbound_def]) >>
      ‘¬MEM lfd (FLAT (MAP chd st.cs))’ by (drule_all cinv_not_lfd >> simp[]) >>
      drule_all etail_noconn >> simp[]) >>
  (* the invariant *)
  qspecl_then [‘λhd. ∃j. j < es2.p.b.nxt ∧ hd = hdl lfd j’, ‘λhd. ALOOKUP es2.ctbl hd = NONE’,
               ‘cacts a st R’, ‘rs’, ‘st’] mp_tac cupd_props >>
  simp[] >> strip_tac >> simp[cinv_def] >> rpt conj_tac
  >- gvs[cinv_def]
  >- gvs[cinv_def]
  >- (first_x_assum irule >> conj_tac
      >- (rpt strip_tac >>
          irule cres_ok_mono >>
          qexistsl_tac [‘λhd. ALOOKUP es1.ctbl hd = NONE’, ‘λhd. ∃j. j < es1.p.b.nxt ∧ hd = hdl lfd j’] >>
          simp[] >> conj_tac >>
          FIRST [drule_all client_res_ok >> simp[] >> NO_TAC,
                 rpt strip_tac >> drule_all etail_ctbl >> simp[] >> NO_TAC]) >>
      qpat_x_assum ‘cinv _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE[cinv_def]) >>
      irule MONO_EVERY >>
      qexists_tac ‘cok1 (λhd. ∃j. j < es.p.b.nxt ∧ hd = hdl lfd j) (λhd. ALOOKUP es.ctbl hd = NONE)’ >>
      simp[] >> rpt strip_tac >> irule cok1_mono >>
      qexistsl_tac [‘λhd. ALOOKUP es.ctbl hd = NONE’, ‘λhd. ∃j. j < es.p.b.nxt ∧ hd = hdl lfd j’] >>
      simp[] >> rpt strip_tac >>
      FIRST [qexists_tac ‘j’ >> simp[] >> NO_TAC,
             gvs[] >> drule_all round_ctbl_none >> simp[] >> NO_TAC]) >>
  rpt strip_tac >> drule_all etail_rdy_ctbl >> simp[]
QED

(* ------------------------------------------------------------------------
   Every round
   ------------------------------------------------------------------------ *)

Theorem cinv_with_last[simp]:
  cinv lfd N (st with last := l) es R ⇔ cinv lfd N st es R
Proof
  simp[cinv_def]
QED

Theorem cready_SNOC[simp]:
  cready (h ++ [s]) = s.ready
Proof
  simp[cready_def]
QED

Theorem cinv_init:
  cinv lfd N (cstate a N rqs []) einit (cready [])
Proof
  simp[cinv_def, cstate_def, cinit_def, cready_def, einit_def, honestL1PFModelTheory.pinit_def, honestL1ModelTheory.l1init_def,
       EVERY_REPLICATE, cok1_def]
QED

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
  (∀hh. EVERY noshut (new_actions (log_of m) hh)) ∧
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

Theorem client_rounds:
  a < 65536 ∧ N < cbound ∧ l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ⇒
  ∀n. ∃h ws evs logs.
    erounds lfd pol (cifds a N rqs) (cprog a N rqs) (w0, einit) n = SOME (h, ws, evs, logs) ∧
    cinv lfd N (cstate a N rqs h) (SND ws) (cready h) ∧ esmall lfd (SND ws) ∧
    (SND ws).p.b.nxt < cbound + N ∧
    SND (ecm lfd pol (cifds a N rqs) (cprog a N rqs) w0 n) = (SND ws).p.b.nxt ∧
    ∀n'. n' ≤ n ⇒ SND (ecm lfd pol (cifds a N rqs) (cprog a N rqs) w0 n') + 1 < dimword (:64)
Proof
  strip_tac >> Induct
  >- (simp[erounds_def, ecm_def, cinv_init] >> rpt conj_tac
      >- (irule esmall_einit >> metis_tac[small_lfd])
      >- simp[einit_def, honestL1PFModelTheory.pinit_def, honestL1ModelTheory.l1init_def, cbound_def]
      >- simp[einit_def, honestL1PFModelTheory.pinit_def, honestL1ModelTheory.l1init_def]) >>
  pop_assum strip_assume_tac >> PairCases_on ‘ws’ >> gvs[] >>
  ‘ebund lfd ws0 ws1’
    by (drule_at (Pos last) erounds_ebund >> simp[cprog_noshut]) >>
  qspecl_then [‘cstate a N rqs h’, ‘ws1’, ‘ws0’, ‘cready h’] mp_tac client_round >>
  impl_tac >- simp[] >> strip_tac >>
  ‘eshuts (w2, es2) = SOME ((w2, es2), [])’ by (irule eshuts_nil >> first_assum ACCEPT_TAC) >>
  ‘SND (ecm lfd pol (cifds a N rqs) (cprog a N rqs) w0 (SUC n)) = es2.p.b.nxt’
    by (qspecl_then [‘lfd’, ‘pol’, ‘cifds a N rqs’, ‘cprog a N rqs’, ‘w0’, ‘n’, ‘h’, ‘(ws0, ws1)’,
                     ‘evs’, ‘logs’, ‘rs’, ‘aevs’, ‘(w1, es1)’, ‘rdy’, ‘(w2, es2)’, ‘log’, ‘tevs’,
                     ‘(w2, es2)’, ‘[]’] mp_tac
          (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘n’, ‘h’, ‘ws’, ‘evs’, ‘logs’, ‘rs’, ‘aevs’,
                   ‘ws1’, ‘rdy’, ‘ws2’, ‘log’, ‘tevs’, ‘ws3’, ‘shevs’] ecm_step_conns) >>
        simp[cprog_new_actions, cifds_def, cstate_last]) >>
  qexistsl_tac [‘h ++ [ssnap rdy rs]’, ‘(w2, es2)’, ‘evs ++ (aevs ++ tevs ++ [])’, ‘logs ++ [log]’] >>
  rpt conj_tac
  >- (qpat_assum ‘eshuts _ = _’ (fn th =>
        simp[erounds_def, eround_def, cprog_new_actions, cifds_def, cstate_last, th]))
  >- simp[cstate_SNOC, cstep_def, asyncM3WorldTheory.ssnap_def, cstate_last]
  >- simp[]
  >- simp[]
  >- simp[] >>
  rpt strip_tac >> Cases_on ‘n' ≤ n’ >- simp[] >>
  ‘n' = SUC n’ by simp[] >>
  qpat_x_assum ‘es2.p.b.nxt < _’ mp_tac >> qpat_x_assum ‘N < cbound’ mp_tac >>
  simp[cbound_def]
QED

(* C1 (i) and (ii): the hypotheses of client_l1_claim on the L1 run *)
Theorem client_l1_total:
  a < 65536 ∧ N < cbound ∧ l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ⇒
  (∀n. erounds lfd pol (cifds a N rqs) (cprog a N rqs) (w0, einit) n ≠ NONE) ∧
  (∀n. SND (ecm lfd pol (cifds a N rqs) (cprog a N rqs) w0 n) + 1 < dimword (:64))
Proof
  strip_tac >> drule_all client_rounds >> strip_tac >> conj_tac >> gen_tac
  >- (first_x_assum (qspecl_then [‘rqs’, ‘pol’, ‘n’] strip_assume_tac) >> simp[]) >>
  first_x_assum (qspecl_then [‘rqs’, ‘pol’, ‘n’] strip_assume_tac) >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]
QED

(* C1 through E1, without the run hypotheses: along every run of the honest
   L1 in an L0 world, the client's guarantee holds of L1's own history *)
Theorem client_l1_guar:
  2 ≤ N ∧ N < cbound ∧ (∀i. EVERY valid_brequest (rqs i)) ∧ a < 65536 ∧
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ⇒
  client_guar' a N rqs lfd (elv lfd pol (cifds a N rqs) (cprog a N rqs) w0)
    (cifds a N rqs) (cprog a N rqs)
    (pew lfd c pol (cifds a N rqs) (cprog a N rqs) w0 calls)
Proof
  strip_tac >>
  ‘N < cbound ∧ a < 65536’ by simp[] >>
  drule_all client_l1_total >> strip_tac >>
  mp_tac client_l1_claim_holds >> rewrite_tac[client_l1_claim_def] >>
  disch_then irule >> simp[]
QED
