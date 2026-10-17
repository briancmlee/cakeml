(*
  Episode j's sent bytes on the trace (design/47 D, step i, the trace
  side): while episode j is open, l0_sent j is exactly what the sends on
  its fd f took, over the events after j's accept.  Built on the KV
  worker's folds (honestEchoL0Trace: l0_sent j = ep_sn j (0, [])).
*)
Theory honestEchoL0Sent
Ancestors
  honestEchoL0Trace honestEchoL0Spec honestL1BStmts alist
Libs
  preamble

(* An episode the fold has not reached gets no bytes (as honestEchoL0Round's
   ep_fold_fresh, which is behind a theory not yet ported to D23) *)
Theorem ep_fold_unreached:
  ∀evs k opn. ep_ok (k, opn) ∧ FST (l0_ep_st (k, opn) evs) ≤ j ⇒
              ep_fold pf fdf j (k, opn) evs = []
Proof
  Induct >> simp[ep_fold_def] >> rpt gen_tac >> strip_tac >>
  ‘k ≤ FST (l0_ep_step (k, opn) h)’
    by (simp[l0_ep_step_def] >> every_case_tac >> simp[]) >>
  ‘FST (l0_ep_st (l0_ep_step (k, opn) h) evs) ≤ j’ by fs[] >>
  ‘FST (l0_ep_st (l0_ep_step (k, opn) h) evs) =
   FST (l0_ep_step (k, opn) h) + LENGTH (l0_accepted evs)’
    by (Cases_on ‘l0_ep_step (k, opn) h’ >> simp[FST_l0_ep_st]) >>
  conj_tac
  >- (every_case_tac >> simp[] >> gvs[ep_ok_def, EVERY_MEM] >>
      imp_res_tac ALOOKUP_MEM >>
      ‘MEM j (MAP SND opn)’ by (simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
      res_tac >> fs[]) >>
  Cases_on ‘l0_ep_step (k, opn) h’ >> first_x_assum irule >> fs[] >>
  metis_tac[ep_ok_step]
QED

Theorem ep_ok_st:
  ∀evs s. ep_ok s ⇒ ep_ok (l0_ep_st s evs)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >> metis_tac[ep_ok_step]
QED

Theorem send_fd_accepted:
  l0_event_accepted ev = SOME f ⇒ send_fd ev = NONE
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bs’ >> Cases_on ‘nm’ >>
  rw[l0_event_accepted_def, send_fd_def]
QED

Theorem event_sent_other:
  send_fd ev ≠ SOME f ⇒ l0_event_sent f ev = []
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bs’ >> Cases_on ‘nm’ >>
  rw[l0_event_sent_def, send_fd_def]
QED

Theorem alookup_snd_inj[local]:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ ALOOKUP l a = SOME v ∧ ALOOKUP l b = SOME v ⇒ a = b
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[AllCaseEqs()] >>
  imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

(* While f stays open in episode j, the fold collects exactly f's sends *)
Theorem ep_sn_open:
  ∀post s. ep_ok s ∧ ALOOKUP (SND s) f = SOME j ∧ EVERY (λe. ¬ep_ends f e) post ⇒
           ep_sn j s post = FLAT (MAP (l0_event_sent f) post)
Proof
  Induct >> simp[ep_fold_def] >> rpt gen_tac >> PairCases_on ‘s’ >> strip_tac >>
  irule (METIS_PROVE [] “(a:word8 list) = c ∧ b = d ⇒ a ++ b = c ++ d”) >> fs[] >>
  conj_tac
  >- (Cases_on ‘send_fd h’ >> simp[]
      >- (fs[] >> metis_tac[event_sent_other, optionTheory.NOT_SOME_NONE]) >>
      rename1 ‘send_fd h = SOME g’ >> Cases_on ‘g = f’ >> gvs[] >>
      ‘ALOOKUP s1 g ≠ SOME j’
        by (strip_tac >> fs[ep_ok_def] >> metis_tac[alookup_snd_inj]) >>
      rw[] >> metis_tac[event_sent_other, optionTheory.SOME_11]) >>
  first_x_assum irule >> fs[ep_ends_def] >> conj_tac
  >- metis_tac[ep_ok_step] >>
  simp[l0_ep_step_def] >> every_case_tac >> gvs[ALOOKUP_ADELKEY]
QED

(* MAIN (trace side): an open episode's sent bytes *)
Theorem l0_sent_open:
  evs = pre ++ [ev] ++ post ∧ LENGTH (l0_accepted pre) = j ∧
  l0_event_accepted ev = SOME f ∧ EVERY (λe. ¬ep_ends f e) post ⇒
  l0_sent j evs = FLAT (MAP (l0_event_sent f) post)
Proof
  rw[l0_sent_fold, ep_fold_APPEND] >>
  ‘ep_ok (0, [])’ by simp[ep_ok_def] >>
  ‘ep_sn (LENGTH (l0_accepted pre)) (0, []) pre = []’
    by (irule ep_fold_unreached >> simp[FST_l0_ep_st]) >>
  Cases_on ‘l0_ep_st (0, []) pre’ >> rename1 ‘_ = (k, opn)’ >>
  ‘k = LENGTH (l0_accepted pre)’
    by (qspecl_then [‘pre’, ‘0’, ‘[]’] mp_tac FST_l0_ep_st >> simp[]) >>
  ‘ep_ok (k, opn)’ by metis_tac[ep_ok_st] >>
  ‘ep_ok (l0_ep_step (k, opn) ev)’ by metis_tac[ep_ok_step] >>
  imp_res_tac send_fd_accepted >>
  gvs[ep_fold_def, l0_ep_step_def] >>
  irule ep_sn_open >> simp[]
QED
