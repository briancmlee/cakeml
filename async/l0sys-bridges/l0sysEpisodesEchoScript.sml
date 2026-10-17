(*
  The two notions of an L0 episode agree (the coordinator's requirement,
  2026-10-17): for a process that makes no sys_connect, l0sysEpisodes'
  l0_ep_recvd/l0_ep_sent are honestEchoL0Spec's l0_read/l0_sent, episode
  by episode, and the episodes are numbered alike (l0_ep_echo).

  Where they differ, and why it is harmless:
   - honestEchoL0Spec ends an episode at the first successful close of its
     fd; l0sysEpisodes gives a send or recv on f to the latest episode that
     got f.  These differ only for a successful send or recv on f after a
     successful close of f, before f is handed out again (ops_live rules
     it out).  An L0 world never answers such a call successfully: a
     successful send or recv needs a channel fd, close frees the fd, and
     only connect and accept hand a channel fd out (l0sys_ops_live, B2).
   - an episode on fd 0: l0sysEpisodes counts it but gives it no bytes
     (fd 0 is open from the start, so this needs the program to close its
     fd 0; see ep_io).  The theorem excludes episodes on fd 0.
*)
Theory l0sysEpisodesEcho
Ancestors
  honestL0World l0sysEpisodes honestEchoL0SpecCopy
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The hypotheses *)

Definition no_connect_def:
  no_connect ev ⇔ ∀conf bl. ev ≠ IO_event (ExtCall «sys_connect») conf bl
End

(* After evs, fd f has not been closed (successfully) since an episode last
   got it; b: what to say if neither happened *)
Definition live_after_def:
  live_after f b [] = b ∧
  live_after f b (ev :: evs) =
    live_after f (if (∃h. ev_new ev = SOME (f, h)) then T
                  else if l0_event_closed ev = SOME f then F else b) evs
End

(* A successful send or recv with bytes, on an fd other than 0, is never on
   an fd closed since an episode last got it *)
Definition ops_live_def:
  ops_live evs ⇔
    ∀pre ev post f bs.
      evs = pre ++ [ev] ++ post ∧ (ev_sent ev = SOME (f, bs) ∨ ev_recvd ev = SOME (f, bs)) ∧
      bs ≠ [] ∧ f ≠ 0w ⇒ live_after f T pre
End

(*---------------------------------------------------------------------------*)
(* The two definitions as left folds *)

Definition m_step_def:
  m_step (opn, n) ev =
    case ev_new ev of
    | SOME (f, _) => ((if f = 0w then opn else (f, n :num) :: opn), n + 1)
    | NONE => (opn, n)
End

Definition t_step_def:
  t_step (k, opn) ev =
    case l0_event_accepted ev of
    | SOME f => (k + 1 : num, (f, k) :: ADELKEY f opn)
    | NONE =>
        case l0_event_closed ev of
        | SOME f => (k, ADELKEY f opn)
        | NONE => (k, opn)
End

Theorem ep_io_SNOC:
  ∀evs opn n.
    ep_io sel j opn n (evs ++ [ev]) =
    ep_io sel j opn n evs ++
    (case sel ev of
     | SOME (f, bs) => if ALOOKUP (FST (FOLDL m_step (opn, n) evs)) f = SOME j then bs else []
     | NONE => [])
Proof
  Induct >> simp[ep_io_def]
  >- (Cases_on ‘sel ev : (word64 # word8 list) option’ >> simp[] >> TRY (PairCases_on ‘x’) >> simp[] >>
      Cases_on ‘ev_new ev’ >> simp[ep_io_def] >> PairCases_on ‘x’ >> simp[ep_io_def]) >>
  rpt gen_tac >> simp[m_step_def] >> Cases_on ‘ev_new h’ >> simp[] >>
  PairCases_on ‘x’ >> simp[]
QED

Theorem l0_ep_events_SNOC:
  ∀evs k opn.
    l0_ep_events j k opn (evs ++ [ev]) =
    l0_ep_events j k opn evs ++
    (if MEM j (MAP SND (SND (FOLDL t_step (k, opn) evs))) then [ev] else [])
Proof
  Induct >> simp[l0_ep_events_def]
  >- (rpt gen_tac >> Cases_on ‘l0_event_accepted ev’ >> simp[l0_ep_events_def] >>
      Cases_on ‘l0_event_closed ev’ >> simp[l0_ep_events_def]) >>
  rpt gen_tac >> simp[t_step_def] >>
  Cases_on ‘l0_event_accepted h’ >> simp[] >> Cases_on ‘l0_event_closed h’ >> simp[]
QED

Theorem l0_accepted_SNOC:
  l0_accepted (evs ++ [ev]) =
  l0_accepted evs ++ (case l0_event_accepted ev of SOME f => [f] | NONE => [])
Proof
  rw[l0_accepted_def] >> every_case_tac >> simp[]
QED

Theorem live_after_SNOC:
  ∀evs b.
    live_after f b (evs ++ [ev]) =
    if (∃h. ev_new ev = SOME (f, h)) then T
    else if l0_event_closed ev = SOME f then F else live_after f b evs
Proof
  Induct >> rw[live_after_def]
QED

(*---------------------------------------------------------------------------*)
(* One event *)

Theorem no_connect_ev_new:
  no_connect ev ⇒ OPTION_MAP FST (ev_new ev) = l0_event_accepted ev
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[no_connect_def, ev_new_def, l0_event_accepted_def, l0_ev_res_def] >>
  every_case_tac >> gvs[]
QED

Theorem accepted_not_closed:
  l0_event_accepted ev = SOME f ⇒ l0_event_closed ev = NONE
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[l0_event_accepted_def, l0_event_closed_def] >> gvs[]
QED

Theorem event_recv_ev_recvd:
  l0_event_recv g ev =
  case ev_recvd ev of SOME (f, bs) => if f = g then bs else [] | NONE => []
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[l0_event_recv_def, ev_recvd_def, l0_ev_res_def, l0_hdr_def] >>
  every_case_tac >> gvs[]
QED

Theorem event_sent_ev_sent:
  l0_event_sent g ev =
  case ev_sent ev of SOME (f, bs) => if f = g then bs else [] | NONE => []
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[l0_event_sent_def, ev_sent_def, l0_ev_res_def] >>
  every_case_tac >> gvs[]
QED

(*---------------------------------------------------------------------------*)
(* The invariant between the two folds *)

Definition echo_rel_def:
  echo_rel evs ⇔
    let m = FOLDL m_step ([], 0) evs; t = FOLDL t_step (0, []) evs;
        acc = l0_accepted evs in
      SND m = LENGTH acc ∧ FST t = LENGTH acc ∧
      ALL_DISTINCT (MAP FST (SND t)) ∧
      (∀f i. MEM (f, i) (SND t) ⇒ i < LENGTH acc ∧ EL i acc = f) ∧
      (∀f i. f ≠ 0w ∧ ALOOKUP (SND t) f = SOME i ⇒ ALOOKUP (FST m) f = SOME i) ∧
      (∀f i. f ≠ 0w ∧ live_after f T evs ∧ ALOOKUP (FST m) f = SOME i ⇒
             ALOOKUP (SND t) f = SOME i) ∧
      ALOOKUP (FST m) 0w = NONE
End

Theorem MEM_ADELKEY_pair:
  MEM (a, b) (ADELKEY k l) ⇔ MEM (a, b) l ∧ a ≠ k
Proof
  simp[ADELKEY_def, MEM_FILTER] >> metis_tac[]
QED

Theorem ALL_DISTINCT_ADELKEY:
  ALL_DISTINCT (MAP FST l) ⇒ ALL_DISTINCT (MAP FST (ADELKEY k l))
Proof
  simp[ADELKEY_def] >> Induct_on ‘l’ >> rw[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem echo_rel_FOLDL:
  ∀evs. EVERY no_connect evs ⇒ echo_rel evs
Proof
  ho_match_mp_tac SNOC_INDUCT >> conj_tac
  >- simp[echo_rel_def, live_after_def, l0_accepted_def] >>
  rw[SNOC_APPEND] >> gvs[] >>
  ‘no_connect x’ by gvs[EVERY_APPEND] >>
  drule no_connect_ev_new >> strip_tac >>
  gvs[echo_rel_def, FOLDL_APPEND, l0_accepted_SNOC, live_after_SNOC] >>
  Cases_on ‘FOLDL m_step ([],0) evs’ >> Cases_on ‘FOLDL t_step (0,[]) evs’ >> gvs[] >>
  Cases_on ‘ev_new x’ >> gvs[]
  >- ((* not an accept: maybe a close *)
      simp[m_step_def, t_step_def] >>
      Cases_on ‘l0_event_closed x’ >>
      gvs[ALOOKUP_ADELKEY, MEM_ADELKEY_pair, ALL_DISTINCT_ADELKEY] >>
      rw[] >> gvs[] >> res_tac >> gvs[]) >>
  (* an accept of fd g *)
  rename1 ‘ev_new x = SOME z’ >> PairCases_on ‘z’ >> gvs[] >>
  qpat_x_assum ‘SOME _ = _’ (assume_tac o GSYM) >>
  rename1 ‘l0_event_accepted x = SOME g’ >>
  drule accepted_not_closed >> strip_tac >>
  simp[m_step_def, t_step_def] >>
  gvs[ALOOKUP_ADELKEY, MEM_ADELKEY_pair, ALL_DISTINCT_ADELKEY, MEM_MAP, EL_APPEND1,
      EL_APPEND2, FORALL_PROD] >>
  rw[] >> gvs[EL_APPEND1, EL_APPEND2] >> res_tac >> gvs[EL_APPEND1]
QED

(*---------------------------------------------------------------------------*)
(* The bytes agree *)

(* No episode j yet: honestEchoL0Spec's episode j has no events *)
Theorem l0_ep_events_unborn:
  EVERY no_connect evs ∧ LENGTH (l0_accepted evs) ≤ j ⇒ l0_ep_events j 0 [] evs = []
Proof
  qid_spec_tac ‘evs’ >> ho_match_mp_tac SNOC_INDUCT >>
  rw[SNOC_APPEND, l0_ep_events_def, l0_ep_events_SNOC, l0_accepted_SNOC] >>
  gvs[EVERY_APPEND] >>
  drule echo_rel_FOLDL >> simp[echo_rel_def] >>
  Cases_on ‘FOLDL t_step (0,[]) evs’ >> simp[] >> strip_tac >>
  IF_CASES_TAC >> gvs[MEM_MAP] >> rename1 ‘MEM y _’ >> Cases_on ‘y’ >> res_tac >> gvs[]
QED

(* For sel and the matching per-fd selector of honestEchoL0Spec *)
Theorem ep_io_echo:
  (∀g ev. tsel g ev = case sel ev of SOME (f, bs) => if f = g then bs else [] | NONE => []) ⇒
  ∀evs. EVERY no_connect evs ∧
        (∀pre ev post f bs. evs = pre ++ [ev] ++ post ∧ sel ev = SOME (f, bs) ∧
                            bs ≠ [] ∧ f ≠ 0w ⇒ live_after f T pre) ⇒
        ∀g. g ≠ 0w ∧ (j < LENGTH (l0_accepted evs) ⇒ EL j (l0_accepted evs) = g) ⇒
            ep_io sel j [] 0 evs = FLAT (MAP (tsel g) (l0_ep_events j 0 [] evs))
Proof
  strip_tac >> ho_match_mp_tac SNOC_INDUCT >> conj_tac
  >- simp[ep_io_def, l0_ep_events_def] >>
  rw[SNOC_APPEND, ep_io_SNOC, l0_ep_events_SNOC] >> gvs[EVERY_APPEND] >>
  first_x_assum (qspec_then ‘g’ mp_tac) >> impl_tac
  >- (rw[]
      >- (qpat_x_assum ‘_ < LENGTH (l0_accepted (_ ++ _)) ⇒ _’ mp_tac >>
          simp[l0_accepted_SNOC, EL_APPEND1]) >>
      qpat_x_assum ‘∀pre ev post f bs. _ ++ [_] = _ ⇒ _’
        (qspecl_then [‘pre’, ‘ev’, ‘post ++ [x]’, ‘f’, ‘bs’] mp_tac) >> simp[]) >>
  strip_tac >> simp[] >>
  drule echo_rel_FOLDL >> simp[echo_rel_def] >>
  Cases_on ‘FOLDL m_step ([],0) evs’ >> Cases_on ‘FOLDL t_step (0,[]) evs’ >> simp[] >>
  strip_tac >> gvs[] >>
  Cases_on ‘sel x’ >> simp[] >- rw[] >>
  rename1 ‘sel x = SOME y’ >> PairCases_on ‘y’ >> rename1 ‘sel x = SOME (f, bs)’ >> simp[] >>
  Cases_on ‘bs = []’ >- rw[] >>
  Cases_on ‘f = 0w’ >- (rw[] >> gvs[]) >>
  ‘live_after f T evs’
    by (first_x_assum (qspecl_then [‘evs’, ‘x’, ‘[]’, ‘f’, ‘bs’] mp_tac) >> simp[]) >>
  rename1 ‘FOLDL t_step _ _ = (_, r)’ >>
  Cases_on ‘ALOOKUP r f = SOME j’
  >- (‘ALOOKUP q f = SOME j’
        by (qpat_x_assum ‘∀f i. f ≠ 0w ∧ ALOOKUP r _ = _ ⇒ _’ irule >> simp[]) >>
      ‘MEM (f, j) r’ by (irule ALOOKUP_MEM >> simp[]) >>
      ‘j < LENGTH (l0_accepted evs) ∧ EL j (l0_accepted evs) = f’ by (qpat_x_assum ‘∀f i. MEM _ r ⇒ _’ drule >> simp[]) >>
      ‘MEM j (MAP SND r)’ by (simp[MEM_MAP, EXISTS_PROD] >> qexists_tac ‘f’ >> simp[]) >>
      gvs[l0_accepted_SNOC, EL_APPEND1]) >>
  ‘ALOOKUP q f ≠ SOME j’
    by (strip_tac >> qpat_x_assum ‘∀f i. f ≠ 0w ∧ live_after _ _ _ ∧ _ ⇒ _’ drule_all >>
        simp[]) >> simp[] >>
  rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
  rename1 ‘MEM (f', j) r’ >>
  ‘j < LENGTH (l0_accepted evs) ∧ EL j (l0_accepted evs) = f'’ by (qpat_x_assum ‘∀f i. MEM _ r ⇒ _’ drule >> simp[]) >>
  gvs[l0_accepted_SNOC, EL_APPEND1] >>
  rw[] >> gvs[] >> drule_all ALOOKUP_ALL_DISTINCT_MEM >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* The bridge *)

(* The episodes are numbered alike *)
Theorem l0_ep_echo_count:
  ∀evs lst. EVERY no_connect evs ⇒ LENGTH (ep_roles lst evs) = LENGTH (l0_accepted evs)
Proof
  Induct >> simp[ep_roles_def, l0_accepted_def] >> rw[] >>
  drule no_connect_ev_new >> Cases_on ‘ev_new h’ >> simp[] >> strip_tac >>
  gvs[GSYM l0_accepted_def] >>
  rename1 ‘ev_new h = SOME y’ >> PairCases_on ‘y’ >> Cases_on ‘y1’ >>
  qpat_x_assum ‘SOME _ = _’ (assume_tac o GSYM) >> gvs[GSYM l0_accepted_def]
QED

(* THE BRIDGE: for a process that makes no sys_connect, in every episode
   whose fd is not 0, l0sysEpisodes' bytes are honestEchoL0Spec's *)
Theorem l0_ep_echo:
  EVERY no_connect evs ∧ ops_live evs ∧
  (j < LENGTH (l0_accepted evs) ⇒ EL j (l0_accepted evs) ≠ 0w) ⇒
  l0_ep_recvd j evs = l0_read j evs ∧ l0_ep_sent j evs = l0_sent j evs
Proof
  strip_tac >>
  qabbrev_tac ‘g = if j < LENGTH (l0_accepted evs) then EL j (l0_accepted evs) else 1w’ >>
  ‘g ≠ 0w ∧ (j < LENGTH (l0_accepted evs) ⇒ EL j (l0_accepted evs) = g)’
    by (rw[Abbr ‘g’]) >>
  ‘LENGTH (l0_accepted evs) ≤ j ⇒ l0_ep_events j 0 [] evs = []’
    by metis_tac[l0_ep_events_unborn] >>
  ‘ep_io ev_sent j [] 0 evs = FLAT (MAP (l0_event_sent g) (l0_ep_events j 0 [] evs))’
    by (irule ep_io_echo >> simp[event_sent_ev_sent] >> gvs[ops_live_def] >> metis_tac[]) >>
  ‘ep_io ev_recvd j [] 0 evs = FLAT (MAP (l0_event_recv g) (l0_ep_events j 0 [] evs))’
    by (irule ep_io_echo >> simp[event_recv_ev_recvd] >> gvs[ops_live_def] >> metis_tac[]) >>
  simp[l0_ep_recvd_def, l0_ep_sent_def, l0_read_def, l0_sent_def] >>
  rw[] >> gvs[NOT_LESS]
QED
