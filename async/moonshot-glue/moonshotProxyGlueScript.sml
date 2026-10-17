(*
  Moonshot step 12 glue: the proxy's guarantee by trace position
  (proxy_safe_l0, step 9) gives its guarantee by episode number
  (proxy_safe_ep, moonshotPairGlue), over l0sysEpisodes' vocabulary.

  ft is the proxy's whole trace in the system run, a prefix of the io of
  its claim; each instant's trace tr px t is a prefix of ft.  Episode a is
  the a-th event of ft that got an fd for a connection (ev_new); prx_of
  maps it to the episode of its backend.

  The hypotheses, besides proxy_safe_l0 (revision 5) and a, b < 2^16, are
  facts about honest L0 answers, as ep_ok ft:
   - opens_ok: every open is seen alike by both vocabularies (the proxy's
     l0_event_opened is ev_new's fd);
   - no open gets fd 0 (step-12 gap B3);
   - ops_live (as for the echo, l0sysEpisodesEcho): a successful send or
     recv is never on an fd closed since an episode last got it;
   - accepts_known: an accept is on a listener the trace opened.

  The bridge: pos_ep (episode a's bytes are position p's), and
  proxy_safe_bridge.
*)
Theory moonshotProxyGlue
Ancestors
  proxyL0StmtsCopy moonshotPairGlue l0sysInv l0sysEpisodesEcho l0sysEpisodes
  honestEchoL0SpecCopy Marshalling
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The hypotheses *)

Definition opens_ok_def:
  opens_ok ev ⇔ l0_event_opened ev = OPTION_MAP FST (ev_new ev)
End

(* An accept is on a listener the trace opened *)
Definition accepts_known_def:
  accepts_known evs ⇔
    ∀p f l. p < LENGTH evs ∧ ev_new (EL p evs) = SOME (f, INR l) ⇒
            ALOOKUP (FOLDL lsn_step [] (TAKE p evs)) l ≠ NONE
End

Definition ep_ok_def:
  ep_ok evs ⇔
    EVERY opens_ok evs ∧ EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) evs ∧ ops_live evs ∧
    accepts_known evs
End

(*---------------------------------------------------------------------------*)
(* Episodes by position *)

(* Position p of evs got an fd for a connection; it is episode ep_idx *)
Definition ep_at_def:
  ep_at evs p ⇔ p < LENGTH evs ∧ ev_new (EL p evs) ≠ NONE
End

Definition ep_idx_def:
  ep_idx evs p = LENGTH (ep_fds (TAKE p evs))
End

(* Episode a's position in ft *)
Definition ep_pos_def:
  ep_pos ft a = @p. ep_at ft p ∧ ep_idx ft p = a
End

(* Front a's backend, by episode number *)
Definition prx_of_def:
  prx_of pr ft a =
    if a < LENGTH (ep_fds ft) ∧ is_front (ep_pos ft a) ft then
      case pr (ep_pos ft a) of
      | SOME q => if ep_at ft q then SOME (ep_idx ft q) else NONE
      | NONE => NONE
    else NONE
End

(*---------------------------------------------------------------------------*)
(* One event *)

Theorem accepted_new:
  l0_event_accepted ev ≠ NONE ⇔ ∃f l. ev_new ev = SOME (f, INR l)
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[l0_event_accepted_def, ev_new_def, l0_ev_res_def] >> every_case_tac >> gvs[]
QED

Theorem connected_new:
  opens_ok ev ∧ l0_event_connected ev ≠ NONE ⇒ ∃f port. ev_new ev = SOME (f, INL port)
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[opens_ok_def, l0_event_opened_def, l0_event_connected_def, l0_event_accepted_def] >>
  gvs[ev_new_def, LET_THM] >> every_case_tac >> gvs[]
QED

Theorem new_connect_port:
  ev_new ev = SOME (f, INL port) ∧ connect_port ev = SOME c ⇒ port = w22n c
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[connect_port_def, ev_new_def, LET_THM] >> every_case_tac >> gvs[]
QED

Theorem new_not_io:
  ev_new ev ≠ NONE ⇒ ev_sent ev = NONE ∧ ev_recvd ev = NONE
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[ev_new_def, ev_sent_def, ev_recvd_def, LET_THM] >> every_case_tac >> gvs[]
QED

Theorem closed_not_io:
  l0_event_closed ev ≠ NONE ⇒ ev_new ev = NONE ∧ ev_sent ev = NONE ∧ ev_recvd ev = NONE
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[l0_event_closed_def, ev_new_def, ev_sent_def, ev_recvd_def, LET_THM] >>
  every_case_tac >> gvs[]
QED

Theorem w22n_pbytes:
  b < 65536 ⇒ w22n (pbytes b) = b
Proof
  strip_tac >> ‘pbytes b = n2w2 b’ by simp[pbytes_def, n2w2_def] >>
  simp[w22n_n2w2]
QED

(*---------------------------------------------------------------------------*)
(* The fold of ep_io *)

Theorem ep_fds_APPEND:
  ep_fds (xs ++ ys) = ep_fds xs ++ ep_fds ys
Proof
  simp[ep_fds_def]
QED

Theorem ep_fds_prefix:
  xs ≼ ys ⇒ LENGTH (ep_fds xs) ≤ LENGTH (ep_fds ys)
Proof
  rw[IS_PREFIX_APPEND] >> simp[ep_fds_APPEND]
QED

Theorem ep_io_APPEND:
  ∀xs opn n.
    ep_io sel j opn n (xs ++ ys) =
    ep_io sel j opn n xs ++
    ep_io sel j (FST (FOLDL m_step (opn, n) xs)) (SND (FOLDL m_step (opn, n) xs)) ys
Proof
  Induct >> simp[ep_io_def, m_step_def] >> rpt gen_tac >>
  Cases_on ‘ev_new h’ >> simp[] >> PairCases_on ‘x’ >> simp[]
QED

Theorem live_after_APPEND:
  ∀xs b. live_after f b (xs ++ ys) = live_after f (live_after f b xs) ys
Proof
  Induct >> simp[live_after_def]
QED

(* No fd maps to j any more *)
Theorem ep_io_dead:
  ∀ys opn n. (∀g. ALOOKUP opn g ≠ SOME j) ∧ j < n ⇒ ep_io sel j opn n ys = []
Proof
  Induct >> simp[ep_io_def] >> rpt strip_tac >>
  Cases_on ‘sel h’ >> TRY (rename1 ‘sel h = SOME y’ >> PairCases_on ‘y’) >> fs[] >>
  Cases_on ‘ev_new h’ >> fs[] >> TRY (rename1 ‘ev_new h = SOME z’ >> PairCases_on ‘z’) >>
  fs[] >> first_x_assum irule >> rw[] >> IF_CASES_TAC >> simp[]
QED

(* The selectors: an open or a close is no send or recv *)
Definition sel_ok_def:
  sel_ok sel ⇔ ∀ev. ev_new ev ≠ NONE ∨ l0_event_closed ev ≠ NONE ⇒ sel ev = NONE
End

Theorem sel_ok_sent:
  sel_ok ev_sent ∧ sel_ok ev_recvd
Proof
  rw[sel_ok_def] >> metis_tac[new_not_io, closed_not_io]
QED

Definition fsel_def:
  fsel sel f ev = case sel ev of SOME (g, bs) => if g = f then bs else [] | NONE => []
End

(* f, closed, still maps to j: nothing more for j *)
Theorem ep_io_closed:
  ∀ys opn n.
    sel_ok sel ∧ ALOOKUP opn f = SOME j ∧ (∀g. g ≠ f ⇒ ALOOKUP opn g ≠ SOME j) ∧ j < n ∧
    f ≠ 0w ∧
    (∀a x b bs. ys = a ++ [x] ++ b ∧ sel x = SOME (f, bs) ∧ bs ≠ [] ⇒ live_after f F a) ⇒
    ep_io sel j opn n ys = []
Proof
  Induct >> simp[ep_io_def] >> rpt strip_tac >>
  ‘(case sel h of SOME (g, bs) => if ALOOKUP opn g = SOME j then bs else [] | NONE => []) = []’
    by (Cases_on ‘sel h’ >> simp[] >> rename1 ‘sel h = SOME y’ >> PairCases_on ‘y’ >>
        rw[] >> Cases_on ‘y0 = f’ >> gvs[] >>
        CCONTR_TAC >>
        first_x_assum (qspecl_then [‘[]’, ‘h’, ‘ys’, ‘y1’] mp_tac) >> simp[live_after_def]) >>
  simp[] >>
  Cases_on ‘ev_new h’ >> simp[]
  >- (first_x_assum irule >> simp[] >> rpt strip_tac >>
      first_x_assum (qspecl_then [‘h :: a’, ‘x’, ‘b’, ‘bs’] mp_tac) >>
      simp[live_after_def] >> rw[]) >>
  PairCases_on ‘x’ >> simp[] >>
  Cases_on ‘x0 = f’
  >- (gvs[] >> irule ep_io_dead >> rw[] >> gvs[]) >>
  first_x_assum irule >> rw[] >>
  first_x_assum (qspecl_then [‘h :: a’, ‘x’, ‘b’, ‘bs’] mp_tac) >>
  simp[live_after_def] >> rw[] >> gvs[]
QED

(* f maps to j and is open: j's bytes are f's, up to f's end *)
Theorem ep_io_alive:
  ∀ys opn n.
    sel_ok sel ∧ ALOOKUP opn f = SOME j ∧ (∀g. g ≠ f ⇒ ALOOKUP opn g ≠ SOME j) ∧ j < n ∧
    f ≠ 0w ∧ EVERY opens_ok ys ∧
    (∀a x b bs. ys = a ++ [x] ++ b ∧ sel x = SOME (f, bs) ∧ bs ≠ [] ⇒ live_after f T a) ⇒
    ep_io sel j opn n ys = FLAT (MAP (fsel sel f) (FST (SPLITP (pos_ends f) ys)))
Proof
  Induct >> simp[ep_io_def, SPLITP] >> rpt strip_tac >>
  Cases_on ‘pos_ends f h’ >> simp[]
  >- ((* h ends f: a close or a reopen *)
      ‘sel h = NONE’
        by (gvs[sel_ok_def, pos_ends_def, opens_ok_def] >> first_x_assum irule >>
            Cases_on ‘ev_new h’ >> gvs[]) >>
      simp[] >>
      Cases_on ‘ev_new h’ >> simp[]
      >- (‘l0_event_closed h = SOME f’ by gvs[pos_ends_def, opens_ok_def] >>
          mp_tac (Q.SPECL [‘ys’, ‘opn’, ‘n’] ep_io_closed) >> simp[] >>
          disch_then irule >> rpt strip_tac >>
          qpat_x_assum ‘∀a x b bs. _ ⇒ live_after _ T _’
            (qspecl_then [‘h :: a’, ‘x’, ‘b’, ‘bs’] mp_tac) >>
          fs[live_after_def]) >>
      PairCases_on ‘x’ >> simp[] >>
      ‘x0 = f’ by (gvs[pos_ends_def, opens_ok_def] >> metis_tac[closed_not_io, NOT_NONE_SOME]) >>
      gvs[] >> irule ep_io_dead >> rw[] >> gvs[]) >>
  (* h does not end f *)
  ‘(case sel h of SOME (g, bs) => if ALOOKUP opn g = SOME j then bs else [] | NONE => []) =
   fsel sel f h’
    by (simp[fsel_def] >> Cases_on ‘sel h’ >> simp[] >> rename1 ‘sel h = SOME y’ >>
        PairCases_on ‘y’ >> rw[] >> gvs[]) >>
  simp[] >>
  ‘∀g r. ev_new h = SOME (g, r) ⇒ g ≠ f’
    by (rpt strip_tac >> gvs[pos_ends_def, opens_ok_def]) >>
  ‘l0_event_closed h ≠ SOME f’ by gvs[pos_ends_def] >>
  ‘¬∃r. ev_new h = SOME (f, r)’ by metis_tac[] >>
  ‘∀a x b bs. ys = a ++ [x] ++ b ∧ sel x = SOME (f, bs) ∧ bs ≠ [] ⇒ live_after f T a’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀a x b bs. _ ⇒ live_after _ T _’
          (qspecl_then [‘h :: a’, ‘x’, ‘b’, ‘bs’] mp_tac) >>
        asm_simp_tac std_ss [live_after_def, APPEND]) >>
  Cases_on ‘ev_new h’ >> fs[] >> TRY (rename1 ‘ev_new h = SOME z’ >> PairCases_on ‘z’) >>
  fs[] >> first_x_assum irule >> rw[] >> fs[] >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Episode a's bytes are position p's *)

Theorem m_of_bound:
  ALOOKUP (FST (m_of evs)) g = SOME i ⇒ i < SND (m_of evs)
Proof
  strip_tac >> imp_res_tac m_of_lookup >> simp[m_of_count]
QED

Theorem split_at:
  ∀ft p. p < LENGTH ft ⇒ ft = TAKE p ft ++ [EL p ft] ++ DROP (SUC p) ft
Proof
  Induct >> rw[] >> Cases_on ‘p’ >> gvs[]
QED

Theorem ep_io_pos:
  sel_ok sel ∧ EVERY opens_ok evs ∧ ep_at evs p ∧ ev_new (EL p evs) = SOME (f, r) ∧
  f ≠ 0w ∧
  (∀a x b bs. evs = a ++ [x] ++ b ∧ sel x = SOME (f, bs) ∧ bs ≠ [] ⇒ live_after f T a) ⇒
  ep_io sel (ep_idx evs p) [] 0 evs =
  FLAT (MAP (fsel sel f) (FST (SPLITP (pos_ends f) (DROP (SUC p) evs))))
Proof
  rw[ep_at_def, ep_idx_def] >>
  drule split_at >> qabbrev_tac ‘pre = TAKE p evs’ >> qabbrev_tac ‘post = DROP (SUC p) evs’ >>
  qabbrev_tac ‘e = EL p evs’ >> strip_tac >>
  ‘sel e = NONE’ by gvs[sel_ok_def] >>
  Cases_on ‘m_of pre’ >> rename1 ‘m_of pre = (opn0, n0)’ >>
  ‘LENGTH (ep_fds pre) = n0’ by metis_tac[m_of_count, SND] >>
  ‘∀g i. ALOOKUP opn0 g = SOME i ⇒ i < n0’ by metis_tac[m_of_bound, FST, SND] >>
  qpat_x_assum ‘evs = _’ (fn th => ONCE_REWRITE_TAC [th] >> assume_tac th) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >>
  simp[ep_io_APPEND, ep_io_unborn, ep_io_def] >>
  irule ep_io_alive >> simp[FOLDL_APPEND, m_step_def] >> rpt conj_tac >>
  TRY (qpat_x_assum ‘EVERY opens_ok _’ mp_tac >>
       qpat_x_assum ‘evs = _’ (fn th => ONCE_REWRITE_TAC [th]) >> simp[EVERY_APPEND] >>
       NO_TAC) >>
  TRY (rpt strip_tac >> res_tac >> gvs[] >> NO_TAC) >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [‘pre ++ [e] ++ a’, ‘x’, ‘b’, ‘bs’] mp_tac) >>
  simp[live_after_APPEND, live_after_def]
QED

Theorem fsel_l0[simp]:
  fsel ev_sent f = l0_event_sent f ∧ fsel ev_recvd f = l0_event_recv f
Proof
  simp[FUN_EQ_THM, fsel_def, event_sent_ev_sent, event_recv_ev_recvd] >>
  rw[] >> every_case_tac >> gvs[]
QED

(* THE BYTES: an episode's bytes, by number, are its bytes by position *)
Theorem pos_ep:
  ep_ok evs ∧ ep_at evs p ⇒
  l0_ep_sent (ep_idx evs p) evs = pos_sent p evs ∧
  l0_ep_recvd (ep_idx evs p) evs = pos_read p evs
Proof
  rw[ep_ok_def] >>
  ‘∃f r. ev_new (EL p evs) = SOME (f, r)’
    by (gvs[ep_at_def] >> Cases_on ‘ev_new (EL p evs)’ >> gvs[] >> metis_tac[pair_CASES]) >>
  ‘p < LENGTH evs’ by gvs[ep_at_def] >>
  ‘f ≠ 0w ∧ opens_ok (EL p evs)’ by (gvs[EVERY_EL] >> metis_tac[]) >>
  ‘pos_fd p evs = SOME f’ by gvs[pos_fd_def, opens_ok_def] >>
  simp[pos_sent_def, pos_read_def, pos_events_def, l0_ep_sent_def, l0_ep_recvd_def] >>
  ‘∀sel. sel_ok sel ∧
         (∀a x b bs. evs = a ++ [x] ++ b ∧ sel x = SOME (f, bs) ∧ bs ≠ [] ⇒ live_after f T a) ⇒
         ep_io sel (ep_idx evs p) [] 0 evs =
         FLAT (MAP (fsel sel f) (FST (SPLITP (pos_ends f) (DROP (SUC p) evs))))’
    by (rpt strip_tac >> irule ep_io_pos >> simp[]) >>
  ‘∀a x b bs. evs = a ++ [x] ++ b ∧ ev_sent x = SOME (f, bs) ∧ bs ≠ [] ⇒ live_after f T a’
    by (rpt strip_tac >> qpat_assum ‘ops_live _’ (mp_tac o REWRITE_RULE [ops_live_def]) >>
        disch_then irule >> metis_tac[]) >>
  ‘∀a x b bs. evs = a ++ [x] ++ b ∧ ev_recvd x = SOME (f, bs) ∧ bs ≠ [] ⇒ live_after f T a’
    by (rpt strip_tac >> qpat_assum ‘ops_live _’ (mp_tac o REWRITE_RULE [ops_live_def]) >>
        disch_then irule >> metis_tac[]) >>
  rpt conj_tac >> REWRITE_TAC [GSYM fsel_l0] >>
  irule ep_io_pos >> fs[sel_ok_sent] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Prefixes *)

Theorem lprefix_prefix:
  evs ≼ ft ∧ LPREFIX (fromList ft) io ⇒ LPREFIX (fromList evs) io
Proof
  strip_tac >> irule LPREFIX_TRANS >> qexists_tac ‘fromList ft’ >>
  simp[LPREFIX_fromList, from_toList]
QED

Theorem prefix_EL_TAKE:
  evs ≼ ft ∧ p < LENGTH evs ⇒ EL p ft = EL p evs ∧ TAKE p ft = TAKE p evs
Proof
  rw[IS_PREFIX_APPEND] >> simp[EL_APPEND1, TAKE_APPEND1]
QED

Theorem ep_ok_prefix:
  evs ≼ ft ∧ ep_ok ft ⇒ ep_ok evs
Proof
  rw[IS_PREFIX_APPEND] >> gvs[ep_ok_def, EVERY_APPEND, ops_live_def, accepts_known_def] >>
  rw[] >>
  TRY (qpat_x_assum ‘∀pre ev post f bs. _’ irule >> simp[] >>
       metis_tac[APPEND_ASSOC] >> NO_TAC) >>
  qpat_x_assum ‘∀p f l'. _’ (qspecl_then [‘p’, ‘f’, ‘l'’] mp_tac) >>
  simp[EL_APPEND1, TAKE_APPEND1]
QED

Theorem pos_unborn:
  LENGTH evs ≤ p ⇒ pos_sent p evs = [] ∧ pos_read p evs = []
Proof
  rw[pos_sent_def, pos_read_def, pos_fd_def]
QED

(* At every instant (a prefix evs of ft) *)
Theorem pos_ep_prefix:
  ep_ok ft ∧ evs ≼ ft ∧ ep_at ft p ⇒
  l0_ep_sent (ep_idx ft p) evs = pos_sent p evs ∧
  l0_ep_recvd (ep_idx ft p) evs = pos_read p evs
Proof
  strip_tac >> Cases_on ‘p < LENGTH evs’
  >- (‘ep_at evs p ∧ ep_idx ft p = ep_idx evs p’
        by (drule_all prefix_EL_TAKE >> strip_tac >> fs[ep_at_def, ep_idx_def] >> metis_tac[]) >>
      simp[] >> irule pos_ep >> simp[] >> metis_tac[ep_ok_prefix]) >>
  simp[pos_unborn] >>
  ‘LENGTH (ep_fds evs) ≤ ep_idx ft p’
    by (simp[ep_idx_def] >> irule ep_fds_prefix >>
        gvs[IS_PREFIX_APPEND, NOT_LESS] >>
        qexists_tac ‘TAKE (p - LENGTH evs) l’ >> simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]) >>
  simp[l0_ep_sent_def, l0_ep_recvd_def, ep_io_unborn]
QED

(*---------------------------------------------------------------------------*)
(* Positions and numbers *)

Theorem TAKE_SUC_EL:
  ∀l n. n < LENGTH l ⇒ TAKE (SUC n) l = TAKE n l ++ [EL n l]
Proof
  Induct >> rw[] >> Cases_on ‘n’ >> gvs[]
QED

Theorem ep_idx_lt:
  ep_at ft p1 ∧ p1 < p2 ∧ p2 ≤ LENGTH ft ⇒
  ep_idx ft p1 < LENGTH (ep_fds (TAKE p2 ft))
Proof
  rw[ep_idx_def, ep_at_def] >>
  ‘TAKE (SUC p1) ft = TAKE p1 ft ++ [EL p1 ft]’ by simp[TAKE_SUC_EL] >>
  ‘TAKE (SUC p1) ft ≼ TAKE p2 ft’
    by (simp[IS_PREFIX_EQ_TAKE] >> qexists_tac ‘SUC p1’ >> simp[TAKE_TAKE]) >>
  drule ep_fds_prefix >> simp[ep_fds_APPEND] >> simp[ep_fds_def] >>
  Cases_on ‘ev_new (EL p1 ft)’ >> gvs[] >> PairCases_on ‘x’ >> simp[]
QED

Theorem ep_idx_bound:
  ep_at ft p ⇒ ep_idx ft p < LENGTH (ep_fds ft)
Proof
  strip_tac >> drule ep_idx_lt >>
  disch_then (qspec_then ‘LENGTH ft’ mp_tac) >> gvs[ep_at_def]
QED

Theorem ep_idx_inj:
  ep_at ft p1 ∧ ep_at ft p2 ∧ ep_idx ft p1 = ep_idx ft p2 ⇒ p1 = p2
Proof
  ‘∀p1 p2. ep_at ft p1 ∧ ep_at ft p2 ∧ p1 < p2 ⇒ ep_idx ft p1 < ep_idx ft p2’
    suffices_by (rpt strip_tac >> CCONTR_TAC >> ‘p1 < p2 ∨ p2 < p1’ by simp[] >>
                 first_assum (qspecl_then [‘p1’, ‘p2’] mp_tac) >>
                 first_x_assum (qspecl_then [‘p2’, ‘p1’] mp_tac) >> simp[]) >>
  rpt strip_tac >> ‘p2 ≤ LENGTH ft’ by fs[ep_at_def] >>
  drule_all ep_idx_lt >> simp[ep_idx_def]
QED

Theorem ep_pos_exists:
  ∀ft a. a < LENGTH (ep_fds ft) ⇒ ∃p. ep_at ft p ∧ ep_idx ft p = a
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[ep_fds_def] >>
  rw[SNOC_APPEND, GSYM ep_fds_def, ep_fds_APPEND] >>
  Cases_on ‘a < LENGTH (ep_fds ft)’
  >- (first_x_assum drule >> strip_tac >> qexists_tac ‘p’ >>
      gvs[ep_at_def, ep_idx_def, EL_APPEND1, TAKE_APPEND1]) >>
  qexists_tac ‘LENGTH ft’ >>
  gvs[ep_at_def, ep_idx_def, EL_APPEND2, TAKE_APPEND1, ep_fds_def] >>
  Cases_on ‘ev_new x’ >> gvs[] >> PairCases_on ‘x'’ >> gvs[]
QED

Theorem ep_pos_thm:
  a < LENGTH (ep_fds ft) ⇒ ep_at ft (ep_pos ft a) ∧ ep_idx ft (ep_pos ft a) = a
Proof
  strip_tac >> simp[ep_pos_def] >> SELECT_ELIM_TAC >> metis_tac[ep_pos_exists]
QED

Theorem ep_pos_idx:
  ep_at ft p ⇒ ep_pos ft (ep_idx ft p) = p
Proof
  strip_tac >> drule ep_idx_bound >> strip_tac >> drule ep_pos_thm >>
  metis_tac[ep_idx_inj]
QED

(*---------------------------------------------------------------------------*)
(* Roles *)

Definition ev_role_def:
  ev_role lst ev =
    case ev_new ev of
    | SOME (_, INL p) => Connected p
    | SOME (_, INR l) => Accepted (case ALOOKUP lst l of SOME p => p | NONE => 0)
    | NONE => Connected 0
End

Theorem ep_roles_LENGTH:
  ∀xs lst. LENGTH (ep_roles lst xs) = LENGTH (ep_fds xs)
Proof
  Induct >> simp[ep_roles_def, ep_fds_def] >> rpt gen_tac >>
  every_case_tac >> fs[ep_fds_def]
QED

Theorem ep_roles_EL:
  ∀pre lst. ev_new e ≠ NONE ⇒
    LENGTH (ep_fds pre) < LENGTH (ep_roles lst (pre ++ e :: post)) ∧
    EL (LENGTH (ep_fds pre)) (ep_roles lst (pre ++ e :: post)) =
    ev_role (FOLDL lsn_step lst pre) e
Proof
  Induct
  >- (simp[ep_roles_def, ep_fds_def, ev_role_def] >> rpt strip_tac >>
      every_case_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then
    ‘case ev_listen h of SOME (l, p) => (l, p) :: lst | NONE => lst’ mp_tac) >>
  simp[] >> strip_tac >>
  ‘lsn_step lst h = case ev_listen h of SOME (l, p) => (l, p) :: lst | NONE => lst’
    by (simp[lsn_step_def] >> Cases_on ‘ev_listen h’ >> simp[] >>
        rename1 ‘SOME y’ >> Cases_on ‘y’ >> simp[]) >>
  ‘ep_fds (h :: pre) = (case ev_new h of SOME (f, _) => [f] | NONE => []) ++ ep_fds pre’
    by simp[ep_fds_def] >>
  pop_assum SUBST1_TAC >> pop_assum SUBST1_TAC >>
  simp[ep_roles_def] >> Cases_on ‘ev_new h’ >> fs[] >>
  rename1 ‘ev_new h = SOME y’ >> PairCases_on ‘y’ >> Cases_on ‘y1’ >> simp[] >>
  REWRITE_TAC [GSYM ADD1, EL, TL] >> fs[]
QED

Theorem role_at:
  ep_at ft p ⇒
  l0_ep_role (ep_idx ft p) ft = SOME (ev_role (FOLDL lsn_step [] (TAKE p ft)) (EL p ft))
Proof
  rw[ep_at_def, ep_idx_def, l0_ep_role_def] >> drule split_at >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> strip_tac >>
  mp_tac (Q.SPECL [‘TAKE p ft’, ‘[]’]
           (Q.INST [‘e’ |-> ‘EL p ft’, ‘post’ |-> ‘DROP (SUC p) ft’] ep_roles_EL)) >>
  pop_assum (fn th => REWRITE_TAC [GSYM th]) >> simp[]
QED

Theorem role_lt:
  l0_ep_role j ft = SOME r ⇒ j < LENGTH (ep_fds ft)
Proof
  rw[l0_ep_role_def, ep_roles_LENGTH]
QED

(* An episode's role, from its event *)
Theorem role_of_ep:
  ep_at ft p ⇒
  (l0_ep_role (ep_idx ft p) ft = SOME (Connected port) ⇔
     ∃f. ev_new (EL p ft) = SOME (f, INL port)) ∧
  ((∃port. l0_ep_role (ep_idx ft p) ft = SOME (Accepted port)) ⇔
     ∃f l. ev_new (EL p ft) = SOME (f, INR l))
Proof
  strip_tac >> drule role_at >> simp[] >> strip_tac >> gvs[ep_at_def] >>
  simp[ev_role_def] >> every_case_tac >> gvs[]
QED

(* A listener's port is a listen's *)
Theorem lsn_port:
  ∀xs lst. ALOOKUP (FOLDL lsn_step lst xs) l = SOME port ⇒
           ALOOKUP lst l = SOME port ∨ ∃ev. MEM ev xs ∧ ev_listen ev = SOME (l, port)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> first_x_assum drule >>
  simp[lsn_step_def] >> Cases_on ‘ev_listen h’ >> simp[] >>
  TRY (rename1 ‘ev_listen h = SOME y’ >> PairCases_on ‘y’) >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem ev_listen_listen:
  ev_listen ev = SOME (l, port) ⇒
  ∃conf bs k. ev = IO_event (ExtCall «sys_listen») conf bs ∧ l0_ev_res bs = SOME (Ok k) ∧
              port = w22n conf
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[ev_listen_def, l0_ev_res_def, LET_THM] >> every_case_tac >> gvs[]
QED

Theorem new_INL_connected:
  opens_ok ev ∧ ev_new ev = SOME (f, INL port) ⇒ l0_event_connected ev ≠ NONE
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[opens_ok_def, l0_event_opened_def, ev_new_def, LET_THM] >>
  gvs[l0_event_accepted_def, AllCaseEqs()] >> every_case_tac >> gvs[]
QED

(*---------------------------------------------------------------------------*)
(* The proxy's clauses, on ft and its prefixes *)

Definition bridge_hyps_def:
  bridge_hyps Bnd pa pb pr io ft ⇔
    proxy_safe_l0 Bnd pa pb pr io ∧ LPREFIX (fromList ft) io ∧ ep_ok ft ∧
    pa < 65536 ∧ pb < 65536
End

Theorem ps_inj:
  bridge_hyps Bnd pa pb pr io ft ∧ pr p = SOME q ∧ pr p' = SOME q ⇒ p = p'
Proof
  rw[bridge_hyps_def, proxy_safe_l0_def] >> metis_tac[]
QED

Theorem ps_at:
  bridge_hyps Bnd pa pb pr io ft ∧ evs ≼ ft ⇒
  (∀conf bs k. MEM (IO_event (ExtCall «sys_listen») conf bs) evs ∧
               l0_ev_res bs = SOME (Ok k) ⇒ conf = pbytes pa) ∧
  (∀q. q < LENGTH evs ∧ l0_event_connected (EL q evs) ≠ NONE ⇒
       connect_port (EL q evs) = SOME (pbytes pb) ∧
       ∃p. p < q ∧ is_front p evs ∧ pr p = SOME q) ∧
  (∀p q. pr p = SOME q ∧ q < LENGTH evs ⇒ l0_event_connected (EL q evs) ≠ NONE) ∧
  ∀p. is_front p evs ⇒
    case pr p of
    | NONE => pos_sent p evs = []
    | SOME q => pos_sent q evs ≼ pos_read p evs ∧ pos_sent p evs ≼ pos_read q evs
Proof
  rw[bridge_hyps_def] >> ‘LPREFIX (fromList evs) io’ by metis_tac[lprefix_prefix] >>
  qpat_x_assum ‘proxy_safe_l0 _ _ _ _ _’ (mp_tac o REWRITE_RULE [proxy_safe_l0_def]) >>
  strip_tac >> first_x_assum drule >> strip_tac >> rpt strip_tac >>
  TRY (metis_tac[] >> NO_TAC) >>
  qpat_x_assum ‘∀p. is_front p evs ⇒ _’ drule >> CASE_TAC >> simp[]
QED

(* A front's role is Accepted pa *)
Theorem front_role:
  bridge_hyps Bnd pa pb pr io ft ∧ ep_at ft p ∧ ev_new (EL p ft) = SOME (f, INR l) ⇒
  l0_ep_role (ep_idx ft p) ft = SOME (Accepted pa)
Proof
  strip_tac >> drule role_at >> simp[ev_role_def] >> strip_tac >>
  ‘accepts_known ft ∧ p < LENGTH ft’ by gvs[bridge_hyps_def, ep_ok_def, ep_at_def] >>
  ‘∃port. ALOOKUP (FOLDL lsn_step [] (TAKE p ft)) l = SOME port’
    by (gvs[accepts_known_def] >> res_tac >> Cases_on ‘ALOOKUP (lsn (TAKE p ft)) l’ >> gvs[]) >>
  simp[] >> drule lsn_port >> simp[] >> strip_tac >>
  drule ev_listen_listen >> strip_tac >> gvs[] >>
  ‘MEM (IO_event (ExtCall «sys_listen») conf bs) ft’ by metis_tac[MEM_TAKE] >>
  drule_then (qspec_then ‘ft’ mp_tac) ps_at >> simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[bridge_hyps_def, w22n_pbytes]
QED

Theorem front_new:
  is_front p ft ⇒ ep_at ft p ∧ ∃f l. ev_new (EL p ft) = SOME (f, INR l)
Proof
  rw[is_front_def, ep_at_def] >> gvs[accepted_new]
QED

(* A backend position is a connect episode, after its front *)
Theorem backend_at:
  bridge_hyps Bnd pa pb pr io ft ∧ is_front p ft ∧ pr p = SOME q ∧ q < LENGTH ft ⇒
  ep_at ft q ∧ p < q ∧ l0_ep_role (ep_idx ft q) ft = SOME (Connected pb)
Proof
  strip_tac >> drule_then (qspec_then ‘ft’ mp_tac) ps_at >> simp[] >> strip_tac >>
  ‘l0_event_connected (EL q ft) ≠ NONE’ by metis_tac[] >>
  ‘opens_ok (EL q ft)’ by gvs[bridge_hyps_def, ep_ok_def, EVERY_EL] >>
  drule_all connected_new >> strip_tac >>
  ‘ep_at ft q’ by simp[ep_at_def] >>
  ‘connect_port (EL q ft) = SOME (pbytes pb)’ by metis_tac[] >>
  ‘port = pb’ by (drule_all new_connect_port >> gvs[bridge_hyps_def, w22n_pbytes]) >>
  ‘∃p'. p' < q ∧ is_front p' ft ∧ pr p' = SOME q’ by metis_tac[] >>
  ‘p' = p’ by metis_tac[ps_inj] >> gvs[] >>
  metis_tac[role_of_ep]
QED

(*---------------------------------------------------------------------------*)
(* The five clauses of proxy_safe_ep *)

Theorem prx_SOME:
  prx_of pr ft a = SOME c ⇔
  a < LENGTH (ep_fds ft) ∧ is_front (ep_pos ft a) ft ∧
  ∃q. pr (ep_pos ft a) = SOME q ∧ ep_at ft q ∧ c = ep_idx ft q
Proof
  rw[prx_of_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Theorem prx_inj:
  bridge_hyps Bnd pa pb pr io ft ∧ prx_of pr ft a = SOME c ∧ prx_of pr ft a' = SOME c ⇒
  a = a'
Proof
  rw[prx_SOME] >> rename1 ‘pr (ep_pos ft a') = SOME q'’ >>
  ‘q = q'’ by metis_tac[ep_idx_inj] >> gvs[] >>
  ‘ep_pos ft a = ep_pos ft a'’ by metis_tac[ps_inj] >>
  metis_tac[ep_pos_thm]
QED

Theorem prx_back:
  bridge_hyps Bnd pa pb pr io ft ∧ prx_of pr ft a = SOME c ⇒
  l0_ep_role c ft = SOME (Connected pb)
Proof
  rw[prx_SOME] >> ‘q < LENGTH ft’ by gvs[ep_at_def] >> metis_tac[backend_at]
QED

Theorem prx_cover:
  bridge_hyps Bnd pa pb pr io ft ∧ l0_ep_role c ft = SOME (Connected pb) ⇒
  ∃a. prx_of pr ft a = SOME c ∧ l0_ep_role a ft = SOME (Accepted pa)
Proof
  strip_tac >> drule role_lt >> strip_tac >> drule ep_pos_thm >> strip_tac >>
  qabbrev_tac ‘q = ep_pos ft c’ >>
  ‘∃f. ev_new (EL q ft) = SOME (f, INL pb)’ by metis_tac[role_of_ep] >>
  ‘q < LENGTH ft ∧ opens_ok (EL q ft)’
    by gvs[bridge_hyps_def, ep_ok_def, EVERY_EL, ep_at_def] >>
  ‘l0_event_connected (EL q ft) ≠ NONE’ by metis_tac[new_INL_connected] >>
  drule_then (qspec_then ‘ft’ mp_tac) ps_at >> simp[] >> strip_tac >>
  ‘∃p. p < q ∧ is_front p ft ∧ pr p = SOME q’ by metis_tac[] >>
  drule front_new >> strip_tac >>
  qexists_tac ‘ep_idx ft p’ >> conj_tac
  >- (simp[prx_SOME, ep_pos_idx, ep_idx_bound] >> gvs[]) >>
  metis_tac[front_role]
QED

Theorem prx_unpaired:
  bridge_hyps Bnd pa pb pr io ft ∧ evs ≼ ft ∧
  l0_ep_role a ft = SOME (Accepted pa) ∧ prx_of pr ft a = NONE ⇒
  l0_ep_sent a evs = []
Proof
  strip_tac >> drule role_lt >> strip_tac >> drule ep_pos_thm >> strip_tac >>
  qabbrev_tac ‘p = ep_pos ft a’ >>
  ‘∃f l. ev_new (EL p ft) = SOME (f, INR l)’ by metis_tac[role_of_ep] >>
  ‘is_front p ft’ by gvs[is_front_def, ep_at_def, accepted_new] >>
  ‘ep_ok ft’ by gvs[bridge_hyps_def] >>
  ‘l0_ep_sent a evs = pos_sent p evs’ by metis_tac[pos_ep_prefix] >> simp[] >>
  Cases_on ‘LENGTH evs ≤ p’ >- simp[pos_unborn] >>
  ‘is_front p evs’ by (gvs[is_front_def, NOT_LESS_EQUAL] >> metis_tac[prefix_EL_TAKE]) >>
  drule_all ps_at >> strip_tac >>
  first_x_assum drule >> Cases_on ‘pr p’ >> simp[] >> rename1 ‘pr p = SOME q’ >>
  ‘¬ep_at ft q’ by (strip_tac >> gvs[prx_of_def]) >>
  ‘LENGTH ft ≤ q’ by (CCONTR_TAC >> gvs[NOT_LESS_EQUAL] >> metis_tac[backend_at]) >>
  ‘LENGTH evs ≤ q’ by (imp_res_tac IS_PREFIX_LENGTH >> simp[]) >>
  simp[pos_unborn]
QED

Theorem prx_relay:
  bridge_hyps Bnd pa pb pr io ft ∧ evs ≼ ft ∧ prx_of pr ft a = SOME c ⇒
  l0_ep_sent c evs ≼ l0_ep_recvd a evs ∧ l0_ep_sent a evs ≼ l0_ep_recvd c evs
Proof
  strip_tac >> fs[prx_SOME] >> qabbrev_tac ‘p = ep_pos ft a’ >>
  drule ep_pos_thm >> strip_tac >>
  ‘q < LENGTH ft’ by gvs[ep_at_def] >>
  ‘p < q’ by metis_tac[backend_at] >>
  ‘ep_ok ft’ by gvs[bridge_hyps_def] >>
  ‘l0_ep_sent a evs = pos_sent p evs ∧ l0_ep_recvd a evs = pos_read p evs ∧
   l0_ep_sent (ep_idx ft q) evs = pos_sent q evs ∧
   l0_ep_recvd (ep_idx ft q) evs = pos_read q evs’ by metis_tac[pos_ep_prefix] >>
  Cases_on ‘LENGTH evs ≤ p’
  >- (‘LENGTH evs ≤ q’ by decide_tac >> fs[pos_unborn]) >>
  ‘EL p ft = EL p evs’ by metis_tac[prefix_EL_TAKE, NOT_LESS_EQUAL] >>
  ‘is_front p evs’ by (qpat_x_assum ‘is_front _ ft’ mp_tac >> fs[is_front_def, Abbr ‘p’]) >>
  drule_all ps_at >> strip_tac >>
  first_x_assum drule >> fs[]
QED

(*---------------------------------------------------------------------------*)
(* THE BRIDGE: the proxy's claim, by position, gives proxy_safe_ep, by
   episode number, on the system's instants *)
Theorem proxy_safe_bridge:
  proxy_safe_l0 Bnd pa pb pr io ∧ LPREFIX (fromList ft) io ∧ ep_ok ft ∧
  pa < 65536 ∧ pb < 65536 ∧
  (∀t. tr px t ≼ ft) ∧ (∀j. rl px j = l0_ep_role j ft) ⇒
  proxy_safe_ep (prx_of pr ft) rl tr px pa pb
Proof
  strip_tac >> ‘bridge_hyps Bnd pa pb pr io ft’ by simp[bridge_hyps_def] >>
  simp[proxy_safe_ep_def] >> rpt conj_tac
  >- metis_tac[prx_inj]
  >- metis_tac[prx_back]
  >- metis_tac[prx_cover]
  >- metis_tac[prx_unpaired] >>
  metis_tac[prx_relay]
QED
