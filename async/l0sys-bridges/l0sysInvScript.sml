(*
  The per-process invariant behind B2 (l0sys_causal): how a process's own
  trace (l0sysEpisodes) sits on its L0 state.

  cs lists, for each episode of the trace, its channel in the L0 state.
  pinv evs w cs says: an open channel fd other than 0 is the fd of the
  latest episode that got it, and a channel's episode got the channel's fd
  (a failed connect may leave a socket on fd 0, once the program has closed
  its fd 0, that is no episode's); an episode's sends are
  its channel's sent bytes, and what its recvs returned, followed by the
  channel's inbox, is what the peer sent (a prefix of it once a break
  flushed the inbox); and the connections queued on a listener have no fd,
  belong to no episode and have sent nothing yet.

  The invariant holds after every arrival (pinv_deliver), every call
  (pinv_call) and close_all (pinv_close_all).
*)
Theory l0sysInv
Ancestors
  honestL0 honestL0World honestL0Rely honestL0WorldProps l0sys l0sysEpisodes l0sysEpisodesEcho
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The trace side *)

(* The fds the episodes got, in order (fd 0 included) *)
Definition ep_fds_def:
  ep_fds evs = FLAT (MAP (λev. case ev_new ev of SOME (f, _) => [f] | NONE => []) evs)
End

Overload m_of = “λevs. FOLDL m_step ([], 0) evs”

Definition lsn_step_def:
  lsn_step lst ev = case ev_listen ev of SOME lp => lp :: lst | NONE => lst
End

Overload lsn = “λevs. FOLDL lsn_step [] evs”

Theorem ep_fds_SNOC:
  ep_fds (evs ++ [ev]) =
  ep_fds evs ++ (case ev_new ev of SOME (f, _) => [f] | NONE => [])
Proof
  simp[ep_fds_def]
QED

Theorem m_of_count:
  ∀evs. SND (m_of evs) = LENGTH (ep_fds evs)
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[ep_fds_def] >>
  rw[SNOC_APPEND, FOLDL_APPEND] >>
  Cases_on ‘m_of evs’ >> gvs[m_step_def, GSYM ep_fds_def] >>
  every_case_tac >> gvs[]
QED

(* The episode an fd is mapped to got that fd *)
Theorem m_of_lookup:
  ∀evs f j. ALOOKUP (FST (m_of evs)) f = SOME j ⇒
            j < LENGTH (ep_fds evs) ∧ EL j (ep_fds evs) = f ∧ f ≠ 0w
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[] >>
  simp[SNOC_APPEND, FOLDL_APPEND, ep_fds_SNOC] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >>
  ‘SND (m_of evs) = LENGTH (ep_fds evs)’ by simp[m_of_count] >>
  Cases_on ‘m_of evs’ >> gvs[m_step_def] >>
  Cases_on ‘ev_new x’ >> gvs[] >- (strip_tac >> res_tac >> simp[]) >>
  rename1 ‘ev_new x = SOME y’ >> PairCases_on ‘y’ >> gvs[] >>
  Cases_on ‘y0 = 0w’ >> gvs[] >- (strip_tac >> res_tac >> simp[EL_APPEND1]) >>
  Cases_on ‘y0 = f’ >> gvs[EL_APPEND2] >> strip_tac >> res_tac >> simp[EL_APPEND1]
QED

(* No episode j yet: it has no bytes *)
Theorem ep_io_unborn:
  LENGTH (ep_fds evs) ≤ j ⇒ ep_io sel j [] 0 evs = []
Proof
  qid_spec_tac ‘evs’ >> ho_match_mp_tac SNOC_INDUCT >> simp[ep_io_def] >>
  rw[SNOC_APPEND, ep_io_SNOC, ep_fds_SNOC] >>
  every_case_tac >> gvs[] >> imp_res_tac m_of_lookup >> gvs[]
QED

(*---------------------------------------------------------------------------*)
(* The invariant *)

(* What the recvs returned (r), then the inbox, is what the peer sent; a
   prefix once a break has flushed the inbox *)
Definition in_ok_def:
  in_ok r (c : lchan) ⇔
    r ++ c.inbox ≼ c.peer_sent ∧ (¬c.broken ⇒ r ++ c.inbox = c.peer_sent)
End

(* TEMPORARY VERBATIM COPY (remove at merge, use the original): fds_lt of
   honestL0WorldProps on final/L3-02-world-facts (async/kernel/world,
   @ cc5ebb5e3): the fds in use are below the fd limit *)
Definition fds_lt_def:
  fds_lt (w : l0world) ⇔ ∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit
End

Definition pinv_def:
  pinv evs (w : l0world) cs ⇔
    fds_lt w ∧
    LENGTH cs = LENGTH (ep_fds evs) ∧ ALL_DISTINCT cs ∧
    EVERY (λc. c < LENGTH w.chans) cs ∧
    EVERY (λ(f, c). c < LENGTH w.chans) w.open_fds ∧
    (∀f c. l0_chan_of w f = SOME c ⇒
           (∀j. j < LENGTH cs ∧ EL j cs = c ⇒ EL j (ep_fds evs) = f) ∧
           (f ≠ 0w ⇒ ∃j. j < LENGTH cs ∧ EL j cs = c ∧ ALOOKUP (FST (m_of evs)) f = SOME j)) ∧
    (∀j. j < LENGTH cs ∧ EL j (ep_fds evs) ≠ 0w ⇒
         ep_io ev_sent j [] 0 evs = (EL (EL j cs) w.chans).sent ∧
         in_ok (ep_io ev_recvd j [] 0 evs) (EL (EL j cs) w.chans)) ∧
    ALL_DISTINCT (MAP FST w.listeners) ∧
    ALL_DISTINCT (FLAT (MAP (SND o SND) w.listeners)) ∧
    (∀l p q. MEM (l, p, q) w.listeners ⇒
       ALOOKUP (lsn evs) l = SOME p ∧
       ∀c. MEM c q ⇒ c < LENGTH w.chans ∧ ¬MEM c cs ∧ (∀f. l0_chan_of w f ≠ SOME c) ∧
                     (EL c w.chans).sent = [] ∧ in_ok [] (EL c w.chans))
End

Theorem pinv_init:
  w.listeners = [] ∧ w.chans = [] ∧ w.open_fds = [] ∧ fds_lt w ⇒ pinv [] w []
Proof
  rw[pinv_def, ep_fds_def, l0_chan_of_def]
QED

(* Clock and history are not in it *)
Theorem pinv_clock_hist[simp]:
  pinv evs (w with <| clock := n; hist := h |>) cs ⇔ pinv evs w cs
Proof
  simp[pinv_def, l0_chan_of_def, fds_lt_def, l0_used_def]
QED

(*---------------------------------------------------------------------------*)
(* Updating one channel *)

Theorem m_step_none:
  ev_new ev = NONE ⇒ m_step x ev = x
Proof
  Cases_on ‘x’ >> simp[m_step_def]
QED

Theorem fds_lt_upd[simp]:
  fds_lt (upd_lchan c g w) ⇔ fds_lt w
Proof
  simp[fds_lt_def, l0_used_def, upd_lchan_def]
QED

Theorem fds_lt_chans[simp]:
  fds_lt (w with chans := X) ⇔ fds_lt w
Proof
  simp[fds_lt_def, l0_used_def]
QED

Theorem fds_lt_listeners_chans:
  MAP FST L = MAP FST w.listeners ⇒
  (fds_lt (w with <| listeners := L; chans := X |>) ⇔ fds_lt w)
Proof
  simp[fds_lt_def, l0_used_def]
QED


Theorem l0_chan_of_upd[simp]:
  l0_chan_of (upd_lchan c g w) f = l0_chan_of w f
Proof
  simp[l0_chan_of_def, upd_lchan_def]
QED

Theorem upd_lchan_listeners[simp]:
  (upd_lchan c g w).listeners = w.listeners ∧
  LENGTH (upd_lchan c g w).chans = LENGTH w.chans
Proof
  simp[upd_lchan_def]
QED

Theorem EL_upd_lchan:
  c < LENGTH w.chans ⇒
  EL c' (upd_lchan c g w).chans = if c' = c then g (EL c w.chans) else EL c' w.chans
Proof
  rw[upd_lchan_def, EL_LUPDATE]
QED

Theorem upd_lchan_fields[simp]:
  (upd_lchan c g w).open_fds = w.open_fds ∧ (upd_lchan c g w).reserved = w.reserved ∧
  (upd_lchan c g w).fd_limit = w.fd_limit
Proof
  simp[upd_lchan_def]
QED

Theorem pinv_upd:
  pinv evs w cs ∧ c < LENGTH w.chans ∧
  (g (EL c w.chans)).sent = (EL c w.chans).sent ∧
  (∀r. in_ok r (EL c w.chans) ⇒ in_ok r (g (EL c w.chans))) ⇒
  pinv evs (upd_lchan c g w) cs
Proof
  rw[pinv_def, upd_lchan_def, EL_LUPDATE, fds_lt_def, l0_used_def] >> rw[] >> gvs[] >>
  res_tac >> gvs[]
QED

(*---------------------------------------------------------------------------*)
(* Arrivals *)

Theorem MAP_FST_AFUPDKEY[simp]:
  ∀l. MAP FST (AFUPDKEY k f l) = MAP FST l
Proof
  Induct >> simp[AFUPDKEY_def] >> Cases >> rw[AFUPDKEY_def]
QED

(* The first entry for key k gets f applied; the others are unchanged *)
Theorem MEM_AFUPDKEY:
  ∀l. ALL_DISTINCT (MAP FST l) ⇒
      (MEM (a, b) (AFUPDKEY k f l) ⇔
       (a ≠ k ∧ MEM (a, b) l) ∨ (a = k ∧ ∃b0. MEM (k, b0) l ∧ b = f b0))
Proof
  Induct >> simp[AFUPDKEY_def] >> Cases >> rw[AFUPDKEY_def, MEM_MAP] >>
  gvs[FORALL_PROD] >> metis_tac[]
QED

Theorem MEM_AFUPDKEY_q:
  ∀L. MEM x (FLAT (MAP (SND o SND) (AFUPDKEY l (λ(p, q). (p, q ++ [c])) L))) ⇒
      x = c ∨ MEM x (FLAT (MAP (SND o SND) L))
Proof
  Induct >> simp[AFUPDKEY_def] >> PairCases >> rw[AFUPDKEY_def] >> gvs[] >>
  metis_tac[]
QED

Theorem ALL_DISTINCT_AFUPDKEY_q:
  ∀L. ALL_DISTINCT (FLAT (MAP (SND o SND) L)) ∧ ¬MEM c (FLAT (MAP (SND o SND) L)) ⇒
      ALL_DISTINCT (FLAT (MAP (SND o SND) (AFUPDKEY l (λ(p, q). (p, q ++ [c])) L)))
Proof
  Induct >> simp[AFUPDKEY_def] >> PairCases >> rw[AFUPDKEY_def, ALL_DISTINCT_APPEND] >>
  gvs[] >> metis_tac[MEM_AFUPDKEY_q]
QED

Theorem pinv_incoming:
  pinv evs w cs ⇒ pinv evs (l0_deliver w (LIncoming p)) cs
Proof
  rw[l0_deliver_def] >> every_case_tac >> simp[] >>
  rename1 ‘FILTER _ w.listeners = h :: _’ >> PairCases_on ‘h’ >> gvs[] >>
  ‘MEM (h0, h1, h2) w.listeners’
    by (qpat_x_assum ‘FILTER _ _ = _’ (mp_tac o Q.AP_TERM ‘MEM (h0, h1, h2)’) >>
        simp[MEM_FILTER]) >>
  gvs[pinv_def, fds_lt_listeners_chans] >>
  ‘∀L X f. l0_chan_of (w with <| listeners := L; chans := w.chans ++ X |>) f = l0_chan_of w f’
    by (rw[l0_chan_of_def] >> every_case_tac >> gvs[EVERY_MEM, FORALL_PROD] >>
        imp_res_tac ALOOKUP_MEM >> res_tac >> gvs[]) >>
  pop_assum (fn th => simp[th, EL_APPEND1]) >> rpt conj_tac
  >- (gvs[EVERY_MEM] >> rw[] >> res_tac >> simp[])
  >- (gvs[EVERY_MEM, FORALL_PROD] >> rw[] >> res_tac >> simp[])
  >- (rw[] >> ‘EL j cs < LENGTH w.chans’ by gvs[EVERY_EL] >> simp[EL_APPEND1])
  >- (irule ALL_DISTINCT_AFUPDKEY_q >> simp[MEM_FLAT, MEM_MAP, EXISTS_PROD] >>
      rw[] >> CCONTR_TAC >> gvs[] >> res_tac >> gvs[]) >>
  rpt gen_tac >> simp[MEM_AFUPDKEY, FORALL_PROD] >> strip_tac >> gvs[]
  >- (res_tac >> simp[] >> rw[] >> res_tac >> simp[EL_APPEND1]) >>
  rename1 ‘MEM (l, b0) _’ >> PairCases_on ‘b0’ >> gvs[] >>
  first_x_assum (drule_then strip_assume_tac) >> simp[] >> rpt gen_tac >>
  Cases_on ‘c = LENGTH w.chans’ >> simp[EL_APPEND1, EL_APPEND2]
  >- (simp[fresh_lchan_def, in_ok_def] >> rw[]
      >- (strip_tac >> gvs[EVERY_MEM] >> res_tac >> gvs[]) >>
      simp[l0_chan_of_def] >> CASE_TAC >> simp[]) >>
  strip_tac >> res_tac >> simp[EL_APPEND1]
QED

Theorem pinv_deliver:
  pinv evs w cs ⇒ pinv evs (l0_deliver w a) cs
Proof
  Cases_on ‘a’ >- simp[pinv_incoming] >>
  rw[l0_deliver_def] >>
  irule pinv_upd >> simp[] >> rw[in_ok_def, break_lchan_def] >>
  gvs[] >> qpat_x_assum ‘_ ++ _ = _’ (SUBST1_TAC o SYM) >> simp[IS_PREFIX_APPEND3]
QED

(*---------------------------------------------------------------------------*)
(* Calls that start no episode *)

(* An event that changes no projection *)
Theorem pinv_noop:
  ev_new ev = NONE ∧ ev_listen ev = NONE ∧ ev_sent ev = NONE ∧ ev_recvd ev = NONE ⇒
  (pinv (evs ++ [ev]) w cs ⇔ pinv evs w cs)
Proof
  rw[pinv_def, ep_fds_SNOC, ep_io_SNOC, FOLDL_APPEND, m_step_none, lsn_step_def]
QED

(* A successful send of bs' on fd f *)
Theorem pinv_sent:
  pinv evs w cs ∧ l0_chan_of w f = SOME c ∧
  ev_new ev = NONE ∧ ev_listen ev = NONE ∧ ev_recvd ev = NONE ∧ ev_sent ev = SOME (f, bs') ⇒
  pinv (evs ++ [ev])
       (upd_lchan c (λch. ch with <| sent := ch.sent ++ bs'; inflight := x ch |>) w) cs
Proof
  strip_tac >>
  ‘c < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >>
  ‘∀j. j < LENGTH cs ∧ EL j cs = c ⇒ EL j (ep_fds evs) = f’ by gvs[pinv_def] >>
  ‘∃j0. (f ≠ 0w ⇒ j0 < LENGTH cs ∧ EL j0 cs = c) ∧
        ∀j. ALOOKUP (FST (m_of evs)) f = SOME j ⇔ f ≠ 0w ∧ j = j0’
    by (Cases_on ‘f = 0w’
        >- (simp[] >> CCONTR_TAC >> gvs[] >> imp_res_tac m_of_lookup >> gvs[]) >>
        ‘∃j0. j0 < LENGTH cs ∧ EL j0 cs = c ∧ ALOOKUP (FST (m_of evs)) f = SOME j0’
          by (gvs[pinv_def] >> metis_tac[]) >>
        qexists_tac ‘j0’ >> rw[] >> eq_tac >> rw[] >> gvs[]) >>
  gvs[pinv_def, ep_fds_SNOC, ep_io_SNOC, FOLDL_APPEND, m_step_none, lsn_step_def,
      EL_upd_lchan] >>
  rpt strip_tac
  >- (qpat_x_assum ‘∀j. _ ⇒ ep_io ev_sent _ _ _ _ = _ ∧ _’ (qspec_then ‘j’ mp_tac) >>
      rw[] >> gvs[] >> ‘j = j0’ by metis_tac[ALL_DISTINCT_EL_IMP] >> gvs[])
  >- (qpat_x_assum ‘∀j. _ ⇒ ep_io ev_sent _ _ _ _ = _ ∧ _’ (qspec_then ‘j’ mp_tac) >>
      rw[] >> gvs[in_ok_def])
  >- metis_tac[]
  >- metis_tac[] >>
  rw[] >> metis_tac[]
QED

(* A successful recv of the first k bytes of the inbox, on fd f *)
Theorem pinv_recvd:
  pinv evs w cs ∧ l0_chan_of w f = SOME c ∧
  ev_new ev = NONE ∧ ev_listen ev = NONE ∧ ev_sent ev = NONE ∧
  ev_recvd ev = SOME (f, TAKE k (EL c w.chans).inbox) ⇒
  pinv (evs ++ [ev]) (upd_lchan c (λch. ch with inbox := DROP k ch.inbox) w) cs
Proof
  strip_tac >>
  ‘c < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >>
  ‘∀j. j < LENGTH cs ∧ EL j cs = c ⇒ EL j (ep_fds evs) = f’ by gvs[pinv_def] >>
  ‘∃j0. (f ≠ 0w ⇒ j0 < LENGTH cs ∧ EL j0 cs = c) ∧
        ∀j. ALOOKUP (FST (m_of evs)) f = SOME j ⇔ f ≠ 0w ∧ j = j0’
    by (Cases_on ‘f = 0w’
        >- (simp[] >> CCONTR_TAC >> gvs[] >> imp_res_tac m_of_lookup >> gvs[]) >>
        ‘∃j0. j0 < LENGTH cs ∧ EL j0 cs = c ∧ ALOOKUP (FST (m_of evs)) f = SOME j0’
          by (gvs[pinv_def] >> metis_tac[]) >>
        qexists_tac ‘j0’ >> rw[] >> eq_tac >> rw[] >> gvs[]) >>
  gvs[pinv_def, ep_fds_SNOC, ep_io_SNOC, FOLDL_APPEND, m_step_none, lsn_step_def,
      EL_upd_lchan] >>
  rpt strip_tac >>
  TRY (qpat_x_assum ‘∀j. _ ⇒ ep_io ev_sent _ _ _ _ = _ ∧ _’ (qspec_then ‘j’ mp_tac) >>
       rw[] >> gvs[in_ok_def] >> REWRITE_TAC[GSYM APPEND_ASSOC, TAKE_DROP] >> gvs[] >>
       TRY (qspecl_then [‘cs’, ‘j’, ‘j0’] mp_tac ALL_DISTINCT_EL_IMP >> gvs[] >>
            rpt strip_tac >> gvs[]) >>
       res_tac >> gvs[] >> NO_TAC) >>
  rw[] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Closing *)

Theorem l0_chan_of_ADELKEY:
  l0_chan_of (w with open_fds := ADELKEY f w.open_fds) g =
  if g = f then NONE else l0_chan_of w g
Proof
  rw[l0_chan_of_def, ALOOKUP_ADELKEY]
QED

Theorem pinv_drop_fd:
  pinv evs w cs ⇒ pinv evs (w with open_fds := ADELKEY f w.open_fds) cs
Proof
  rw[pinv_def, l0_chan_of_ADELKEY] >> gvs[] >>
  TRY (fs[fds_lt_def, l0_used_def, MEM_MAP, ADELKEY_def, MEM_FILTER] >> rw[] >>
       first_x_assum irule >> metis_tac[] >> NO_TAC) >>
  TRY (gvs[EVERY_MEM, ADELKEY_def, MEM_FILTER] >> NO_TAC) >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  metis_tac[]
QED

Theorem ALL_DISTINCT_MAP_FILTER:
  ∀l. ALL_DISTINCT (MAP f l) ⇒ ALL_DISTINCT (MAP f (FILTER P l))
Proof
  Induct >> rw[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem ALL_DISTINCT_FLAT_FILTER:
  ∀l. ALL_DISTINCT (FLAT (MAP g l)) ⇒ ALL_DISTINCT (FLAT (MAP g (FILTER P l)))
Proof
  Induct >> rw[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem pinv_drop_listener:
  pinv evs w cs ⇒ pinv evs (w with listeners := FILTER P w.listeners) cs
Proof
  strip_tac >>
  ‘∀f. l0_chan_of (w with listeners := FILTER P w.listeners) f = l0_chan_of w f’
    by simp[l0_chan_of_def] >>
  ‘fds_lt (w with listeners := FILTER P w.listeners)’
    by (gvs[pinv_def, fds_lt_def, l0_used_def] >> rw[] >> first_x_assum irule >>
        gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  fs[pinv_def] >> rw[] >> gvs[MEM_FILTER] >>
  TRY (simp[ALL_DISTINCT_MAP_FILTER, ALL_DISTINCT_FLAT_FILTER] >> NO_TAC) >>
  res_tac >> gvs[]
QED

Theorem LUPDATE_out_of_range:
  LENGTH l ≤ n ⇒ LUPDATE x n l = l
Proof
  rw[LIST_EQ_REWRITE, EL_LUPDATE]
QED

Theorem pinv_break:
  pinv evs w cs ⇒ pinv evs (upd_lchan c (break_lchan e k) w) cs
Proof
  Cases_on ‘c < LENGTH w.chans’
  >- (strip_tac >> irule pinv_upd >> rw[break_lchan_def, in_ok_def] >>
      metis_tac[IS_PREFIX_APPEND1]) >>
  simp[upd_lchan_def, LUPDATE_out_of_range] >>
  ‘w with chans := w.chans = w’ by simp[l0world_component_equality] >> simp[]
QED

Theorem pinv_breaks:
  ∀q w. pinv evs w cs ⇒
        pinv evs (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w q) cs
Proof
  Induct >> rw[] >> first_x_assum irule >> simp[pinv_break]
QED

Theorem pinv_drop_reserved:
  pinv evs w cs ⇒ pinv evs (w with reserved := FILTER P w.reserved) cs
Proof
  rw[pinv_def, l0_chan_of_def] >>
  gvs[fds_lt_def, l0_used_def, MEM_FILTER] >> metis_tac[]
QED

Theorem pinv_close_fd:
  pinv evs w cs ⇒ pinv evs (close_fd f w) cs
Proof
  rw[close_fd_def] >> every_case_tac >> gvs[] >>
  TRY (irule pinv_drop_reserved >> simp[] >> NO_TAC) >>
  TRY (irule pinv_breaks >> irule pinv_drop_listener >> simp[] >> NO_TAC) >>
  rename1 ‘l0_chan_of w f = SOME j’ >>
  ‘j < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >>
  irule pinv_upd >> simp[pinv_drop_fd, in_ok_def]
QED

Theorem pinv_close_all:
  pinv evs w cs ⇒ pinv evs (close_all w) cs
Proof
  simp[close_all_def] >>
  qspec_tac (‘MAP FST w.open_fds ++ MAP FST w.listeners’, ‘fs’) >>
  qid_spec_tac ‘w’ >> Induct_on ‘fs’ >> rw[] >>
  first_x_assum irule >> simp[pinv_close_fd]
QED

(*---------------------------------------------------------------------------*)
(* Calls that get a new fd *)

(* With the fds below the limit, the lowest free fd is free *)
Theorem l0_alloc_fresh:
  fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ∧ l0_alloc w = SOME f ⇒
  ¬MEM f (l0_used w) ∧ w2n f < w.fd_limit
Proof
  strip_tac >> gvs[l0_alloc_def, AllCaseEqs()] >>
  ‘∃n. ¬MEM (n2w n : word64) (l0_used w)’
    by (qexists_tac ‘w.fd_limit’ >> strip_tac >> gvs[fds_lt_def] >> res_tac >>
        ‘w2n (n2w w.fd_limit : word64) = w.fd_limit’
          by (simp[w2n_n2w] >> irule LESS_MOD >> simp[]) >> gvs[]) >>
  simp[lowest_fd_def] >> numLib.LEAST_ELIM_TAC >> simp[] >> metis_tac[]
QED

Theorem pinv_listen:
  pinv evs w cs ∧ ¬MEM f (l0_used w) ∧ w2n f < w.fd_limit ∧
  ev_new ev = NONE ∧ ev_listen ev = SOME (f, p) ∧ ev_sent ev = NONE ∧ ev_recvd ev = NONE ⇒
  pinv (evs ++ [ev]) (w with listeners := w.listeners ++ [(f, p, [])]) cs
Proof
  strip_tac >>
  ‘∀g. l0_chan_of (w with listeners := w.listeners ++ [(f, p, [])]) g = l0_chan_of w g’
    by simp[l0_chan_of_def] >>
  ‘∀p q. ¬MEM (f, p, q) w.listeners’
    by (gvs[l0_used_def, MEM_MAP, FORALL_PROD] >> metis_tac[]) >>
  ‘¬MEM f (MAP FST w.listeners)’ by gvs[l0_used_def] >>
  fs[pinv_def, ep_fds_SNOC, ep_io_SNOC, FOLDL_APPEND, m_step_none, lsn_step_def] >>
  rw[] >> gvs[] >> TRY (res_tac >> gvs[] >> NO_TAC) >>
  gvs[fds_lt_def, l0_used_def, ALL_DISTINCT_APPEND] >> rw[] >> res_tac >> gvs[]
QED

Theorem pinv_new_chan:
  pinv evs w cs ⇒ pinv evs (w with chans := w.chans ++ [c0]) cs
Proof
  strip_tac >>
  ‘∀g. l0_chan_of (w with chans := w.chans ++ [c0]) g = l0_chan_of w g’
    by (fs[pinv_def] >> rw[l0_chan_of_def] >> every_case_tac >>
        gvs[EVERY_MEM, FORALL_PROD] >> imp_res_tac ALOOKUP_MEM >> res_tac >> gvs[]) >>
  ‘∀c. c < LENGTH w.chans ⇒ EL c (w.chans ++ [c0]) = EL c w.chans’ by simp[EL_APPEND1] >>
  fs[pinv_def] >> rw[] >> gvs[] >>
  TRY (gvs[fds_lt_def, l0_used_def] >> NO_TAC) >>
  TRY (gvs[EVERY_MEM, FORALL_PROD] >> rw[] >> res_tac >> simp[] >> NO_TAC) >>
  TRY (‘EL j cs < LENGTH w.chans’ by gvs[EVERY_EL] >> res_tac >> gvs[] >> NO_TAC) >>
  res_tac >> gvs[]
QED

(* fd f is opened on channel j, which no fd, episode or queue has: a new
   episode *)
Theorem pinv_open:
  pinv evs w cs ∧ j < LENGTH w.chans ∧ ¬MEM j cs ∧ (∀g. l0_chan_of w g ≠ SOME j) ∧
  (EL j w.chans).sent = [] ∧ in_ok [] (EL j w.chans) ∧
  (∀l p q. MEM (l, p, q) w.listeners ⇒ ¬MEM j q) ∧
  ¬MEM f (l0_used w) ∧ w2n f < w.fd_limit ∧
  ev_new ev = SOME (f, h) ∧ ev_listen ev = NONE ∧ ev_sent ev = NONE ∧ ev_recvd ev = NONE ⇒
  pinv (evs ++ [ev]) (w with open_fds := (f, j) :: w.open_fds) (cs ++ [j])
Proof
  strip_tac >>
  qabbrev_tac ‘n = LENGTH cs’ >>
  ‘LENGTH (ep_fds evs) = n ∧ SND (m_of evs) = n’ by gvs[pinv_def, m_of_count] >>
  ‘m_of (evs ++ [ev]) = ((if f = 0w then FST (m_of evs) else (f, n) :: FST (m_of evs)), n + 1)’
    by (simp[FOLDL_APPEND] >> Cases_on ‘m_of evs’ >> gvs[m_step_def]) >>
  ‘∀g. l0_chan_of (w with open_fds := (f, j) :: w.open_fds) g =
       if g = f then SOME j else l0_chan_of w g’
    by rw[l0_chan_of_def] >>
  ‘¬MEM f (MAP FST w.open_fds)’ by gvs[l0_used_def] >>
  ‘∀sel j'. j' < n ⇒ ep_io sel j' [] 0 (evs ++ [ev]) =
                     ep_io sel j' [] 0 evs ++
                     case sel ev of SOME (g, bs) =>
                       if ALOOKUP (FST (m_of evs)) g = SOME j' then bs else [] | NONE => []’
    by simp[ep_io_SNOC] >>
  ‘∀c. MEM c cs ⇒ c ≠ j’ by metis_tac[] >>
  fs[pinv_def, ep_fds_SNOC, lsn_step_def, FOLDL_APPEND] >>
  simp[ep_io_SNOC] >> rpt conj_tac
  >- (gvs[fds_lt_def, l0_used_def] >> rw[] >> res_tac >> simp[])
  >- simp[ALL_DISTINCT_APPEND]
  >- (rpt gen_tac >> Cases_on ‘f' = f’ >> simp[] >> strip_tac >> gvs[]
      >- (rw[] >> Cases_on ‘j' < LENGTH cs’ >> gvs[EL_APPEND1, EL_APPEND2]
          >- (‘MEM (EL j' cs) cs’ by (irule EL_MEM >> gvs[]) >> gvs[]) >>
          ‘j' = LENGTH cs’ by simp[] >> gvs[EL_APPEND2] >>
          TRY (‘LENGTH cs = LENGTH (ep_fds evs)’ by simp[] >> gvs[])) >>
      ‘c ≠ j’ by (strip_tac >> gvs[]) >>
      first_x_assum drule >> strip_tac >> conj_tac
      >- (rw[] >> Cases_on ‘j' < LENGTH cs’ >> gvs[EL_APPEND1, EL_APPEND2] >>
          ‘j' = LENGTH cs’ by simp[] >> gvs[EL_APPEND2] >>
          TRY (‘LENGTH cs = LENGTH (ep_fds evs)’ by simp[] >> gvs[])) >>
      strip_tac >> gvs[] >> qexists_tac ‘j'’ >> rw[EL_APPEND1])
  >- (rpt gen_tac >> strip_tac >> Cases_on ‘j' < LENGTH cs’ >> gvs[EL_APPEND1, EL_APPEND2] >>
      ‘j' = LENGTH cs’ by simp[] >> gvs[EL_APPEND2] >>
          TRY (‘LENGTH cs = LENGTH (ep_fds evs)’ by simp[] >> gvs[]) >> simp[ep_io_unborn]) >>
  rpt gen_tac >> strip_tac >> res_tac >> simp[] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >> gvs[] >> res_tac >>
  strip_tac >> gvs[]
QED

(* Popping channel x off listener l's queue *)
Theorem FLAT_AFUPDKEY_K:
  ∀L. ALL_DISTINCT (MAP FST L) ∧ MEM (l, p0, x :: q') L ⇒
      ∃A B. FLAT (MAP (SND o SND) L) = A ++ x :: q' ++ B ∧
            FLAT (MAP (SND o SND) (AFUPDKEY l (K (p, q')) L)) = A ++ q' ++ B
Proof
  Induct >> simp[] >> PairCases >> rw[AFUPDKEY_def] >> gvs[MEM_MAP, FORALL_PROD] >>
  TRY (qexists_tac ‘[]’ >> simp[] >> NO_TAC) >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  TRY (first_x_assum drule >> strip_tac) >> qexists_tac ‘h2 ++ A’ >> qexists_tac ‘B’ >> simp[]
QED

Theorem MEM_FST_unique:
  ALL_DISTINCT (MAP FST L) ∧ MEM (k, a) L ∧ MEM (k, b) L ⇒ a = b
Proof
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM, SOME_11]
QED

Theorem pinv_pop:
  pinv evs w cs ∧ FILTER (λ(l', p, q). l' = l) w.listeners = (l1, p, j :: q') :: t ⇒
  pinv evs (w with listeners := AFUPDKEY l (K (p, q')) w.listeners) cs ∧
  (∀l' p' q''. MEM (l', p', q'') (AFUPDKEY l (K (p, q')) w.listeners) ⇒ ¬MEM j q'')
Proof
  strip_tac >>
  ‘MEM (l1, p, j :: q') (FILTER (λ(l', p, q). l' = l) w.listeners)’ by simp[] >>
  ‘MEM (l, p, j :: q') w.listeners’ by gvs[MEM_FILTER] >>
  ‘ALL_DISTINCT (MAP FST w.listeners) ∧ ALL_DISTINCT (FLAT (MAP (SND o SND) w.listeners))’
    by gvs[pinv_def] >>
  drule_all FLAT_AFUPDKEY_K >> disch_then (qspec_then ‘p’ strip_assume_tac) >>
  ‘∀a b. MEM (a, b) (AFUPDKEY l (K (p, q')) w.listeners) ⇔
         (a ≠ l ∧ MEM (a, b) w.listeners) ∨ (a = l ∧ b = (p, q'))’
    by (rw[MEM_AFUPDKEY] >> eq_tac >> rw[] >> gvs[] >>
        qexists_tac ‘(p, j :: q')’ >> simp[]) >>
  ‘ALL_DISTINCT (A ++ q' ++ B) ∧ ¬MEM j (A ++ q' ++ B)’
    by (qpat_x_assum ‘FLAT _ = A ++ j :: q' ++ B’ (fn th => gvs[th]) >>
        gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘∀g. l0_chan_of (w with listeners := AFUPDKEY l (K (p, q')) w.listeners) g =
       l0_chan_of w g’ by simp[l0_chan_of_def] >>
  conj_tac
  >- (fs[pinv_def] >> rpt conj_tac >>
      TRY (qpat_x_assum ‘fds_lt w’ mp_tac >> simp[fds_lt_def, l0_used_def] >> NO_TAC) >>
      TRY (simp[] >> NO_TAC) >>
      rpt gen_tac >> strip_tac >> gvs[]
      >- (res_tac >> simp[]) >>
      first_x_assum drule >> rw[] >> gvs[]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  ‘MEM j (FLAT (MAP (SND o SND) (AFUPDKEY l (K (p, q')) w.listeners)))’
    by (simp[MEM_FLAT, MEM_MAP] >> qexists_tac ‘q''’ >> simp[] >>
        qexists_tac ‘(l', p', q'')’ >> simp[]) >>
  gvs[]
QED

(* A failed connect whose value is 0 (no socket, or a socket on fd 0 that
   the trace cannot tell from none): channel j gets fd 0, no episode *)
Theorem pinv_hidden:
  pinv evs w cs ∧ j < LENGTH w.chans ∧ ¬MEM j cs ∧ (∀g. l0_chan_of w g ≠ SOME j) ∧
  (∀l p q. MEM (l, p, q) w.listeners ⇒ ¬MEM j q) ∧
  ¬MEM 0w (l0_used w) ∧ 0 < w.fd_limit ∧
  ev_new ev = NONE ∧ ev_listen ev = NONE ∧ ev_sent ev = NONE ∧ ev_recvd ev = NONE ⇒
  pinv (evs ++ [ev]) (w with open_fds := (0w, j) :: w.open_fds) cs
Proof
  strip_tac >> drule_all (iffRL pinv_noop) >> strip_tac >>
  ‘∀g. l0_chan_of (w with open_fds := (0w, j) :: w.open_fds) g =
       if g = 0w then SOME j else l0_chan_of w g’
    by rw[l0_chan_of_def] >>
  qpat_x_assum ‘pinv (_ ++ _) _ _’ mp_tac >> simp[pinv_def] >> strip_tac >> rpt conj_tac >>
  FIRST [
    qpat_x_assum ‘fds_lt w’ mp_tac >> simp[fds_lt_def, l0_used_def] >> rw[] >> simp[] >> NO_TAC,
    gvs[EVERY_MEM, FORALL_PROD] >> rw[] >> gvs[] >> res_tac >> simp[] >> NO_TAC,
    rpt gen_tac >> Cases_on ‘f = 0w’ >> simp[] >> strip_tac >> gvs[]
    >- (rw[] >> ‘j' < LENGTH cs’ by gvs[] >>
        ‘MEM (EL j' cs) cs’ by (irule EL_MEM >> simp[]) >> gvs[]) >>
    res_tac >> simp[] >> NO_TAC,
    rpt gen_tac >> strip_tac >> res_tac >> simp[] >> rpt strip_tac >>
    qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >> res_tac >> gvs[] >>
    strip_tac >> gvs[]]
QED
