(*
  The simulation, for I/O events: what the handle layer's events (on fds,
  with closes) say about each episode is what the version-1 events (on
  handles) say about each handle.  Renamed by rn_evs (asyncHLEpisodes),
  the events of one action carry the same bytes, per handle, as the
  version-1 event of that action (hdo_events), and EchoSpec2's
  bookkeeping of open episodes is the handle layer's open fds.
*)
Theory asyncHLSimEvents
Ancestors
  alist words ffi ffiSpikeSocketFFI asyncM3World EchoSpec EchoSpec2
  socketV2FFI socketV2Fair socketV2Proof asyncHLFair asyncHLModel
  asyncHLSimWorld asyncHLSimOps asyncHLEpisodes asyncM4SockInv asyncHLEof socketV2Events
Libs
  preamble

(* ------------------------------------------------------------------------
   The events of the actions
   ------------------------------------------------------------------------ *)

Theorem MAP_SND_ZIP_REPLICATE[local]:
  LENGTH l = n ⇒ MAP SND (ZIP (REPLICATE n x, l)) = l
Proof
  rw[] >> simp[MAP_ZIP]
QED

Theorem act_event_kinds[simp]:
  event_accepted (act_event (Accept l) (Accepted r)) = r ∧
  event_closed (act_event a r') = NONE ∧
  event_accepted (act_event (Read c n) r') = NONE ∧
  event_accepted (act_event (Write c bs) r') = NONE ∧
  ev_fd (act_event (Accept l) r') = NONE ∧
  ev_fd (act_event (Read c n) (Got ro)) = SOME c ∧
  ev_fd (act_event (Write c bs) Wrote) = SOME c
Proof
  rpt conj_tac
  >- (Cases_on ‘r’ >>
      simp[act_event_def, event_accepted_def, MAP_SND_ZIP_REPLICATE] >>
      simp[TAKE_LENGTH_TOO_LONG])
  >- (Cases_on ‘a’ >> Cases_on ‘r'’ >> simp[act_event_def, event_closed_def])
  >- (Cases_on ‘r'’ >> simp[act_event_def, event_accepted_def])
  >- (Cases_on ‘r'’ >> simp[act_event_def, event_accepted_def])
  >- (Cases_on ‘r'’ >> simp[act_event_def, ev_fd_def])
  >- simp[act_event_def, ev_fd_def]
  >> simp[act_event_def, ev_fd_def, TAKE_APPEND1, TAKE_LENGTH_TOO_LONG]
QED

Theorem close_event_kinds[simp]:
  event_closed (close_event f) = SOME f ∧
  event_accepted (close_event f) = NONE ∧
  ev_fd (close_event f) = NONE
Proof
  simp[close_event_def, event_closed_def, event_accepted_def, ev_fd_def]
QED

Theorem ev_ren_act[simp]:
  ev_ren c' (act_event (Read c n) (Got ro)) = act_event (Read c' n) (Got ro) ∧
  ev_ren c' (act_event (Write c bs) Wrote) = act_event (Write c' bs) Wrote
Proof
  simp[act_event_def, ev_ren_def, DROP_APPEND1, DROP_LENGTH_TOO_LONG]
QED

(* Events without bytes *)
Theorem act_event_no_bytes[simp]:
  event_read c (act_event (Accept l) r) = [] ∧
  event_written c (act_event (Accept l) r) = [] ∧
  event_read c (act_event (Read c' n) (Got (SOME []))) = [] ∧
  event_written c (act_event (Read c' n) (Got ro)) = []
Proof
  rpt conj_tac >>
  TRY (Cases_on ‘r’) >>
  simp[act_event_def, event_read_def, event_written_def, sread_out_def,
       MAP_SND_ZIP_REPLICATE] >>
  TRY (Cases_on ‘o'’) >> simp[]
QED

(* ------------------------------------------------------------------------
   One action
   ------------------------------------------------------------------------ *)

(* MAIN: an action of the handle layer, renamed, carries the bytes of the
   version-1 event of the action, and the open fds are EchoSpec2's
   bookkeeping; except that a write on a closed handle would be lost *)
Theorem hdo_events:
  hsim0 lfd s1 (s2, hs) ∧ hdo lfd (s2, hs) a = SOME (r, (s2', hs'), evs) ∧
  act_ok lfd hs.nxt a ∧
  (∀c bs. a = Write c bs ⇒ ALOOKUP hs.tbl c ≠ NONE) ⇒
  ep_st hs.nxt s2.open_fds evs = (hs'.nxt, s2'.open_fds) ∧
  (∀c. bytes_read_from c (rn_evs lfd hs.nxt s2.open_fds evs) =
       bytes_read_from c [act_event a r]) ∧
  (∀c. bytes_written_to c (rn_evs lfd hs.nxt s2.open_fds evs) =
       bytes_written_to c [act_event a r])
Proof
  strip_tac >> Cases_on ‘a’ >> fs[act_ok_def] >> rveq
  (* accept *)
  >- (qpat_x_assum ‘hdo _ _ _ = _’ mp_tac >>
      simp[hdo_def, sock_accept2_def, AllCaseEqs()] >> strip_tac >>
      gvs[rn_evs_def, ep_st_def, bytes_read_from_def, bytes_written_to_def] >>
      (* the accepted client is the oldest pending one, hs.nxt, on a free fd *)
      qpat_assum ‘hsim0 _ _ _’
        (assume_tac o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[hsim0_def]) >>
      gvs[] >> Cases_on ‘LENGTH s2.clients − hs.nxt’ >> gvs[GENLIST_CONS] >>
      ‘alloc_ok s2.alloc’ by fs[hsim0_def] >>
      qmatch_goalsub_abbrev_tac ‘ADELKEY f _’ >>
      ‘¬MEM f (MAP FST s2.open_fds)’
        by (‘¬MEM f (used_fds s2)’ by fs[alloc_ok_def, Abbr ‘f’] >>
            fs[used_fds_def]) >>
      simp[ADELKEY_def, FILTER_EQ_ID, EVERY_MEM] >> Cases >> rpt strip_tac >>
      gvs[MEM_MAP] >> metis_tac[FST])
  (* read *)
  >- (rename1 ‘Read (hdl lfd j) n’ >>
      qpat_x_assum ‘hdo _ _ _ = _’ mp_tac >> simp[hdo_def] >>
      Cases_on ‘ALOOKUP hs.tbl (hdl lfd j)’ >> simp[]
      (* a closed handle: no event; the version-1 read returns EOF *)
      >- (strip_tac >> gvs[rn_evs_def, ep_st_def, bytes_read_from_def, bytes_written_to_def])
      >> rename1 ‘ALOOKUP hs.tbl (hdl lfd j) = SOME f’ >>
      ‘ALOOKUP s2.open_fds f = SOME j’
        by (‘hs.nxt ≤ LENGTH s2.clients’ by fs[hsim0_def] >>
            ‘j < LENGTH s2.clients’ by fs[] >> drule_all hsim0_tbl_open >> simp[]) >>
      simp[AllCaseEqs()] >> strip_tac >>
      gvs[sock_read2_def, sock_close2_def, AllCaseEqs(), update_client_def,
          rn_evs_def, ep_st_def, bytes_read_from_def, bytes_written_to_def])
  (* write *)
  >> rename1 ‘Write (hdl lfd j) bs’ >>
  qpat_x_assum ‘hdo _ _ _ = _’ mp_tac >> simp[hdo_def] >>
  Cases_on ‘ALOOKUP hs.tbl (hdl lfd j)’ >> gvs[] >>
  rename1 ‘ALOOKUP hs.tbl (hdl lfd j) = SOME f’ >>
  ‘ALOOKUP s2.open_fds f = SOME j’
    by (‘hs.nxt ≤ LENGTH s2.clients’ by fs[hsim0_def] >>
        ‘j < LENGTH s2.clients’ by fs[] >> drule_all hsim0_tbl_open >> simp[]) >>
  strip_tac >>
  gvs[sock_write2_def, AllCaseEqs(), update_client_def,
      rn_evs_def, ep_st_def, bytes_read_from_def, bytes_written_to_def]
QED

(* ------------------------------------------------------------------------
   A round's actions
   ------------------------------------------------------------------------ *)

(* Every closed handle had its EOF read, among the performed pairs P *)
Definition closed_eof_def:
  closed_eof lfd P hs ⇔
    ∀j. j < hs.nxt ∧ ALOOKUP hs.tbl (hdl lfd j) = NONE ⇒
        ∃k. MEM (Read (hdl lfd j) k, Got (SOME [])) P
End

(* After P, no pair of ps acts on a connection whose EOF was read before *)
Definition no_after_eof_def:
  no_after_eof P ps ⇔
    ∀p1 a r p2 c k. ps = p1 ++ (a, r) :: p2 ∧
                    MEM (Read c k, Got (SOME [])) (P ++ p1) ⇒ ¬sock_on c a
End

Theorem no_after_eof_CONS:
  no_after_eof P ((a, r) :: ps) ⇒
  (∀c k. MEM (Read c k, Got (SOME [])) P ⇒ ¬sock_on c a) ∧
  no_after_eof (P ++ [(a, r)]) ps
Proof
  simp[no_after_eof_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [‘[]’, ‘a’, ‘r’, ‘ps’, ‘c’, ‘k’] mp_tac) >> simp[])
  >> rpt strip_tac >>
  first_x_assum (qspecl_then [‘(a, r) :: p1’, ‘a'’, ‘r'’, ‘p2’, ‘c’, ‘k’] mp_tac) >>
  impl_tac >- fs[] >> simp[]
QED

(* A handle closed after an action was closed before, or the action read
   its EOF *)
Theorem hdo_closed:
  hdo lfd (s2, hs) a = SOME (r, (s2', hs'), evs) ∧
  j < hs'.nxt ∧ ALOOKUP hs'.tbl (hdl lfd j) = NONE ⇒
  (j < hs.nxt ∧ ALOOKUP hs.tbl (hdl lfd j) = NONE) ∨
  ∃k. a = Read (hdl lfd j) k ∧ r = Got (SOME [])
Proof
  Cases_on ‘a’ >> simp[hdo_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- (Cases_on ‘j = hs.nxt’ >> gvs[] >>
      qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >> gvs[])
  >> gvs[ALOOKUP_ADELKEY] >> pop_assum mp_tac >> rw[] >> gvs[]
QED

(* MAIN: a round's actions, performed by the handle layer and renamed,
   carry the bytes of the version-1 events, per handle *)
Theorem hacts_events:
  ∀acts s1 s2 hs rs evs1 s1' P.
    hsim lfd s1 (s2, hs) ∧ sched_wf2 s2 ∧ EVERY (action_ok lfd acc) acts ∧
    set acc ⊆ set (GENLIST (hdl lfd) hs.nxt) ∧
    sock_acts s1 acts = SOME (rs, evs1, s1') ∧
    closed_eof lfd P hs ∧ no_after_eof P (ZIP (acts, rs)) ⇒
    ∃evs2 s2' hs'.
      hacts lfd (s2, hs) acts = SOME (rs, evs2, (s2', hs')) ∧
      hsim lfd s1' (s2', hs') ∧ sched_wf2 s2' ∧
      closed_eof lfd (P ++ ZIP (acts, rs)) hs' ∧
      ep_st hs.nxt s2.open_fds evs2 = (hs'.nxt, s2'.open_fds) ∧
      (∀c. bytes_read_from c (rn_evs lfd hs.nxt s2.open_fds evs2) = bytes_read_from c evs1) ∧
      (∀c. bytes_written_to c (rn_evs lfd hs.nxt s2.open_fds evs2) =
           bytes_written_to c evs1)
Proof
  Induct
  >- simp[sock_acts_def, hacts_def, ep_st_def, rn_evs_def]
  >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘sock_acts _ _ = _’ mp_tac >> simp[sock_acts_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename1 ‘sock_do s1 a = SOME (r, s1a)’ >>
  ‘act_ok lfd hs.nxt a’
    by (Cases_on ‘a’ >> fs[action_ok_def, act_ok_def, SUBSET_DEF] >>
        res_tac >> fs[MEM_GENLIST] >> metis_tac[]) >>
  ‘∃s2a hsa evsa. hdo lfd (s2, hs) a = SOME (r, (s2a, hsa), evsa) ∧
                  hsim lfd s1a (s2a, hsa) ∧ LENGTH s2a.clients = LENGTH s2.clients ∧
                  s2a.future = s2.future’
    by (Cases_on ‘a’ >> fs[act_ok_def]
        >- (rveq >> drule_all hdo_sim_accept >> simp[])
        >- (rveq >> drule_all hdo_sim_read >> simp[])
        >> rveq >> drule_all hdo_sim_write >> simp[]) >>
  ‘sched_wf2 s2a’ by metis_tac[hdo_sched_wf2] >>
  drule hdo_nxt >> strip_tac >>
  qpat_x_assum ‘no_after_eof _ _’ (strip_assume_tac o MATCH_MP no_after_eof_CONS) >>
  (* no write on a closed handle *)
  ‘∀c bs. a = Write c bs ⇒ ALOOKUP hs.tbl c ≠ NONE’
    by (rpt strip_tac >> gvs[act_ok_def] >>
        gvs[closed_eof_def] >> first_x_assum drule_all >> strip_tac >>
        first_x_assum drule >> simp[sock_on_def]) >>
  ‘hsim0 lfd s1 (s2, hs)’ by fs[hsim_def] >>
  drule_all hdo_events >> strip_tac >>
  first_x_assum (qspecl_then [‘s1a’, ‘s2a’, ‘hsa’, ‘rs'’, ‘evs’, ‘s1'’,
                              ‘P ++ [(a, r)]’] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- (fs[SUBSET_DEF] >> rw[] >> res_tac >> fs[])
      >> rw[closed_eof_def] >> drule_all hdo_closed >> strip_tac
      >- (fs[closed_eof_def] >> metis_tac[])
      >> gvs[] >> metis_tac[]) >>
  strip_tac >>
  qpat_x_assum ‘closed_eof _ _ hs'’ (assume_tac o REWRITE_RULE[GSYM APPEND_ASSOC, APPEND]) >>
  fs[hacts_def, ep_st_APPEND, rn_evs_APPEND, bytes_read_from_def, bytes_written_to_def]
QED

(* ------------------------------------------------------------------------
   Every EOF read is followed by its close
   ------------------------------------------------------------------------ *)

Theorem REPLICATE_9[local]:
  REPLICATE (n + 9) x = x :: REPLICATE (n + 8) x
Proof
  ‘n + 9 = SUC (n + 8)’ by simp[] >> pop_assum SUBST1_TAC >> simp[REPLICATE]
QED

Theorem act_event_eof[simp]:
  event_eof (act_event (Read c n) (Got ro)) = (if ro = SOME [] then SOME c else NONE) ∧
  event_eof (act_event (Accept l) r) = NONE ∧
  event_eof (act_event (Write c bs) r) = NONE ∧
  event_eof (close_event f) = NONE
Proof
  rpt conj_tac >> TRY (Cases_on ‘r’) >> TRY (Cases_on ‘ro’) >>
  simp[act_event_def, event_eof_def, close_event_def, sread_out_def, REPLICATE_9] >>
  TRY (rename1 ‘Accepted oc’ >> Cases_on ‘oc’) >> rw[REPLICATE_9] >> gvs[]
QED

Theorem eof_then_close_NIL[simp]:
  eof_then_close []
Proof
  simp[eof_then_close_def]
QED

Theorem eof_then_close_CONS_iff:
  eof_then_close (e :: evs) ⇔
    (∀f. event_eof e = SOME f ⇒ ∃e' p3. evs = e' :: p3 ∧ event_closed e' = SOME f) ∧
    eof_then_close evs
Proof
  rw[eof_then_close_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspecl_then [‘[]’, ‘e’, ‘evs’, ‘f’] mp_tac) >> simp[])
  >- (first_x_assum (qspecl_then [‘e :: p1’, ‘e'’, ‘p2’, ‘f’] mp_tac) >> simp[])
  >> Cases_on ‘p1’ >> gvs[] >> metis_tac[]
QED

Theorem eof_then_close_APPEND:
  ∀A. eof_then_close A ∧ eof_then_close B ⇒ eof_then_close (A ++ B)
Proof
  Induct >> simp[eof_then_close_CONS_iff] >> rpt strip_tac >> res_tac >>
  Cases_on ‘A’ >> gvs[]
QED

Theorem hdo_eof_then_close:
  hdo lfd (s, hs) a = SOME (r, st', evs) ⇒ eof_then_close evs
Proof
  Cases_on ‘a’ >> simp[hdo_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[eof_then_close_CONS_iff] >> rw[] >> gvs[]
QED

Theorem hacts_eof_then_close:
  ∀acts st rs evs st'.
    hacts lfd st acts = SOME (rs, evs, st') ⇒ eof_then_close evs
Proof
  Induct >> simp[hacts_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> PairCases_on ‘st’ >>
  irule eof_then_close_APPEND >> conj_tac
  >- (drule hdo_eof_then_close >> simp[])
  >> first_x_assum drule >> simp[]
QED
