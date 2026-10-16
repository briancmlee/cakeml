(*
  Per-fd projections of a version-1 trace (toward the disciplined
  sym_equiv claims).  In a trace of version 1's calls (no close, no
  connect) whose opened fds are distinct and whose reads and writes are on
  fds opened before them, connection c = the j-th opened fd is episode j:
   - proj_ch_events: c's bytes in episode j's events are c's bytes;
   - proj_ren_evs: in the renamed trace (endpointServers' ren_evs), fd
     n2w j's bytes are c's bytes;
  for the read and written bytes (proj_ok event_read, proj_ok event_written).
*)
Theory endpointV1Proj
Ancestors
  llist alist ffi ffiSpikeSocketFFI EchoSpec EchoSpec2 endpointSpecForms
  endpointServers ffiSpikeSocketFair socketV2FFI endpointV1Sim endpointV1Run
Libs
  preamble

(* ------------------------------------------------------------------------
   The projections
   ------------------------------------------------------------------------ *)

(* A per-fd projection: only reads and writes on the fd count, and renaming
   an event's fd renames its projection *)
Definition proj_ok_def:
  proj_ok (pr : word64 -> io_event -> word8 list) ⇔
    (∀c ev. pr c ev ≠ [] ⇒ rw_fd ev = SOME c) ∧
    (∀d d' f ev. rw_fd ev = SOME f ∧ v1_event ev ⇒
                 pr d (ren_ev d' ev) = if d = d' then pr f ev else [])
End

Theorem TAKE_fd_bytes[local,simp]:
  TAKE 8 (fd_bytes d) = fd_bytes d
Proof
  metis_tac[LENGTH_fd_bytes, TAKE_LENGTH_ID]
QED

Theorem proj_ok_written:
  proj_ok event_written
Proof
  rw[proj_ok_def]
  >- (Cases_on ‘ev’ >> rename1 ‘IO_event nm _ _’ >> Cases_on ‘nm’ >>
      fs[event_written_def, rw_fd_def] >> rw[] >> fs[] >> gvs[AllCaseEqs()]) >>
  fs[v1_event_def, v1_calls_def] >> gvs[rw_fd_def, AllCaseEqs()] >>
  simp[ren_ev_def, event_written_def, TAKE_APPEND1, DROP_APPEND2] >>
  rw[] >> gvs[]
QED

Theorem proj_ok_read:
  proj_ok event_read
Proof
  rw[proj_ok_def]
  >- (Cases_on ‘ev’ >> rename1 ‘IO_event nm _ _’ >> Cases_on ‘nm’ >>
      fs[event_read_def, rw_fd_def] >> rw[] >> fs[] >> gvs[AllCaseEqs()]) >>
  fs[v1_event_def, v1_calls_def] >> gvs[rw_fd_def, AllCaseEqs()] >>
  simp[ren_ev_def, event_read_def] >> rw[] >> gvs[]
QED

(* ------------------------------------------------------------------------
   The invariant of a pass over the trace
   ------------------------------------------------------------------------ *)

(* Passing over evs with k fds opened so far (opn: fd ↦ episode), c is
   episode j: already open, or the fd that opens as episode j *)
Definition proj_inv_def:
  proj_inv pr c j k opn evs ⇔
    EVERY v1_event evs ∧ ALL_DISTINCT (MAP FST opn ++ opened_fds evs) ∧
    ALL_DISTINCT (MAP SND opn) ∧ (∀p. MEM p opn ⇒ SND p < k) ∧
    k + LENGTH (opened_fds evs) ≤ dimword (:64) ∧
    (∀pre ev post. evs = pre ++ ev :: post ∧ pr c ev ≠ [] ⇒
                   MEM c (MAP FST opn ++ opened_fds pre)) ∧
    (MEM (c, j) opn ∨
     ¬MEM c (MAP FST opn) ∧ MEM c (opened_fds evs) ∧ j = k + findi c (opened_fds evs))
End

Theorem v1_event_closed[local]:
  v1_event ev ⇒ event_closed ev = NONE
Proof
  rw[v1_event_def] >> fs[event_closed_def, v1_calls_def] >> rw[] >> fs[]
QED

Theorem ADELKEY_fresh[local]:
  ¬MEM f (MAP FST opn) ⇒ ADELKEY f opn = opn
Proof
  rw[ADELKEY_def] >> irule (iffRL FILTER_EQ_ID) >> fs[EVERY_MEM, MEM_MAP] >>
  metis_tac[]
QED

Theorem opened_fds_cons[local]:
  opened_fds (ev :: evs) =
    (case event_opened ev of SOME f => [f] | NONE => []) ++ opened_fds evs
Proof
  simp[opened_fds_def]
QED

(* The invariant passes over one event *)
Theorem proj_inv_step[local]:
  proj_inv pr c j k opn (ev :: evs) ⇒
  case event_opened ev of
  | SOME f => proj_inv pr c j (k + 1) ((f, k) :: opn) evs ∧ ¬MEM f (MAP FST opn)
  | NONE => proj_inv pr c j k opn evs
Proof
  rw[proj_inv_def] >> CASE_TAC >> fs[opened_fds_cons, ALL_DISTINCT_APPEND] >>
  rpt conj_tac >> rw[] >> fs[] >>
  TRY (first_x_assum (qspecl_then [‘ev :: pre’, ‘ev'’, ‘post’] mp_tac) >>
       simp[opened_fds_cons] >> NO_TAC) >>
  TRY (res_tac >> decide_tac) >>
  TRY (Cases_on ‘c = x’ >> gvs[findi_def] >> NO_TAC) >>
  TRY (CCONTR_TAC >> fs[MEM_MAP] >> res_tac >> fs[] >> NO_TAC) >>
  qpat_x_assum ‘∀pre' ev'' post'. _’ (qspecl_then [‘ev :: pre’, ‘ev'’, ‘post’] mp_tac) >>
  simp[opened_fds_cons]
QED

Theorem proj_inv_episode[local]:
  proj_inv pr c j k opn (ev :: evs) ⇒
  (MEM j (MAP SND opn) ⇔ MEM (c, j) opn) ∧ (¬MEM (c, j) opn ⇒ pr c ev = [])
Proof
  strip_tac >> fs[proj_inv_def, MEM_MAP, EXISTS_PROD]
  >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> res_tac >> fs[]) >>
  CCONTR_TAC >>
  qpat_x_assum ‘∀pre ev post. _’ (qspecl_then [‘[]’, ‘ev’, ‘evs’] mp_tac) >>
  simp[opened_fds_def]
QED

(* MAIN: c's bytes in episode j's events are c's bytes *)
Theorem proj_ch_events:
  ∀evs k opn. proj_ok pr ∧ proj_inv pr c j k opn evs ⇒
              FLAT (MAP (pr c) (ch_events j k opn evs)) = FLAT (MAP (pr c) evs)
Proof
  Induct >> simp[ch_events_def] >> rpt strip_tac >>
  ‘event_closed h = NONE’ by fs[proj_inv_def, v1_event_closed] >>
  drule proj_inv_episode >> strip_tac >>
  drule proj_inv_step >> strip_tac >>
  Cases_on ‘event_opened h’ >> fs[ADELKEY_fresh] >>
  Cases_on ‘MEM (c, j) opn’ >> fs[]
QED

Theorem MEM_SND_inj[local]:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ MEM (a, x) l ∧ MEM (b, x) l ⇒ a = b
Proof
  Induct >> simp[] >> rw[] >> fs[MEM_MAP] >> metis_tac[SND]
QED

(* The renamed trace's first event, projected *)
Theorem ren_head[local]:
  proj_ok pr ∧ proj_inv pr c j k opn (h :: evs) ⇒
  FLAT (MAP (pr (n2w j))
    (case rw_fd h of
     | SOME f => (case ALOOKUP opn f of SOME j' => [ren_ev (n2w j') h] | NONE => [])
     | NONE => [])) = pr c h
Proof
  strip_tac >> drule proj_inv_episode >> strip_tac >>
  ‘(∀c ev. pr c ev ≠ [] ⇒ rw_fd ev = SOME c) ∧
   (∀d d' f ev. rw_fd ev = SOME f ∧ v1_event ev ⇒
                pr d (ren_ev d' ev) = if d = d' then pr f ev else [])’ by fs[proj_ok_def] >>
  ‘v1_event h ∧ ALL_DISTINCT (MAP FST opn) ∧ ALL_DISTINCT (MAP SND opn) ∧
   (∀p. MEM p opn ⇒ SND p < k) ∧ k + LENGTH (opened_fds (h :: evs)) ≤ dimword (:64)’
    by fs[proj_inv_def, ALL_DISTINCT_APPEND] >>
  Cases_on ‘rw_fd h’ >> simp[]
  >- (CCONTR_TAC >> qpat_x_assum ‘∀c ev. pr c ev ≠ [] ⇒ _’ drule >> simp[]) >>
  rename1 ‘rw_fd h = SOME f’ >>
  ‘∀c'. pr c' h ≠ [] ⇒ c' = f’
    by (rpt strip_tac >> qpat_x_assum ‘∀c ev. pr c ev ≠ [] ⇒ _’ drule >> simp[]) >>
  Cases_on ‘ALOOKUP opn f’ >> simp[]
  >- (CCONTR_TAC >> ‘pr c h ≠ []’ by (strip_tac >> fs[]) >>
      ‘c = f’ by (qpat_x_assum ‘∀c'. pr c' h ≠ [] ⇒ _’ (qspec_then ‘c’ mp_tac) >> simp[]) >>
      gvs[] >>
      Cases_on ‘MEM (c, j) opn’ >> fs[] >> fs[ALOOKUP_NONE, MEM_MAP] >> metis_tac[FST]) >>
  rename1 ‘ALOOKUP opn f = SOME j'’ >>
  ‘MEM (f, j') opn’ by metis_tac[ALOOKUP_MEM] >>
  ‘j' < k’ by (first_x_assum (qspec_then ‘(f, j')’ mp_tac) >> simp[]) >>
  qpat_x_assum ‘∀d d' f ev. _’ (qspecl_then [‘n2w j’, ‘n2w j'’, ‘f’, ‘h’] mp_tac) >>
  simp[] >> disch_then kall_tac >>
  Cases_on ‘MEM (c, j) opn’
  >- (‘j < k’ by (first_x_assum (qspec_then ‘(c, j)’ mp_tac) >> simp[]) >>
      ‘j < dimword (:64) ∧ j' < dimword (:64)’ by decide_tac >>
      Cases_on ‘f = c’
      >- (‘ALOOKUP opn c = SOME j’ by (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
          gvs[]) >>
      ‘j' ≠ j’ by (strip_tac >> gvs[] >> metis_tac[MEM_SND_inj]) >>
      ‘j < 18446744073709551616 ∧ j' < 18446744073709551616’ by fs[] >>
      simp[LESS_MOD] >> CCONTR_TAC >>
      qpat_x_assum ‘∀c'. pr c' h ≠ [] ⇒ _’ (qspec_then ‘c’ mp_tac) >> simp[]) >>
  ‘pr c h = []’ by (qpat_x_assum ‘¬MEM (c, j) opn ⇒ _’ mp_tac >> simp[]) >>
  ‘j' ≠ j ∧ j < dimword (:64) ∧ j' < dimword (:64)’
    by (fs[proj_inv_def] >>
        ‘findi c (opened_fds (h::evs)) < LENGTH (opened_fds (h::evs))’ by simp[MEM_findi] >>
        decide_tac) >>
  ‘j < 18446744073709551616 ∧ j' < 18446744073709551616’ by fs[] >>
  simp[LESS_MOD]
QED

(* MAIN: in the renamed trace, fd n2w j's bytes are c's bytes *)
Theorem proj_ren_evs:
  ∀evs k opn. proj_ok pr ∧ proj_inv pr c j k opn evs ⇒
              FLAT (MAP (pr (n2w j)) (ren_evs k opn evs)) = FLAT (MAP (pr c) evs)
Proof
  Induct >> simp[ren_evs_def] >> rpt strip_tac >>
  ‘event_closed h = NONE’ by fs[proj_inv_def, v1_event_closed] >>
  drule_all ren_head >> strip_tac >>
  drule proj_inv_step >> strip_tac >>
  Cases_on ‘event_opened h’ >> fs[ADELKEY_fresh]
QED

(* ------------------------------------------------------------------------
   From the start of a trace
   ------------------------------------------------------------------------ *)

(* MAIN: the j-th opened fd's bytes, by episode and renamed *)
Theorem proj_v1:
  proj_ok pr ∧ EVERY v1_event evs ∧ ALL_DISTINCT (opened_fds evs) ∧
  LENGTH (opened_fds evs) ≤ dimword (:64) ∧
  (∀pre ev post. evs = pre ++ ev :: post ∧ pr c ev ≠ [] ⇒ MEM c (opened_fds pre)) ∧
  j < LENGTH (opened_fds evs) ∧ c = EL j (opened_fds evs) ⇒
  FLAT (MAP (pr c) (ch_events j 0 [] evs)) = FLAT (MAP (pr c) evs) ∧
  FLAT (MAP (pr (n2w j)) (ren_evs 0 [] evs)) = FLAT (MAP (pr c) evs)
Proof
  strip_tac >>
  ‘proj_inv pr c j 0 [] evs’
    by (simp[proj_inv_def] >> gvs[] >> simp[EL_MEM] >>
        metis_tac[findi_EL]) >>
  metis_tac[proj_ch_events, proj_ren_evs]
QED

(* An fd never opened has no bytes *)
Theorem proj_unopened:
  (∀pre ev post. evs = pre ++ ev :: post ∧ pr c ev ≠ [] ⇒ MEM c (opened_fds pre)) ∧
  ¬MEM c (opened_fds evs) ⇒
  FLAT (MAP (pr c) evs) = []
Proof
  rw[FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >> CCONTR_TAC >>
  qpat_x_assum ‘MEM _ evs’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  qpat_x_assum ‘∀pre ev post. _’ (qspecl_then [‘l1’, ‘x’, ‘l2’] mp_tac) >>
  gvs[opened_fds_def]
QED

(* For version 1's events, EchoSpec2's episodes are the endpoint ones *)
Theorem ep_events_v1:
  ∀evs j k opn. EVERY v1_event evs ⇒
    ep_events j k opn evs = ch_events j k opn evs ∧ accepted_fds evs = opened_fds evs
Proof
  ‘∀ev. v1_event ev ⇒ event_opened ev = event_accepted ev’
    by (rw[v1_event_def] >> simp[event_opened_def] >>
        ‘m ≠ «sock_connect»’ by (strip_tac >> fs[v1_calls_def]) >>
        simp[] >> CASE_TAC >> simp[]) >>
  Induct >> simp[ep_events_def, ch_events_def, accepted_fds_def, opened_fds_def] >>
  rw[] >> fs[accepted_fds_def, opened_fds_def]
QED

(* ------------------------------------------------------------------------
   What the clients send, renamed
   ------------------------------------------------------------------------ *)

Theorem rn1_step_APPEND[local]:
  ∀a cs. rn1_step cs (a ++ b) =
         (FST (rn1_step (FST (rn1_step cs a)) b),
          SND (rn1_step cs a) ++ SND (rn1_step (FST (rn1_step cs a)) b))
Proof
  Induct >> simp[rn1_step_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[])
QED

(* The renamed schedule's arrivals are the arrivals renamed *)
Theorem arrivals2_rn1[local]:
  ∀n cs ll. arrivals2_upto n (rn1_sched cs ll) = SND (rn1_step cs (arrivals_upto n ll))
Proof
  Induct >> simp[arrivals2_upto_def, arrivals_upto_def, rn1_step_def] >>
  rpt gen_tac >> simp[rn1_sched_LHD] >> Cases_on ‘LHD ll’ >> simp[rn1_step_def] >>
  drule rn1_sched_LTL >> disch_then (qspec_then ‘cs’ assume_tac) >> simp[] >>
  simp[rn1_step_APPEND, rn1_step_conns]
QED

(* The arrivals of a list make sense from the connections cs: data and EOF
   only on known connections, each connect a new one *)
Definition arrs_ok_def:
  arrs_ok cs [] = T ∧
  arrs_ok cs (Connect l c :: as) = (¬MEM c cs ∧ arrs_ok (cs ++ [c]) as) ∧
  arrs_ok cs (Data c bs :: as) = (MEM c cs ∧ arrs_ok cs as) ∧
  arrs_ok cs (Eof c :: as) = (MEM c cs ∧ arrs_ok cs as)
End

Theorem arrs_ok_APPEND[local]:
  ∀a cs. arrs_ok cs (a ++ b) ⇔ arrs_ok cs a ∧ arrs_ok (cs ++ step_conns a) b
Proof
  Induct >> simp[arrs_ok_def, step_conns_def] >> Cases >> simp[arrs_ok_def] >>
  fs[step_conns_def] >> rw[] >> metis_tac[APPEND_ASSOC, APPEND]
QED

(* A step of effective arrivals makes sense, and adds its connects *)
Theorem step_ok_arrs_ok[local]:
  ∀st s cs. step_ok s st ∧ MAP FST s.conns = REVERSE cs ⇒
            arrs_ok cs st ∧
            MAP FST (FOLDL deliver1 s st).conns = REVERSE (cs ++ step_conns st)
Proof
  Induct >> simp[arrs_ok_def, step_conns_def] >> Cases >>
  simp[step_ok_def, arrival_ok_def] >> rpt gen_tac >> strip_tac >>
  fs[GSYM step_conns_def]
  >- (rename [‘Connect l cn’] >>
      ‘¬MEM cn cs’ by (fs[is_conn_def, ALOOKUP_NONE] >> metis_tac[MEM_REVERSE]) >>
      first_x_assum (qspecl_then [‘deliver1 s (Connect l cn)’, ‘cs ++ [cn]’] mp_tac) >>
      simp[deliver1_def, arrs_ok_def] >> fs[step_conns_def])
  >> (‘MEM c cs’ by (fs[ALOOKUP_NONE] >> metis_tac[MEM_REVERSE, ALOOKUP_MEM, MEM_MAP, FST]) >>
      first_x_assum (drule_then (qspec_then ‘cs’ mp_tac)) >>
      simp[deliver1_def, MAP_FST_AFUPDKEY, arrs_ok_def])
QED

(* MAIN (helper): left alone, a fair world's arrivals make sense *)
Theorem sched_arrs_ok[local]:
  ∀n s cs. sched_wf s ∧ MAP FST s.conns = REVERSE cs ⇒ arrs_ok cs (arrivals_upto n s.sched)
Proof
  Induct >> simp[arrivals_upto_def, arrs_ok_def] >> rpt gen_tac >> strip_tac >>
  Cases_on ‘LHD s.sched’ >> simp[arrs_ok_def] >>
  ‘step_ok s x’
    by (fs[sched_wf_def] >> first_x_assum (qspec_then ‘0’ mp_tac) >>
        simp[ticks_def, next_step_def]) >>
  ‘step_ok (s with sched := THE (LTL s.sched)) x’ by fs[step_ok_with_sched] >>
  drule step_ok_arrs_ok >> disch_then (qspec_then ‘cs’ mp_tac) >> simp[] >> strip_tac >>
  simp[arrs_ok_APPEND] >>
  first_x_assum (qspecl_then [‘tick s’, ‘cs ++ step_conns x’] mp_tac) >>
  simp[sched_wf_tick] >> simp[tick_def, deliver_def] >>
  simp[FOLDL_deliver1_sched]
QED

Definition data_of1_def:
  data_of1 c = λa. case a of Data c' bs => if c' = c then bs else [] | _ => []
End

Definition data_of2_def:
  data_of2 j = λa. case a of Data2 j' bs => if j' = j then bs else [] | _ => []
End

Theorem arrs_ok_distinct[local]:
  ∀as cs. arrs_ok cs as ∧ ALL_DISTINCT cs ⇒ ALL_DISTINCT (cs ++ step_conns as)
Proof
  Induct >> simp[] >> Cases >> simp[arrs_ok_def, step_conns_def] >> rpt strip_tac >>
  fs[GSYM step_conns_def] >>
  rename [‘arrs_ok (cs ++ [cn]) as’] >>
  first_x_assum (qspec_then ‘cs ++ [cn]’ mp_tac) >> simp[] >>
  ‘cs ++ cn :: step_conns as = (cs ++ [cn]) ++ step_conns as’ by simp[] >>
  simp[ALL_DISTINCT_APPEND]
QED

Theorem data_of_simps[local,simp]:
  data_of1 c (Connect l c') = [] ∧ data_of1 c (Data c' bs) = (if c' = c then bs else []) ∧
  data_of1 c (Eof c') = [] ∧
  data_of2 j (Connect2 l) = [] ∧ data_of2 j (Data2 j' bs) = (if j' = j then bs else []) ∧
  data_of2 j (Eof2 j') = []
Proof
  simp[data_of1_def, data_of2_def]
QED

Theorem step_conns_cons_simp[local,simp] = step_conns_cons;

Theorem findi_inj[local]:
  MEM x l ∧ MEM y l ∧ findi x l = findi y l ⇒ x = y
Proof
  metis_tac[EL_findi]
QED

(* Renaming the arrivals: connection c's data is client (findi c)'s *)
Theorem data_rn1[local]:
  ∀as cs. arrs_ok cs as ∧ ALL_DISTINCT cs ⇒
          FLAT (MAP (data_of1 c) as) =
          if MEM c (cs ++ step_conns as)
          then FLAT (MAP (data_of2 (findi c (cs ++ step_conns as))) (SND (rn1_step cs as)))
          else []
Proof
  Induct >- simp[rn1_step_def, step_conns_def] >>
  Cases >> rpt gen_tac >> strip_tac >> simp[rn1_step_cons, rn1_arr_def]
  >- ((* a connect *)
      rename [‘Connect l cn’] >> fs[arrs_ok_def] >>
      first_x_assum (qspec_then ‘cs ++ [cn]’ mp_tac) >> simp[ALL_DISTINCT_APPEND] >>
      disch_then kall_tac >> rw[] >> fs[])
  >> (* data or EOF *)
  fs[arrs_ok_def] >>
  first_x_assum (qspec_then ‘cs’ mp_tac) >> simp[] >> strip_tac >>
  Cases_on ‘MEM c (cs ++ step_conns as)’ >> fs[] >>
  TRY (‘c' ≠ c’ by (strip_tac >> fs[]) >> simp[] >> NO_TAC) >>
  ‘findi c' cs = findi c' (cs ++ step_conns as)’ by simp[indexedListsTheory.findi_APPEND] >>
  ‘c' = c ⇔ findi c' cs = findi c (cs ++ step_conns as)’
    by (eq_tac >> simp[] >> strip_tac >> irule findi_inj >>
        qexists_tac ‘cs ++ step_conns as’ >> fs[]) >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem sched_conns_arrivals[local]:
  ∀n ll. sched_conns n ll = step_conns (arrivals_upto n ll)
Proof
  Induct >> simp[sched_conns_def, arrivals_upto_def, step_conns_def] >>
  rpt gen_tac >> CASE_TAC >> simp[step_conns_def]
QED

(* MAIN: in a version-1 server world, what connection c sends in n steps
   is what its client sends in the version-2 world *)
Theorem sent_v2of1:
  server_world lfd sk ⇒
  sent_upto c n sk =
    if MEM c (sched_conns n sk.sched)
    then sent2_upto (findi c (sched_conns n sk.sched)) n (v2of1 lfd sk)
    else []
Proof
  strip_tac >> fs[server_world_def] >>
  ‘arrs_ok [] (arrivals_upto n sk.sched)’ by (irule sched_arrs_ok >> simp[]) >>
  mp_tac (Q.SPECL [‘arrivals_upto n sk.sched’, ‘[]’] data_rn1) >>
  simp[sched_conns_arrivals, sent_upto_def, sent2_upto_def, v2of1_def, arrivals2_rn1,
       data_of1_def, data_of2_def]
QED


(* ------------------------------------------------------------------------
   The renamed trace, prefix by prefix
   ------------------------------------------------------------------------ *)

(* Renaming a prefix gives a prefix *)
Theorem ren_evs_prefix:
  ∀evs1 evs k opn. evs1 ≼ evs ⇒ ren_evs k opn evs1 ≼ ren_evs k opn evs
Proof
  Induct >> simp[ren_evs_def] >> rpt gen_tac >> Cases_on ‘evs’ >> simp[ren_evs_def] >>
  strip_tac >> gvs[] >> CASE_TAC >> simp[] >> every_case_tac >> simp[]
QED

(* Episodes not yet opened have no bytes in the renamed trace *)
Theorem proj_ren_beyond:
  ∀evs k opn. proj_ok pr ∧ EVERY v1_event evs ∧ (∀p. MEM p opn ⇒ SND p < k) ∧
              k + LENGTH (opened_fds evs) ≤ j ∧ j < dimword (:64) ⇒
              FLAT (MAP (pr (n2w j)) (ren_evs k opn evs)) = []
Proof
  Induct >> simp[ren_evs_def] >> rpt gen_tac >> strip_tac >>
  ‘event_closed h = NONE’ by fs[v1_event_closed] >>
  conj_tac
  >- (Cases_on ‘rw_fd h’ >> simp[] >> Cases_on ‘ALOOKUP opn x’ >> simp[] >>
      rename1 ‘ALOOKUP opn f = SOME j'’ >>
      ‘j' < k’ by (imp_res_tac ALOOKUP_MEM >> res_tac >> fs[]) >>
      ‘pr (n2w j) (ren_ev (n2w j') h) = if (n2w j : word64) = n2w j' then pr f h else []’
        by fs[proj_ok_def] >>
      ‘j' < dimword (:64) ∧ j' ≠ j’ by (fs[opened_fds_cons] >> decide_tac) >>
      fs[]) >>
  Cases_on ‘event_opened h’ >> fs[opened_fds_cons] >>
  first_x_assum irule >> simp[] >>
  rw[] >> fs[MEM_FILTER, ADELKEY_def] >> res_tac >> decide_tac
QED
