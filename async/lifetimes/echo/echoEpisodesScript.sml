(*
  EchoEpisodesSpec's episodes, by renaming.  rn_evs replays EchoEpisodesSpec's
  bookkeeping of open episodes (ep_events: k accepts so far, opn the open
  fds and their episodes) and renames the fd of each read and write event
  to its episode's handle hdl lfd j.  Then what episode j read and wrote
  is what the renamed trace read from and wrote to hdl lfd j
  (ep_read_rn, ep_written_rn), as long as the handles of the episodes
  are distinct.  So the per-episode projections of the version-2 trace
  become EchoSpec's per-fd projections of a version-1 style trace.
*)
Theory echoEpisodes
Ancestors
  alist words ffi socketWorld EchoSpec EchoEpisodesSpec loopHandlesModel
Libs
  preamble

(* The fd a read or write event is on *)
Definition ev_fd_def:
  ev_fd (IO_event (ExtCall n) conf bytes) =
    (if n = «sock_read» ∧ LENGTH conf = 8 then SOME (bytes_fd conf)
     else if n = «sock_write» ∧ 8 ≤ LENGTH conf then SOME (bytes_fd (TAKE 8 conf))
     else NONE) ∧
  ev_fd _ = NONE
End

(* The same event on fd c *)
Definition ev_ren_def:
  ev_ren c (IO_event (ExtCall n) conf bytes) =
    (if n = «sock_read» ∧ LENGTH conf = 8 then IO_event (ExtCall n) (fd_bytes c) bytes
     else if n = «sock_write» ∧ 8 ≤ LENGTH conf then
       IO_event (ExtCall n) (fd_bytes c ++ DROP 8 conf) bytes
     else IO_event (ExtCall n) conf bytes) ∧
  ev_ren c ev = ev
End

(* The trace with each read and write renamed to its episode's handle;
   events outside open episodes are dropped *)
Definition rn_evs_def:
  rn_evs lfd k opn [] = [] ∧
  rn_evs lfd k opn (ev :: evs) =
    (case ev_fd ev of
     | SOME f => (case ALOOKUP opn f of SOME j => [ev_ren (hdl lfd j) ev] | NONE => [])
     | NONE => []) ++
    (case event_accepted ev of
     | SOME f => rn_evs lfd (k + 1) ((f, k) :: ADELKEY f opn) evs
     | NONE =>
         case event_closed ev of
         | SOME f => rn_evs lfd k (ADELKEY f opn) evs
         | NONE => rn_evs lfd k opn evs)
End

(* ------------------------------------------------------------------------
   The projections and renaming
   ------------------------------------------------------------------------ *)

(* A per-fd projection of events that only sees reads or writes on the fd *)
Definition proj_ok_def:
  proj_ok (pj : word64 -> io_event -> 'a list) ⇔
    (∀c ev. ev_fd ev = NONE ⇒ pj c ev = []) ∧
    (∀c f ev. ev_fd ev = SOME f ∧ c ≠ f ⇒ pj c ev = []) ∧
    (∀c c' f ev. ev_fd ev = SOME f ⇒ pj c' (ev_ren c ev) = if c' = c then pj f ev else [])
End

Theorem proj_ok_event_read:
  proj_ok event_read
Proof
  simp[proj_ok_def] >> rpt conj_tac >> rpt gen_tac >>
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bs’ >> Cases_on ‘nm’ >>
  simp[ev_fd_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[ev_ren_def, event_read_def] >>
  Cases_on ‘c' = c’ >> simp[] >> rw[] >> gvs[]
QED

Theorem proj_ok_event_written:
  proj_ok event_written
Proof
  simp[proj_ok_def] >> rpt conj_tac >> rpt gen_tac >>
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bs’ >> Cases_on ‘nm’ >>
  simp[ev_fd_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[ev_ren_def, event_written_def, TAKE_APPEND1, DROP_APPEND1, TAKE_LENGTH_TOO_LONG] >>
  Cases_on ‘c' = c’ >> simp[] >> rw[] >> gvs[]
QED

(* An episode that has ended is never reopened *)
Theorem ep_events_ended[local]:
  ∀evs k opn. j < k ∧ ¬MEM j (MAP SND opn) ⇒ ep_events j k opn evs = []
Proof
  Induct >> rw[ep_events_def] >> every_case_tac >> simp[] >>
  first_x_assum irule >> simp[MEM_MAP, ADELKEY_def, MEM_FILTER] >>
  gvs[MEM_MAP] >> metis_tac[]
QED

Theorem MEM_SND_ADELKEY[local]:
  MEM j (MAP SND (ADELKEY f opn)) ⇒ MEM j (MAP SND opn)
Proof
  simp[ADELKEY_def, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem ALL_DISTINCT_ADELKEY[local]:
  ALL_DISTINCT (MAP g opn) ⇒ ALL_DISTINCT (MAP g (ADELKEY f opn))
Proof
  simp[ADELKEY_def] >> Induct_on ‘opn’ >> rw[] >> gvs[MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

Theorem ALOOKUP_ADELKEY_eq[local]:
  ALOOKUP (ADELKEY k al) x = if x = k then NONE else ALOOKUP al x
Proof
  rw[ALOOKUP_ADELKEY]
QED

Theorem ev_kinds[local]:
  (ev_fd ev ≠ NONE ⇒ event_accepted ev = NONE ∧ event_closed ev = NONE) ∧
  (event_accepted ev ≠ NONE ⇒ event_closed ev = NONE)
Proof
  Cases_on ‘ev’ >> Cases_on ‘f’ >>
  rw[ev_fd_def, event_accepted_def, event_closed_def] >> gvs[]
QED

Theorem alookup_snd_unique[local]:
  ALL_DISTINCT (MAP SND (opn : (word64 # num) list)) ∧ ALOOKUP opn f = SOME j ∧ ALOOKUP opn f' = SOME j ⇒ f = f'
Proof
  rw[] >> imp_res_tac ALOOKUP_MEM >>
  ‘∀l : (word64 # num) list. ALL_DISTINCT (MAP SND l) ∧ MEM (f, j) l ∧ MEM (f' : word64, j) l ⇒ f = f'’
    by (Induct >> simp[FORALL_PROD] >> rw[] >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem distinct_snd_mem[local]:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ MEM (a, v) l ∧ MEM (b, v) l ⇒ a = b
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

(* Closing (or reusing) the fd of an open episode ends it *)
Theorem not_mem_snd_adelkey[local]:
  ALL_DISTINCT (MAP SND opn) ∧ ALOOKUP opn f = SOME j ⇒ ¬MEM j (MAP SND (ADELKEY f opn))
Proof
  rpt strip_tac >> drule ALOOKUP_MEM >> strip_tac >>
  gvs[ADELKEY_def, MEM_MAP, MEM_FILTER] >>
  Cases_on ‘y’ >> gvs[] >> metis_tac[distinct_snd_mem]
QED

Overload PJ = “λpj c evs. FLAT (MAP (pj c) evs)”

Overload rn_head = “λlfd opn ev.
  case ev_fd ev of
  | SOME f => (case ALOOKUP opn f of SOME j => [ev_ren (hdl lfd j) ev] | NONE => [])
  | NONE => []”

Theorem rn_head_open[local]:
  proj_ok pj ∧ (∀j1 j2. j1 < N ∧ j2 < N ⇒ (hdl lfd j1 = hdl lfd j2 ⇔ j1 = j2)) ∧
  ALL_DISTINCT (MAP SND opn) ∧ (∀j. MEM j (MAP SND opn) ⇒ j < N) ∧
  ALOOKUP opn f = SOME j ⇒
  PJ pj (hdl lfd j) (rn_head lfd opn ev) = pj f ev
Proof
  strip_tac >> qpat_x_assum ‘proj_ok _’ (strip_assume_tac o REWRITE_RULE[proj_ok_def]) >>
  ‘MEM j (MAP SND opn)’
    by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> qexists_tac ‘(f, j)’ >> simp[]) >>
  ‘j < N’ by res_tac >>
  Cases_on ‘ev_fd ev’ >> simp[] >>
  TRY (qpat_x_assum ‘∀c ev. ev_fd ev = NONE ⇒ _’ drule >> simp[] >> NO_TAC) >>
  rename1 ‘ev_fd ev = SOME f'’ >> Cases_on ‘ALOOKUP opn f'’ >> simp[]
  >- (‘f' ≠ f’ by (strip_tac >> fs[]) >>
      qpat_x_assum ‘∀c f ev. ev_fd ev = SOME f ∧ c ≠ f ⇒ _’
        (qspecl_then [‘f’, ‘f'’, ‘ev’] mp_tac) >> simp[]) >>
  rename1 ‘ALOOKUP opn f' = SOME j'’ >>
  qpat_x_assum ‘∀c c' f ev. ev_fd ev = SOME f ⇒ _’
    (qspecl_then [‘hdl lfd j'’, ‘hdl lfd j’, ‘f'’, ‘ev’] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then SUBST1_TAC >>
  Cases_on ‘f' = f’
  >- (‘j' = j’ by fs[] >> simp[]) >>
  ‘j' ≠ j’ by metis_tac[alookup_snd_unique] >>
  ‘MEM j' (MAP SND opn)’
    by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> qexists_tac ‘(f', j')’ >> simp[]) >>
  ‘j' < N’ by res_tac >>
  ‘hdl lfd j ≠ hdl lfd j'’
    by (qpat_x_assum ‘∀j1 j2. _’ (qspecl_then [‘j’, ‘j'’] mp_tac) >> simp[]) >>
  simp[] >>
  qpat_x_assum ‘∀c f ev. ev_fd ev = SOME f ∧ c ≠ f ⇒ _’
    (qspecl_then [‘f’, ‘f'’, ‘ev’] mp_tac) >> simp[]
QED

Theorem rn_head_other[local]:
  proj_ok pj ∧ (∀j1 j2. j1 < N ∧ j2 < N ⇒ (hdl lfd j1 = hdl lfd j2 ⇔ j1 = j2)) ∧
  (∀j. MEM j (MAP SND opn) ⇒ j < N) ∧ j < N ∧ ¬MEM j (MAP SND opn) ⇒
  PJ pj (hdl lfd j) (rn_head lfd opn ev) = []
Proof
  strip_tac >> qpat_x_assum ‘proj_ok _’ (strip_assume_tac o REWRITE_RULE[proj_ok_def]) >>
  Cases_on ‘ev_fd ev’ >> simp[] >> rename1 ‘ev_fd ev = SOME f'’ >>
  Cases_on ‘ALOOKUP opn f'’ >> simp[] >> rename1 ‘ALOOKUP opn f' = SOME j'’ >>
  ‘MEM j' (MAP SND opn)’
    by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> qexists_tac ‘(f', j')’ >> simp[]) >>
  ‘j' ≠ j’ by (strip_tac >> fs[]) >>
  ‘j' < N’ by res_tac >>
  ‘hdl lfd j ≠ hdl lfd j'’
    by (qpat_x_assum ‘∀j1 j2. _’ (qspecl_then [‘j’, ‘j'’] mp_tac) >> simp[]) >>
  qpat_x_assum ‘∀c c' f ev. ev_fd ev = SOME f ⇒ _’
    (qspecl_then [‘hdl lfd j'’, ‘hdl lfd j’, ‘f'’, ‘ev’] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> simp[]
QED

Theorem accepted_fds_CONS[local]:
  accepted_fds (ev :: evs) =
  (case event_accepted ev of SOME f => [f] | NONE => []) ++ accepted_fds evs
Proof
  simp[accepted_fds_def]
QED

Theorem rn_evs_CONS[local]:
  rn_evs lfd k opn (ev :: evs) =
  rn_head lfd opn ev ++
  (case event_accepted ev of
   | SOME f => rn_evs lfd (k + 1) ((f, k) :: ADELKEY f opn) evs
   | NONE =>
       case event_closed ev of
       | SOME f => rn_evs lfd k (ADELKEY f opn) evs
       | NONE => rn_evs lfd k opn evs)
Proof
  simp[Once rn_evs_def]
QED

(* The state after an event keeps the invariant *)
Theorem opn_step[local]:
  ALL_DISTINCT (MAP FST opn) ∧ ALL_DISTINCT (MAP SND opn) ∧
  (∀j. MEM j (MAP SND opn) ⇒ j < (k:num)) ⇒
  ALL_DISTINCT (MAP FST ((f, k) :: ADELKEY f opn)) ∧
  ALL_DISTINCT (MAP SND ((f, k) :: ADELKEY f opn)) ∧
  (∀j. MEM j (MAP SND ((f, k) :: ADELKEY f opn)) ⇒ j < k + 1) ∧
  ALL_DISTINCT (MAP FST (ADELKEY f opn)) ∧ ALL_DISTINCT (MAP SND (ADELKEY f opn)) ∧
  (∀j. MEM j (MAP SND (ADELKEY f opn)) ⇒ j < k)
Proof
  strip_tac >>
  ‘∀j. MEM j (MAP SND (ADELKEY f opn)) ⇒ j < k’ by metis_tac[MEM_SND_ADELKEY] >>
  ‘¬MEM k (MAP SND (ADELKEY f opn))’ by (strip_tac >> res_tac >> fs[]) >>
  ‘¬MEM f (MAP FST (ADELKEY f opn))’ by simp[ADELKEY_def, MEM_MAP, MEM_FILTER] >>
  ‘ALL_DISTINCT (MAP FST (ADELKEY f opn)) ∧ ALL_DISTINCT (MAP SND (ADELKEY f opn))’
    by metis_tac[ALL_DISTINCT_ADELKEY] >>
  fs[] >> rw[] >> res_tac >> fs[]
QED

(* the facts about the event itself, for an open episode j on f *)
val open_facts =
  ‘MEM j (MAP SND opn) ∧ PJ pj (hdl lfd j) (rn_head lfd opn ev) = pj f ev’;

(* MAIN, generalised: episode j's projection is the renamed trace's
   projection on hdl lfd j, for an open episode (on fd f), an ended one,
   and a future one (the (j - k)-th accepted fd from now on) *)
Theorem rn_evs_proj:
  ∀evs k opn.
    proj_ok pj ∧
    (∀j1 j2. j1 < N ∧ j2 < N ⇒ (hdl lfd j1 = hdl lfd j2 ⇔ j1 = j2)) ∧
    k + LENGTH (accepted_fds evs) ≤ N ∧
    ALL_DISTINCT (MAP FST opn) ∧ ALL_DISTINCT (MAP SND opn) ∧
    (∀j. MEM j (MAP SND opn) ⇒ j < k) ⇒
    (∀j f. ALOOKUP opn f = SOME j ⇒
           PJ pj f (ep_events j k opn evs) = PJ pj (hdl lfd j) (rn_evs lfd k opn evs)) ∧
    (∀j. j < k ∧ ¬MEM j (MAP SND opn) ⇒ PJ pj (hdl lfd j) (rn_evs lfd k opn evs) = []) ∧
    (∀j. k ≤ j ∧ j < N ⇒
         PJ pj (hdl lfd j) (rn_evs lfd k opn evs) =
         if j − k < LENGTH (accepted_fds evs) then
           PJ pj (EL (j − k) (accepted_fds evs)) (ep_events j k opn evs)
         else [])
Proof
  Induct
  >- simp[ep_events_def, rn_evs_def, accepted_fds_def]
  >> rpt gen_tac >> strip_tac >> rename1 ‘ev :: evs’
  >> ‘∀j. j < k ⇒ j < N’
       by (rpt strip_tac >> qpat_x_assum ‘k + _ ≤ N’ mp_tac >> simp[accepted_fds_CONS])
  >> ‘∀j. MEM j (MAP SND opn) ⇒ j < N’
       by (rpt strip_tac >> qpat_x_assum ‘∀j. MEM j (MAP SND opn) ⇒ j < k’ drule >> simp[])
  >> ‘∀j f. ALOOKUP opn f = SOME j ⇒ MEM j (MAP SND opn)’
       by (rpt strip_tac >> imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >>
           qexists_tac ‘(f, j)’ >> simp[])
  (* the event itself *)
  >> ‘∀j f. ALOOKUP opn f = SOME j ⇒ PJ pj (hdl lfd j) (rn_head lfd opn ev) = pj f ev’
       by (rpt strip_tac >> drule_all rn_head_open >> simp[])
  >> ‘∀j. j < N ∧ ¬MEM j (MAP SND opn) ⇒ PJ pj (hdl lfd j) (rn_head lfd opn ev) = []’
       by (rpt strip_tac >> drule_all rn_head_other >> simp[])
  >> ‘∀j. k ≤ j ⇒ ¬MEM j (MAP SND opn)’
       by (rpt strip_tac >> qpat_x_assum ‘∀j. MEM j (MAP SND opn) ⇒ j < k’ drule >> simp[])
  >> simp[rn_evs_CONS, ep_events_def, accepted_fds_CONS]
  >> Cases_on ‘event_accepted ev’ >> simp[]
  >- (Cases_on ‘event_closed ev’ >> simp[]
      (* neither an accept nor a close *)
      >- (first_x_assum (qspecl_then [‘k’, ‘opn’] mp_tac) >>
          impl_tac >- fs[accepted_fds_CONS] >> strip_tac >>
          rpt conj_tac >> rpt strip_tac
          >- (open_facts by metis_tac[] >> fs[])
          >> fs[])
      (* a close of f2 *)
      >> rename1 ‘event_closed ev = SOME f2’ >>
      first_x_assum (qspecl_then [‘k’, ‘ADELKEY f2 opn’] mp_tac) >>
      impl_tac
      >- (qspecl_then [‘opn’, ‘k’, ‘f2’] mp_tac (Q.GENL [‘opn’, ‘k’, ‘f’] opn_step) >>
          impl_tac >- fs[] >> strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      fs[accepted_fds_CONS]) >>
      strip_tac >>
      rpt conj_tac >> rpt strip_tac
      >- (open_facts by metis_tac[] >> simp[] >>
          Cases_on ‘f2 = f’
          >- (pop_assum SUBST_ALL_TAC >>
              ‘¬MEM j (MAP SND (ADELKEY f opn))’
                by (irule not_mem_snd_adelkey >> simp[]) >>
              ‘j < k’ by metis_tac[] >>
              fs[ep_events_ended])
          >> ‘ALOOKUP (ADELKEY f2 opn) f = SOME j’ by simp[ALOOKUP_ADELKEY_eq] >>
          fs[])
      >- (‘¬MEM j (MAP SND (ADELKEY f2 opn))’ by metis_tac[MEM_SND_ADELKEY] >> fs[])
      >> ‘¬MEM j (MAP SND (ADELKEY f2 opn))’ by metis_tac[MEM_SND_ADELKEY] >> fs[])
  (* an accept of f2 *)
  >> rename1 ‘event_accepted ev = SOME f2’ >>
  first_x_assum (qspecl_then [‘k + 1’, ‘(f2, k) :: ADELKEY f2 opn’] mp_tac) >>
  impl_tac
  >- (qspecl_then [‘opn’, ‘k’, ‘f2’] mp_tac (Q.GENL [‘opn’, ‘k’, ‘f’] opn_step) >>
      impl_tac >- fs[] >> strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      fs[accepted_fds_CONS]) >>
  strip_tac >>
  rpt conj_tac >> rpt strip_tac
  >- (open_facts by metis_tac[] >> simp[] >>
      Cases_on ‘f2 = f’
      >- (pop_assum SUBST_ALL_TAC >>
          ‘j < k’ by metis_tac[] >>
          ‘¬MEM j (MAP SND ((f, k) :: ADELKEY f opn))’
            by (simp[] >> irule not_mem_snd_adelkey >> simp[]) >>
          ‘j < k + 1’ by simp[] >>
          fs[ep_events_ended])
      >> ‘ALOOKUP ((f2, k) :: ADELKEY f2 opn) f = SOME j’ by simp[ALOOKUP_ADELKEY_eq] >>
      fs[])
  >- (‘¬MEM j (MAP SND ((f2, k) :: ADELKEY f2 opn))’
        by (simp[] >> metis_tac[MEM_SND_ADELKEY, prim_recTheory.LESS_REFL]) >>
      ‘j < k + 1’ by simp[] >> fs[])
  >> Cases_on ‘j = k’
  >- (gvs[] >>
      qpat_x_assum ‘∀j f. ALOOKUP ((f2, k) :: _) f = SOME j ⇒ _’
        (qspecl_then [‘k’, ‘f2’] mp_tac) >> simp[])
  >> ‘k + 1 ≤ j’ by simp[] >> fs[] >>
  Cases_on ‘j < k + (LENGTH (accepted_fds evs) + 1)’ >> simp[] >>
  ‘0 < LENGTH (accepted_fds evs)’ by simp[] >>
  ‘j − k = SUC (j − (k + 1))’ by simp[] >> simp[]
QED

(* MAIN: what episode j read and wrote is what the renamed trace read from
   and wrote to the j-th handle *)
Theorem ep_read_rn:
  (∀j1 j2. j1 < N ∧ j2 < N ⇒ (hdl lfd j1 = hdl lfd j2 ⇔ j1 = j2)) ∧
  LENGTH (accepted_fds evs) ≤ N ∧ j < N ⇒
  ep_read j evs = bytes_read_from (hdl lfd j) (rn_evs lfd 0 [] evs)
Proof
  strip_tac >>
  qspecl_then [‘evs’, ‘0’, ‘[]’] mp_tac
    (Q.ISPEC ‘event_read’ (Q.GEN ‘pj’ rn_evs_proj)) >>
  simp[proj_ok_event_read] >> disch_then (qspec_then ‘j’ mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  simp[ep_read_def, bytes_read_from_def] >> rw[] >> gvs[]
QED

Theorem ep_written_rn:
  (∀j1 j2. j1 < N ∧ j2 < N ⇒ (hdl lfd j1 = hdl lfd j2 ⇔ j1 = j2)) ∧
  LENGTH (accepted_fds evs) ≤ N ∧ j < N ⇒
  ep_written j evs = bytes_written_to (hdl lfd j) (rn_evs lfd 0 [] evs)
Proof
  strip_tac >>
  qspecl_then [‘evs’, ‘0’, ‘[]’] mp_tac
    (Q.ISPEC ‘event_written’ (Q.GEN ‘pj’ rn_evs_proj)) >>
  simp[proj_ok_event_written] >> disch_then (qspec_then ‘j’ mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  simp[ep_written_def, bytes_written_to_def] >> rw[] >> gvs[]
QED

(* ------------------------------------------------------------------------
   Splitting the trace
   ------------------------------------------------------------------------ *)

(* The bookkeeping (accepts so far, open fds and their episodes) after evs *)
Definition ep_st_def:
  ep_st (k:num) (opn:(word64 # num) list) [] = (k, opn) ∧
  ep_st k opn (ev :: evs) =
    case event_accepted ev of
    | SOME f => ep_st (k + 1) ((f, k) :: ADELKEY f opn) evs
    | NONE =>
        case event_closed ev of
        | SOME f => ep_st k (ADELKEY f opn) evs
        | NONE => ep_st k opn evs
End

Theorem rn_evs_APPEND:
  ∀e1 k opn.
    rn_evs lfd k opn (e1 ++ e2) =
    rn_evs lfd k opn e1 ++ rn_evs lfd (FST (ep_st k opn e1)) (SND (ep_st k opn e1)) e2
Proof
  Induct >> simp[rn_evs_def, ep_st_def] >> rpt gen_tac >>
  every_case_tac >> simp[]
QED

Theorem ep_st_APPEND:
  ∀e1 k opn.
    ep_st k opn (e1 ++ e2) = ep_st (FST (ep_st k opn e1)) (SND (ep_st k opn e1)) e2
Proof
  Induct >> simp[ep_st_def] >> rpt gen_tac >> every_case_tac >> simp[]
QED

Theorem accepted_fds_APPEND:
  accepted_fds (e1 ++ e2) = accepted_fds e1 ++ accepted_fds e2
Proof
  simp[accepted_fds_def]
QED

Theorem ep_events_APPEND:
  ∀e1 k opn.
    ep_events j k opn (e1 ++ e2) =
    ep_events j k opn e1 ++ ep_events j (FST (ep_st k opn e1)) (SND (ep_st k opn e1)) e2
Proof
  Induct >> simp[ep_events_def, ep_st_def] >> rpt gen_tac >> every_case_tac >> simp[]
QED

(* The projections only grow along the trace *)
Theorem ep_read_mono:
  evs ≼ evs' ⇒ ep_read j evs ≼ ep_read j evs'
Proof
  rw[IS_PREFIX_APPEND] >> rw[ep_read_def, accepted_fds_APPEND, ep_events_APPEND,
                             bytes_read_from_def, EL_APPEND1] >>
  gvs[]
QED

Theorem ep_written_mono:
  evs ≼ evs' ⇒ ep_written j evs ≼ ep_written j evs'
Proof
  rw[IS_PREFIX_APPEND] >> rw[ep_written_def, accepted_fds_APPEND, ep_events_APPEND,
                             bytes_written_to_def, EL_APPEND1] >>
  gvs[]
QED

(* The number of accepts is EchoEpisodesSpec's count *)
Theorem ep_st_count:
  ∀evs k opn. FST (ep_st k opn evs) = k + LENGTH (accepted_fds evs)
Proof
  Induct >- simp[ep_st_def, accepted_fds_def] >>
  simp[ep_st_def, accepted_fds_CONS] >> rpt gen_tac >> every_case_tac >> fs[]
QED

(* ------------------------------------------------------------------------
   Closing
   ------------------------------------------------------------------------ *)

(* Every read that returns EOF is immediately followed by a close of its fd *)
Definition eof_then_close_def:
  eof_then_close evs ⇔
    ∀p1 e p2 f. evs = p1 ++ e :: p2 ∧ event_eof e = SOME f ⇒
                ∃e' p3. p2 = e' :: p3 ∧ event_closed e' = SOME f
End

Theorem event_eof_kinds[local]:
  event_eof e = SOME f ⇒ event_accepted e = NONE ∧ event_closed e = NONE
Proof
  Cases_on ‘e’ >> Cases_on ‘f'’ >>
  simp[event_eof_def, event_accepted_def, event_closed_def] >> rw[]
QED

Theorem eof_then_close_CONS[local]:
  eof_then_close (e :: evs) ⇒ eof_then_close evs
Proof
  rw[eof_then_close_def] >> first_x_assum irule >>
  qexistsl [‘e'’, ‘e :: p1’] >> simp[]
QED

(* MAIN: then an episode in which the program read its client's EOF is
   closed in the same window *)
Theorem ep_eof_closes:
  ∀evs k opn.
    eof_then_close evs ∧ EXISTS (λev. event_eof ev = SOME f) (ep_events j k opn evs) ⇒
    EXISTS (λev. event_closed ev = SOME f) (ep_events j k opn evs)
Proof
  Induct >> simp[ep_events_def] >> rpt gen_tac >> strip_tac >>
  drule eof_then_close_CONS >> strip_tac
  >- (Cases_on ‘MEM j (MAP SND opn)’ >> fs[] >>
      drule event_eof_kinds >> strip_tac >>
      qpat_x_assum ‘eof_then_close (h :: _)’ mp_tac >> simp[eof_then_close_def] >>
      disch_then (qspecl_then [‘[]’, ‘h’, ‘evs’, ‘f’] mp_tac) >> simp[] >> strip_tac >>
      gvs[ep_events_def])
  >> disj2_tac >> every_case_tac >> fs[] >> first_x_assum irule >> fs[]
QED
