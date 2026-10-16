(*
  Route (d), stage S1 (design/46): the spec's per-episode bytes as folds
  over the trace.  The episode state is (k, opn): the accepts so far, and
  each open accepted fd's episode.  An event's received / sent bytes
  count for episode j when its fd is open in episode j at that point.

    l0_read_fold : l0_read j evs = ep_rd j (0, []) evs
    l0_sent_fold : l0_sent j evs = ep_sn j (0, []) evs

  and the folds split over appended traces (ep_rd_APPEND, ep_sn_APPEND).
*)
Theory honestEchoL0Trace
Ancestors
  alist ffi honestEchoL0Spec
Libs
  preamble

(* The episode state after an event, and after a trace *)
Definition l0_ep_step_def:
  l0_ep_step ((k : num), (opn : (word64 # num) list)) ev =
    case l0_event_accepted ev of
    | SOME f => (k + 1, (f, k) :: ADELKEY f opn)
    | NONE =>
        case l0_event_closed ev of
        | SOME f => (k, ADELKEY f opn)
        | NONE => (k, opn)
End

Definition l0_ep_st_def:
  l0_ep_st s evs = FOLDL l0_ep_step s evs
End

(* The fd of a recv event, and of a send event *)
Definition recv_fd_def:
  recv_fd (IO_event (ExtCall n) conf bytes) =
    (if n = «sys_recv» ∧ LENGTH conf = 8 then SOME (bytes_fd conf) else NONE) ∧
  recv_fd _ = NONE
End

Definition send_fd_def:
  send_fd (IO_event (ExtCall n) conf bytes) =
    (if n = «sys_send» ∧ 8 ≤ LENGTH conf then SOME (bytes_fd (TAKE 8 conf)) else NONE) ∧
  send_fd _ = NONE
End

(* Episode j's bytes, event by event: an event's bytes pf f ev (f the
   event's fd, fdf ev) count for j when f is open in episode j *)
Definition ep_fold_def:
  ep_fold pf fdf j s [] = [] ∧
  ep_fold pf fdf j s (ev :: evs) =
    (case fdf ev of
     | SOME f => if ALOOKUP (SND s) f = SOME (j:num) then pf (f:word64) ev else []
     | NONE => []) ++
    ep_fold pf fdf j (l0_ep_step s ev) evs
End

(* Episode j's received bytes, and the bytes taken from its sends *)
Overload ep_rd = “ep_fold l0_event_recv recv_fd”
Overload ep_sn = “ep_fold l0_event_sent send_fd”

Theorem l0_ep_st_simps[simp]:
  l0_ep_st s [] = s ∧
  l0_ep_st s (ev :: evs) = l0_ep_st (l0_ep_step s ev) evs ∧
  l0_ep_st s (xs ++ ys) = l0_ep_st (l0_ep_st s xs) ys
Proof
  simp[l0_ep_st_def, FOLDL_APPEND]
QED

Theorem ep_fold_APPEND:
  ∀xs s. ep_fold pf fdf j s (xs ++ ys) = ep_fold pf fdf j s xs ++ ep_fold pf fdf j (l0_ep_st s xs) ys
Proof
  Induct >> simp[ep_fold_def]
QED

(* Only recv / send events of a matching fd contribute *)
Theorem l0_event_recv_fd:
  l0_event_recv f ev ≠ [] ⇒ recv_fd ev = SOME f
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bytes’ >> Cases_on ‘nm’ >>
  rw[l0_event_recv_def, recv_fd_def] >> gvs[]
QED

Theorem l0_event_sent_fd:
  l0_event_sent f ev ≠ [] ⇒ send_fd ev = SOME f
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bytes’ >> Cases_on ‘nm’ >>
  rw[l0_event_sent_def, send_fd_def] >> gvs[]
QED

Theorem FST_l0_ep_st:
  ∀evs k opn. FST (l0_ep_st (k, opn) evs) = k + LENGTH (l0_accepted evs)
Proof
  Induct >> fs[l0_accepted_def] >> rpt gen_tac >>
  simp[l0_ep_step_def] >> every_case_tac >> fs[]
QED

Theorem l0_accepted_CONS:
  l0_accepted (ev :: evs) =
    (case l0_event_accepted ev of SOME f => [f] | NONE => []) ++ l0_accepted evs
Proof
  simp[l0_accepted_def]
QED

(* The episode state's invariant: keys distinct, episodes distinct and
   below the accept count *)
Definition ep_ok_def:
  ep_ok ((k : num), (opn : (word64 # num) list)) ⇔
    ALL_DISTINCT (MAP FST opn) ∧ ALL_DISTINCT (MAP SND opn) ∧
    EVERY (λi. i < k) (MAP SND opn)
End

(* ADELKEY / ALOOKUP helpers: verbatim copies of close-v2-sim's
   asyncHLEpisodes local lemmas (recorded per the temporary-copy rule) *)
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

Theorem not_mem_snd_adelkey[local]:
  ALL_DISTINCT (MAP SND opn) ∧ ALOOKUP opn f = SOME j ⇒ ¬MEM j (MAP SND (ADELKEY f opn))
Proof
  rpt strip_tac >> drule ALOOKUP_MEM >> strip_tac >>
  gvs[ADELKEY_def, MEM_MAP, MEM_FILTER] >>
  Cases_on ‘y’ >> gvs[] >> metis_tac[distinct_snd_mem]
QED



Theorem ep_ok_step:
  ep_ok st ⇒ ep_ok (l0_ep_step st ev)
Proof
  PairCases_on ‘st’ >> simp[l0_ep_step_def] >> every_case_tac >>
  gvs[ep_ok_def, ALL_DISTINCT_ADELKEY, EVERY_MEM] >> rw[] >>
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER] >> res_tac >> fs[] >>
  metis_tac[prim_recTheory.LESS_REFL]
QED

Theorem NOT_MEM_SND_ADELKEY[local]:
  ¬MEM j (MAP SND opn) ⇒ ¬MEM j (MAP SND (ADELKEY g opn))
Proof
  metis_tac[MEM_SND_ADELKEY]
QED

(* One event: its bytes for episode j, as the spec counts them (when j is
   open, by j's fd) and as the fold does (by the event's fd's episode) *)
Theorem ep_head[local]:
  (∀f ev. pf f ev ≠ [] ⇒ fdf ev = SOME f) ∧ ALL_DISTINCT (MAP SND (opn : (word64 # num) list)) ∧
  (MEM j (MAP SND opn) ⇒ ALOOKUP opn f = SOME j) ⇒
  FLAT (MAP (pf f) (if MEM j (MAP SND opn) then [h : io_event] else [])) =
  (case fdf h of SOME g => if ALOOKUP opn g = SOME j then pf g h else [] | NONE => [])
Proof
  strip_tac >> Cases_on ‘MEM j (MAP SND opn)’ >> simp[]
  >- (gvs[] >> Cases_on ‘pf f h = []’ >> simp[] >> every_case_tac >> simp[] >> rw[] >>
      TRY (rename1 ‘fdf h = SOME g’ >> ‘g = f’ by metis_tac[alookup_snd_unique] >> gvs[]) >>
      res_tac >> gvs[])
  >> every_case_tac >> simp[] >> rw[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >>
  res_tac >> fs[]
QED

(* The spec's per-episode filter is the fold, for episode j's fd f: open
   now, accepted later in the trace, or never open from now on *)
Theorem ep_events_fold:
  (∀f ev. pf f ev ≠ [] ⇒ fdf ev = SOME f) ⇒
  ∀evs k opn j f.
    ep_ok (k, opn) ∧
    (ALOOKUP opn f = SOME j ∨
     (¬MEM j (MAP SND opn) ∧ k ≤ j ∧ j < k + LENGTH (l0_accepted evs) ∧
      f = EL (j - k) (l0_accepted evs)) ∨
     (¬MEM j (MAP SND opn) ∧ (j < k ∨ k + LENGTH (l0_accepted evs) ≤ j))) ⇒
    FLAT (MAP (pf f) (l0_ep_events j k opn evs)) = ep_fold pf fdf j (k, opn) evs
Proof
  strip_tac >> Induct >- simp[l0_ep_events_def, ep_fold_def] >>
  rpt gen_tac >> strip_tac >>
  simp[l0_ep_events_def, ep_fold_def] >>
  (* this event's bytes *)
  DEP_REWRITE_TAC[ep_head] >>
  TRY (conj_tac >- (gvs[ep_ok_def] >> rw[] >> gvs[])) >>
  (* j not open: the fold counts nothing for this event either *)
  TRY (‘(case fdf h of SOME g => if ALOOKUP opn g = SOME j then pf g h else [] | NONE => []) = []’
         by (every_case_tac >> rw[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >>
             res_tac >> fs[]) >>
       pop_assum SUBST1_TAC) >>
  simp[] >>
  (* the rest, from the next episode state *)
  ‘ep_ok (l0_ep_step (k,opn) h)’ by simp[ep_ok_step] >>
  pop_assum mp_tac >> simp[l0_ep_step_def] >>
  every_case_tac >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  gvs[l0_accepted_CONS, ALOOKUP_ADELKEY_eq] >>
  ‘MEM j (MAP SND opn) ⇒ j < k’ by (rw[] >> gvs[ep_ok_def, EVERY_MEM]) >>
  TRY (‘MEM j (MAP SND opn)’
         by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND])) >>
  TRY (‘¬MEM j (MAP SND (ADELKEY f opn))’
         by (irule not_mem_snd_adelkey >> gvs[ep_ok_def])) >>
  gvs[NOT_MEM_SND_ADELKEY] >>
  TRY (Cases_on ‘j = k’ >> gvs[] >>
       ‘j − k = SUC (j − (k + 1))’ by decide_tac >> simp[] >> NO_TAC) >>
  rw[] >> gvs[NOT_MEM_SND_ADELKEY]
QED

(* An episode that is not open and never opens has no events *)
Theorem ep_events_never:
  ∀evs k opn. ¬MEM j (MAP SND opn) ∧ (j < k ∨ k + LENGTH (l0_accepted evs) ≤ j) ⇒
              l0_ep_events j k opn evs = []
Proof
  Induct >> simp[l0_ep_events_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[] >> first_x_assum irule >>
  gvs[l0_accepted_CONS, NOT_MEM_SND_ADELKEY]
QED

(* MAIN (S1): the spec's per-episode bytes are the folds *)
Theorem l0_read_fold:
  l0_read j evs = ep_rd j (0, []) evs
Proof
  rw[l0_read_def]
  >- (irule ep_events_fold >> simp[l0_event_recv_fd, ep_ok_def]) >>
  ‘FLAT (MAP (l0_event_recv 0w) (l0_ep_events j 0 [] evs)) = ep_rd j (0, []) evs’
    by (irule ep_events_fold >> simp[l0_event_recv_fd, ep_ok_def]) >>
  ‘l0_ep_events j 0 [] evs = []’ by (irule ep_events_never >> simp[]) >>
  gvs[]
QED

Theorem l0_sent_fold:
  l0_sent j evs = ep_sn j (0, []) evs
Proof
  rw[l0_sent_def]
  >- (irule ep_events_fold >> simp[l0_event_sent_fd, ep_ok_def]) >>
  ‘FLAT (MAP (l0_event_sent 0w) (l0_ep_events j 0 [] evs)) = ep_sn j (0, []) evs’
    by (irule ep_events_fold >> simp[l0_event_sent_fd, ep_ok_def]) >>
  ‘l0_ep_events j 0 [] evs = []’ by (irule ep_events_never >> simp[]) >>
  gvs[]
QED
