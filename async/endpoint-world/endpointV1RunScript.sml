(*
  Version 1 as version 2 along a whole run (design/35 §4, step 2-3):
  a disciplined program diverges alike in a version-1 world and in the
  related version-2 world.
   - replays: the events of a run are the oracle's answers, in order
     (any FFI; from evaluateProps' call_FFI_rel);
   - v12_events: along disciplined events of a version-1 run, both worlds
     give the same answers (endpointV1Sim's v12_call_wf, call by call);
   - v12_diverge: semantics_prog_upto (async/quiet/ffi) carries a
     disciplined Diverge io over, and determinism every behaviour.
*)
Theory endpointV1Run
Ancestors
  llist lprefix_lub ffi semantics evaluateProps ffiAgreeUpto
  ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec socketV2FFI socketV2Fair
  EchoSpec2 endpointSpecForms endpointInstances endpointV1Sim
Libs
  preamble

(* ------------------------------------------------------------------------
   The events of a run replay the oracle
   ------------------------------------------------------------------------ *)

Definition replays_def:
  replays orc st [] st' = (st' = st) ∧
  replays orc st (IO_event n conf bl :: evs) st' =
    ∃st1. orc n st conf (MAP FST bl) = Oracle_return st1 (MAP SND bl) ∧
          replays orc st1 evs st'
End

Theorem replays_APPEND:
  ∀l1 st st'. replays orc st (l1 ++ l2) st' ⇔ ∃m. replays orc st l1 m ∧ replays orc m l2 st'
Proof
  Induct >> simp[replays_def] >> Cases >> simp[replays_def] >> metis_tac[]
QED

Theorem call_FFI_replays:
  call_FFI f n conf bytes = FFI_return f' b ∧ f.oracle = orc ∧
  replays orc st0 f.io_events f.ffi_state ⇒
  f'.oracle = orc ∧ replays orc st0 f'.io_events f'.ffi_state
Proof
  rw[call_FFI_def] >> gvs[AllCaseEqs()] >>
  rw[replays_APPEND] >> qexists_tac ‘f.ffi_state’ >> simp[replays_def, MAP_ZIP]
QED

Theorem RTC_call_FFI_rel_replays:
  ∀f f'. RTC call_FFI_rel f f' ⇒
         f.oracle = orc ∧ replays orc st0 f.io_events f.ffi_state ⇒
         replays orc st0 f'.io_events f'.ffi_state
Proof
  ho_match_mp_tac RTC_INDUCT >> rw[call_FFI_rel_def] >>
  first_x_assum irule >> metis_tac[call_FFI_replays]
QED

(* MAIN (helper): a clocked run's events replay the oracle from the start *)
Theorem clock_run_replays:
  st.ffi.io_events = [] ⇒
  replays st.ffi.oracle st.ffi.ffi_state
    (FST (evaluate_prog_with_clock st env k prog)).io_events
    (FST (evaluate_prog_with_clock st env k prog)).ffi_state
Proof
  rw[evaluate_prog_with_clock_def] >> pairarg_tac >> simp[] >>
  qspecl_then [‘st with clock := k’, ‘env’, ‘prog’] mp_tac
    (CONJUNCT2 (CONJUNCT2 evaluate_call_FFI_rel)) >>
  simp[] >> strip_tac >>
  drule RTC_call_FFI_rel_replays >> simp[replays_def]
QED

(* ------------------------------------------------------------------------
   Disciplined events get the same answers
   ------------------------------------------------------------------------ *)

Theorem event_fds_call[local]:
  socket_fn n ≠ NONE ⇒ event_fds (IO_event (ExtCall n) conf bl) = call_fds n conf
Proof
  rw[socket_fn_def, event_fds_def, call_fds_def]
QED

Theorem open_now_v1[local]:
  socket_fn n ≠ NONE ⇒
  open_now (IO_event (ExtCall n) conf bl :: evs) =
    case event_accepted (IO_event (ExtCall n) conf bl) of
    | SOME f => f :: open_now evs
    | NONE => open_now evs
Proof
  rw[socket_fn_def, open_now_def, event_opened_def, event_closed_def] >>
  every_case_tac >> fs[]
QED

(* The version-2 fds open only grow, and an accept adds the fd it returns *)
Theorem socket2_oracle_open_fds[local]:
  socket2_oracle (ExtCall n) s conf bytes = Oracle_return s' out ∧ socket_fn n ≠ NONE ⇒
  (∀f. MEM f (MAP FST s.open_fds) ⇒ MEM f (MAP FST s'.open_fds)) ∧
  (event_accepted (IO_event (ExtCall n) conf (ZIP (bytes, out))) = SOME c ∧
   LENGTH out = LENGTH bytes ⇒ MEM c (MAP FST s'.open_fds))
Proof
  ‘∀as s. (FOLDL deliver2 s as).open_fds = s.open_fds’
    by (Induct >> simp[] >> Cases >> rw[deliver2_def, update_client_def]) >>
  ‘∀s. (tick2 s).open_fds = s.open_fds’ by (rw[tick2_def] >> CASE_TAC >> simp[]) >>
  strip_tac >>
  ‘n = «sock_poll» ∨ n = «sock_accept» ∨ n = «sock_read» ∨ n = «sock_write»’
    by (fs[socket_fn_def] >> rw[] >> fs[]) >>
  qpat_x_assum ‘socket2_oracle _ _ _ _ = _’ mp_tac >>
  simp[socket2_oracle_def, socket2_fn_def] >> rw[]
  >- (gvs[ffi_sock_poll2_def, AllCaseEqs()])
  >- (gvs[event_accepted_def])
  >- (gvs[ffi_sock_accept2_def, sock_accept2_def, AllCaseEqs()])
  >- (gvs[ffi_sock_accept2_def, sock_accept2_def, AllCaseEqs(), event_accepted_def, MAP_ZIP])
  >- (gvs[ffi_sock_read2_def, sock_read2_def, update_client_def, AllCaseEqs()])
  >- (gvs[event_accepted_def])
  >- (gvs[ffi_sock_write2_def, sock_write2_def, update_client_def, AllCaseEqs()])
  >> gvs[event_accepted_def]
QED

Theorem socket2_ffi_with[local]:
  socket2_ffi s with ffi_state := s' = socket2_ffi s'
Proof
  simp[socket2_ffi_def]
QED

Theorem socket_ffi_with[local]:
  socket_ffi s with ffi_state := s' = socket_ffi s'
Proof
  simp[socket_ffi_def]
QED

(* The events evs, after done, name only lfd or fds open by then *)
Definition disc_after_def:
  disc_after lfd done evs ⇔
    ∀pre ev post. evs = pre ++ ev :: post ⇒
                  EVERY (λf. f = lfd ∨ MEM f (open_now (REVERSE (done ++ pre)))) (event_fds ev)
End

(* MAIN *)
Theorem v12_events:
  ∀evs done s1 s2 t.
    replays socket_oracle s1 evs t ∧ v12rel lfd ll0 s1 s2 ∧ sched_wf s1 ∧
    (∀f. MEM f (open_now (REVERSE done)) ⇒ MEM f (MAP FST s2.open_fds)) ∧
    disc_after lfd done evs ⇒
    ffi_answers (socket2_ffi s2) (calls_of evs) = ffi_answers (socket_ffi s1) (calls_of evs)
Proof
  Induct >- simp[calls_of_def, ffi_answers_def] >>
  Cases >> rename1 ‘IO_event nm conf bl’ >> rpt gen_tac >> strip_tac >>
  fs[replays_def] >>
  ‘∃n. nm = ExtCall n ∧ socket_fn n ≠ NONE’
    by (Cases_on ‘nm’ >> gvs[socket_oracle_def, AllCaseEqs()]) >>
  gvs[] >>
  ‘EVERY (v12ok lfd s2) (call_fds n conf)’
    by (fs[disc_after_def] >>
        first_x_assum (qspecl_then [‘[]’, ‘IO_event (ExtCall n) conf bl’, ‘evs’] mp_tac) >>
        simp[event_fds_call, EVERY_MEM, v12ok_def] >> metis_tac[]) >>
  drule_all v12_call_wf >> disch_then (qspec_then ‘MAP FST bl’ strip_assume_tac) >>
  gvs[] >>
  simp[calls_of_def, ffi_answers_def, socket_ffi_def, socket2_ffi_def] >>
  REWRITE_TAC[GSYM socket_ffi_def, GSYM socket2_ffi_def,
              REWRITE_RULE[socket_ffi_def, socket2_ffi_def] socket_ffi_with,
              REWRITE_RULE[socket_ffi_def, socket2_ffi_def] socket2_ffi_with] >>
  REWRITE_TAC[GSYM calls_of_def] >>
  first_x_assum irule >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  qexists_tac ‘done ++ [IO_event (ExtCall n) conf bl]’ >>
  reverse conj_tac
  >- (fs[disc_after_def] >> rw[] >>
      first_x_assum (qspecl_then [‘IO_event (ExtCall n) conf bl :: pre’, ‘ev’, ‘post’] mp_tac) >>
      simp[] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]) >>
  simp[REVERSE_APPEND, open_now_v1] >>
  drule_all socket2_oracle_open_fds >> strip_tac >>
  ‘ZIP (MAP FST bl, MAP SND bl) = bl’ by simp[ZIP_MAP_FST_SND_EQ] >>
  CASE_TAC >> rw[] >> gvs[] >>
  first_x_assum irule >> simp[]
QED

(* ------------------------------------------------------------------------
   Whole runs
   ------------------------------------------------------------------------ *)

(* A diverging program has no other behaviour *)
Theorem diverge_only:
  semantics_prog st env prog (Diverge io) ⇒
  (semantics_prog st env prog b ⇔ b = Diverge io)
Proof
  rw[EQ_IMP_THM] >> Cases_on ‘b’ >> fs[semantics_prog_def] >>
  TRY (metis_tac[unique_lprefix_lub] >> NO_TAC) >>
  qpat_x_assum ‘∀k. ∃ffi. _’ (qspec_then ‘k’ strip_assume_tac) >> gvs[]
QED

Theorem prefix_MAP[local]:
  ∀l cs. cs ≼ MAP f l ⇒ ∃l'. l' ≼ l ∧ cs = MAP f l'
Proof
  Induct >> simp[] >> rpt strip_tac >> Cases_on ‘cs’ >> fs[] >>
  first_x_assum drule >> strip_tac >> qexists_tac ‘h::l'’ >> simp[]
QED

Theorem init_state_ffi[local]:
  (init_state f).ffi = f
Proof
  simp[ml_progTheory.init_state_def]
QED

(* The calls of a diverging version-1 run are those of events that replay
   the oracle and lie on the trace *)
Theorem v1_clock_calls:
  semantics_prog (init_state (socket_ffi s1)) init_env prog (Diverge io) ∧
  cs ≼ clock_calls (init_state (socket_ffi s1)) init_env prog k ⇒
  ∃evs t. cs = calls_of evs ∧ replays socket_oracle s1 evs t ∧ LPREFIX (fromList evs) io
Proof
  qabbrev_tac ‘st = init_state (socket_ffi s1)’ >>
  simp[semantics_prog_def] >> strip_tac >>
  qpat_x_assum ‘∀k. ∃ffi. _’ (qspec_then ‘k’ strip_assume_tac) >>
  fs[ext_def, calls_of_def] >>
  drule prefix_MAP >> strip_tac >> gvs[GSYM calls_of_def] >>
  ‘replays socket_oracle s1 ffi.io_events ffi.ffi_state’
    by (qspecl_then [‘st’, ‘init_env’, ‘k’, ‘prog’] mp_tac
          (Q.GENL [‘st’, ‘env’, ‘k’, ‘prog’] clock_run_replays) >>
        simp[Abbr ‘st’, init_state_ffi, socket_ffi_def]) >>
  ‘LPREFIX (fromList ffi.io_events) io’
    by (fs[lprefix_lub_def] >> first_x_assum irule >> simp[] >>
        qexists_tac ‘k’ >> simp[]) >>
  fs[IS_PREFIX_APPEND] >> rename1 ‘ffi.io_events = evs ++ rest’ >>
  gvs[replays_APPEND] >>
  qexistsl_tac [‘evs’, ‘m’] >> simp[] >>
  irule LPREFIX_TRANS >> first_x_assum (irule_at Any) >>
  simp[LPREFIX_fromList, from_toList]
QED

(* Version 1's calls only *)
Theorem replays_v1_calls:
  ∀evs s t. replays socket_oracle s evs t ⇒
            EVERY (λ(n, conf, bytes). ∃m. n = ExtCall m ∧ MEM m v1_calls) (calls_of evs)
Proof
  Induct >> simp[calls_of_def] >> Cases >> simp[replays_def] >> rpt gen_tac >>
  strip_tac >> REWRITE_TAC[GSYM calls_of_def] >> conj_tac
  >- (Cases_on ‘f’ >> fs[socket_oracle_def] >> Cases_on ‘socket_fn s'’ >> fs[] >>
      fs[socket_fn_def, v1_calls_def] >> every_case_tac >> fs[]) >>
  metis_tac[]
QED

(* MAIN: a disciplined diverging version-1 run gets the same answers from
   any related version-2 world *)
Theorem v12_agree:
  semantics_prog (init_state (socket_ffi s1)) init_env prog (Diverge io) ∧
  fd_disciplined lfd io ∧ v12rel lfd ll0 s1 s2 ∧ sched_wf s1 ∧
  cs ≼ clock_calls (init_state (socket_ffi s1)) init_env prog k ⇒
  ffi_answers (socket_ffi s1) cs = ffi_answers (socket2_ffi s2) cs
Proof
  strip_tac >> drule_all v1_clock_calls >> strip_tac >> gvs[] >>
  CONV_TAC SYM_CONV >> irule v12_events >>
  conj_tac >- simp[] >> conj_tac >- metis_tac[] >>
  qexistsl_tac [‘[]’, ‘lfd’, ‘ll0’] >> simp[open_now_def] >>
  rw[disc_after_def] >>
  fs[fd_disciplined_def, always_def] >>
  first_x_assum (qspec_then ‘pre ++ [ev]’ mp_tac) >>
  impl_tac
  >- (irule LPREFIX_TRANS >> first_x_assum (irule_at Any) >>
      simp[LPREFIX_fromList, from_toList]) >>
  simp[]
QED

(* MAIN: a disciplined diverging run in a version-1 world is a run in any
   related version-2 world *)
Theorem v12_diverge:
  semantics_prog (init_state (socket_ffi s1)) init_env prog (Diverge io) ∧
  fd_disciplined lfd io ∧ v12rel lfd ll0 s1 s2 ∧ sched_wf s1 ⇒
  semantics_prog (init_state (socket2_ffi s2)) init_env prog (Diverge io)
Proof
  strip_tac >>
  ‘init_state (socket2_ffi s2) = init_state (socket_ffi s1) with ffi := socket2_ffi s2’
    by simp[ml_progTheory.init_state_def, semanticPrimitivesTheory.state_component_equality] >>
  pop_assum SUBST1_TAC >> irule semantics_prog_upto >>
  REWRITE_TAC[init_state_ffi] >> rpt conj_tac >> TRY (simp[socket2_ffi_def, socket_ffi_def] >> NO_TAC) >>
  rw[agree_upto_def] >> irule v12_agree >> metis_tac[]
QED
