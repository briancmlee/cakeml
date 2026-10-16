(*
  A program's behaviour depends on its FFI only through the answers.

  Two FFI states answer the same if, for every sequence of calls, their
  oracles give the same sequence of answers (bytes, or a final outcome).
  Then CakeML's evaluation runs identically in both (evaluate_ffi_rel), so
  a program has the same behaviours (semantics_prog_same_answers).  This is
  generic: the two oracles may have different state types.
*)
Theory endpointSemantics
Ancestors
  ffi semanticPrimitives semanticPrimitivesProps evaluate evaluateProps semantics llist
Libs
  preamble

(* The answers to a sequence of calls; a final outcome ends them *)
Definition run_calls_def:
  run_calls (f : 'a ffi_state) [] = [] ∧
  run_calls f ((n, conf, bytes) :: cs) =
    case f.oracle n f.ffi_state conf bytes of
    | Oracle_return st' bytes' => INL bytes' :: run_calls (f with ffi_state := st') cs
    | Oracle_final out => [INR out]
End

Definition same_answers_def:
  same_answers (f1 : 'a ffi_state) (f2 : 'b ffi_state) ⇔
    ∀cs. run_calls f1 cs = run_calls f2 cs
End

(* The relation kept by evaluation: same answers from now on, same events
   so far *)
Definition ffi_rel_def:
  ffi_rel (f1 : 'a ffi_state) (f2 : 'b ffi_state) ⇔
    same_answers f1 f2 ∧ f1.io_events = f2.io_events
End

Theorem run_calls_io_events[simp]:
  ∀cs f. run_calls (f with io_events := x) cs = run_calls f cs
Proof
  Induct >> simp[run_calls_def, FORALL_PROD] >> rpt gen_tac >> CASE_TAC >> simp[] >>
  first_x_assum (qspec_then ‘f with ffi_state := f'’ mp_tac) >> simp[]
QED

Theorem run_calls_upd[simp]:
  run_calls (f with <| ffi_state := s; io_events := x |>) cs =
  run_calls (f with ffi_state := s) cs
Proof
  ‘f with <| ffi_state := s; io_events := x |> = (f with ffi_state := s) with io_events := x’
    by simp[ffi_state_component_equality] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC[run_calls_io_events]
QED

Theorem call_FFI_rel:
  ffi_rel f1 f2 ⇒
  (∀e. call_FFI f1 n conf bytes = FFI_final e ⇔ call_FFI f2 n conf bytes = FFI_final e) ∧
  (∀f1' b. call_FFI f1 n conf bytes = FFI_return f1' b ⇒
           ∃f2'. call_FFI f2 n conf bytes = FFI_return f2' b ∧ ffi_rel f1' f2')
Proof
  strip_tac >> fs[ffi_rel_def, same_answers_def] >>
  qpat_assum ‘∀cs. _’ (qspec_then ‘[(n,conf,bytes)]’ mp_tac) >>
  REWRITE_TAC[run_calls_def] >>
  Cases_on ‘f1.oracle n f1.ffi_state conf bytes’ >>
  Cases_on ‘f2.oracle n f2.ffi_state conf bytes’ >>
  REWRITE_TAC[ffiTheory.oracle_result_case_def] >> simp[] >> strip_tac >> rveq >>
  simp[call_FFI_def] >> IF_CASES_TAC >> simp[] >> rw[] >> simp[] >>
  rename1 ‘f1.oracle _ _ _ _ = Oracle_return s1 l’ >>
  rename1 ‘f2.oracle _ _ _ _ = Oracle_return s2 l’ >>
  first_x_assum (qspec_then ‘(n, conf, bytes) :: cs’ mp_tac) >> simp[run_calls_def]
QED

(* Only FFI calls end in an FFI error *)
Theorem do_app_ffi_error:
  do_app (refs, f) op vs = SOME (x, Rerr (Rabort (Rffi_error out))) ⇒ ∃s. op = FFI s
Proof
  simp[do_app_cases] >> rw[] >> gvs[AllCaseEqs(), thunk_op_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem do_app_ffi_rel:
  do_app (refs, f1) op vs = SOME ((refs', f1'), r) ∧ ffi_rel f1 f2 ⇒
  ∃f2'. do_app (refs, f2) op vs = SOME ((refs', f2'), r) ∧ ffi_rel f1' f2'
Proof
  strip_tac >> Cases_on ‘∃s. op = FFI s’
  >- (gvs[] >> qpat_x_assum ‘do_app _ _ _ = _’ mp_tac >>
      simp[Once do_app_def, AllCaseEqs()] >> rw[] >>
      drule call_FFI_rel >>
      disch_then (qspecl_then [‘ExtCall s’, ‘MAP (n2w ∘ ORD) (explode conf)’, ‘ws’]
                  strip_assume_tac)
      >> gvs[] >>
      simp[Once do_app_def] >>
      qpat_assum ‘store_lookup _ _ = _’ (fn th => simp[th]) >>
      qpat_assum ‘call_FFI f2 _ _ _ = _’ (fn th => simp[th]) >>
      TRY (qpat_assum ‘store_assign _ _ _ = _’ (fn th => simp[th])) >>
      first_assum ACCEPT_TAC) >>
  ‘f1' = f1’
    by (‘∀s. op ≠ FFI s’ by metis_tac[] >>
        drule_all semanticPrimitivesPropsTheory.do_app_ffi_unchanged >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  ‘∀out. r ≠ Rerr (Rabort (Rffi_error out))’
    by (rpt strip_tac >> rveq >> drule do_app_ffi_error >> fs[]) >>
  drule_all do_app_SOME_ffi_same >> disch_then (qspec_then ‘f2’ assume_tac) >>
  qexists_tac ‘f2’ >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem dec_clock_ffi[local,simp]:
  dec_clock (s with ffi := f) = (dec_clock s) with ffi := f ∧
  (dec_clock s).ffi = s.ffi
Proof
  simp[dec_clock_def]
QED

Theorem do_eval_res_ffi[local]:
  do_eval_res vs s = (s1, r) ⇒
  s1.ffi = s.ffi ∧ ∀f : 'b ffi_state. do_eval_res vs (s with ffi := f) = (s1 with ffi := f, r)
Proof
  rw[do_eval_res_def] >> every_case_tac >> gvs[]
QED

Theorem do_app_ffi_rel_imp[local]:
  do_app (refs, f1) op vs = SOME ((refs', f1'), r) ⇒
  ∀f2. ffi_rel f1 f2 ⇒
       ∃f2'. do_app (refs, f2) op vs = SOME ((refs', f2'), r) ∧ ffi_rel f1' f2'
Proof
  metis_tac[do_app_ffi_rel]
QED

(* MAIN: evaluation runs identically against FFI states with the same
   answers *)
Theorem evaluate_ffi_rel:
  (∀(s:'a semanticPrimitives$state) env e s' r.
     evaluate s env e = (s',r) ⇒
     ∀f2 : 'b ffi_state. ffi_rel s.ffi f2 ⇒
       ∃f2'. evaluate (s with ffi := f2) env e = (s' with ffi := f2', r) ∧
             ffi_rel s'.ffi f2') ∧
  (∀(s:'a semanticPrimitives$state) env v pes errv s' r.
     evaluate_match s env v pes errv = (s',r) ⇒
     ∀f2 : 'b ffi_state. ffi_rel s.ffi f2 ⇒
       ∃f2'. evaluate_match (s with ffi := f2) env v pes errv = (s' with ffi := f2', r) ∧
             ffi_rel s'.ffi f2') ∧
  (∀(s:'a semanticPrimitives$state) env ds s' r.
     evaluate_decs s env ds = (s',r) ⇒
     ∀f2 : 'b ffi_state. ffi_rel s.ffi f2 ⇒
       ∃f2'. evaluate_decs (s with ffi := f2) env ds = (s' with ffi := f2', r) ∧
             ffi_rel s'.ffi f2')
Proof
  ho_match_mp_tac full_evaluate_ind >> rpt strip_tac >>
  gvs[full_evaluate_def, AllCaseEqs(), PULL_EXISTS] >>
  ntac 2 (
    rpt (first_x_assum (drule_then strip_assume_tac) ORELSE
         qpat_x_assum ‘do_app _ _ _ = NONE’
           (assume_tac o GEN_ALL o MATCH_MP do_app_NONE_ffi) ORELSE
         qpat_x_assum ‘do_app _ _ _ = SOME _’
           (fn th => drule_then strip_assume_tac (MATCH_MP do_app_ffi_rel_imp th)) ORELSE
         qpat_x_assum ‘do_eval_res _ _ = _’
           (strip_assume_tac o MATCH_MP do_eval_res_ffi)) >>
    gvs[]) >>
  metis_tac[]
QED

Theorem ffi_rel_sym:
  ffi_rel f1 f2 ⇒ ffi_rel f2 f1
Proof
  rw[ffi_rel_def, same_answers_def]
QED

Theorem evaluate_prog_with_clock_ffi_rel:
  ffi_rel st.ffi f2 ⇒
  ∃f2'. evaluate_prog_with_clock (st with ffi := f2) env k prog =
          (f2', SND (evaluate_prog_with_clock st env k prog)) ∧
        ffi_rel (FST (evaluate_prog_with_clock st env k prog)) f2'
Proof
  rw[evaluate_prog_with_clock_def] >>
  Cases_on ‘evaluate_decs (st with clock := k) env prog’ >>
  drule (CONJUNCT2 (CONJUNCT2 evaluate_ffi_rel)) >>
  disch_then (qspec_then ‘f2’ mp_tac) >> simp[] >> strip_tac >> fs[]
QED

Theorem semantics_prog_ffi_rel_imp:
  ffi_rel st.ffi f2 ∧ semantics_prog st env prog b ⇒
  semantics_prog (st with ffi := f2) env prog b
Proof
  strip_tac >>
  ‘∀k. ∃f2'. evaluate_prog_with_clock (st with ffi := f2) env k prog =
               (f2', SND (evaluate_prog_with_clock st env k prog)) ∧
             ffi_rel (FST (evaluate_prog_with_clock st env k prog)) f2'’
    by metis_tac[evaluate_prog_with_clock_ffi_rel] >>
  ‘∀k. (FST (evaluate_prog_with_clock (st with ffi := f2) env k prog)).io_events =
       (FST (evaluate_prog_with_clock st env k prog)).io_events ∧
       SND (evaluate_prog_with_clock (st with ffi := f2) env k prog) =
       SND (evaluate_prog_with_clock st env k prog)’
    by (gen_tac >> first_x_assum (qspec_then ‘k’ strip_assume_tac) >>
        fs[ffi_rel_def]) >>
  Cases_on ‘b’ >> fs[semanticsTheory.semantics_prog_def] >>
  TRY (qexists_tac ‘k’) >> TRY gen_tac >>
  rpt (qpat_x_assum ‘∀k. _’ (qspec_then ‘k’ strip_assume_tac)) >> gvs[ffi_rel_def]
QED

(* MAIN: a program has the same behaviours against FFI states with the same
   answers *)
Theorem semantics_prog_same_answers:
  ffi_rel st.ffi f2 ⇒
  (semantics_prog (st with ffi := f2) env prog b ⇔ semantics_prog st env prog b)
Proof
  strip_tac >> eq_tac >- (
    strip_tac >>
    ‘st = (st with ffi := f2) with ffi := st.ffi’ by simp[state_component_equality] >>
    pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
    irule semantics_prog_ffi_rel_imp >> fs[ffi_rel_sym]) >>
  metis_tac[semantics_prog_ffi_rel_imp]
QED
