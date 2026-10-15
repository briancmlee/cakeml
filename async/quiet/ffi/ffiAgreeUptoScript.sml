(*
  A program's behaviour depends on its FFI only through the answers to
  the calls it actually makes.

  This restricts close-v2's endpointSemantics (spike/endpoint-world),
  where the two FFI states must give the same answers to EVERY sequence
  of calls, to the calls of the run: with L the calls of a run under f1,
  if f1 and f2 answer the same to every prefix of L, the program runs the
  same against f2 (evaluate_ffi_upto, semantics_prog_upto).

  Use: two worlds whose oracles differ only on calls this program never
  makes (QuietSpec's select, which fails on a non-socket fd, and #46's,
  which does not).

  MAIN: evaluate_ffi_upto, semantics_prog_upto.
*)
Theory ffiAgreeUpto
Ancestors
  ffi semanticPrimitives semanticPrimitivesProps evaluate evaluateProps
  semantics llist
Libs
  preamble

(* The answers to a sequence of calls; a final outcome ends them *)
Definition ffi_answers_def:
  ffi_answers (f : 'a ffi_state) [] = [] ∧
  ffi_answers f ((n, conf, bytes) :: cs) =
    case f.oracle n f.ffi_state conf bytes of
    | Oracle_return st' bytes' => INL bytes' :: ffi_answers (f with ffi_state := st') cs
    | Oracle_final out => [INR out]
End

(* The calls recorded in a list of events *)
Definition calls_of_def:
  calls_of evs = MAP (λe. case e of IO_event n c bl => (n, c, MAP FST bl)) evs
End

(* The call that ended a run in an FFI error *)
Definition final_ffi_def:
  final_ffi (Final_event n c b out) = [(n, c, b)]
End

Definition final_err_def:
  final_err e =
    case e of
    | Rabort (Rffi_error fe) => final_ffi fe
    | _ => []
End

Definition final_call_def:
  final_call r = case r of Rerr e => final_err e | _ => []
End

(* The calls of a run that ended in FFI state f with result r *)
Definition ext_def:
  ext (f : 'a ffi_state) r = calls_of f.io_events ++ final_call r
End

(* Same events so far, and the same answers to the calls that continue
   them within L *)
Definition ffi_rel_upto_def:
  ffi_rel_upto L (f1 : 'a ffi_state) (f2 : 'b ffi_state) ⇔
    f1.io_events = f2.io_events ∧
    ∀cs. calls_of f1.io_events ++ cs ≼ L ⇒ ffi_answers f1 cs = ffi_answers f2 cs
End

Theorem ffi_answers_io_events[simp]:
  ∀cs f. ffi_answers (f with io_events := x) cs = ffi_answers f cs
Proof
  Induct >> simp[ffi_answers_def, FORALL_PROD] >> rpt gen_tac >> CASE_TAC >> simp[] >>
  first_x_assum (qspec_then ‘f with ffi_state := f'’ mp_tac) >> simp[]
QED

Theorem ffi_answers_upd[simp]:
  ffi_answers (f with <| ffi_state := s; io_events := x |>) cs =
  ffi_answers (f with ffi_state := s) cs
Proof
  ‘f with <| ffi_state := s; io_events := x |> = (f with ffi_state := s) with io_events := x’
    by simp[ffi_state_component_equality] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC[ffi_answers_io_events]
QED

Theorem calls_of_APPEND[simp]:
  calls_of (l1 ++ l2) = calls_of l1 ++ calls_of l2
Proof
  simp[calls_of_def]
QED

Theorem calls_of_prefix:
  l1 ≼ l2 ⇒ calls_of l1 ≼ calls_of l2
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

Theorem final_call_simps[simp]:
  final_call (Rval v) = [] ∧ final_call (Rerr e) = final_err e ∧
  final_err (Rraise x) = [] ∧
  final_err (Rabort (Rffi_error fe)) = final_ffi fe ∧
  final_ffi (Final_event n c b out) = [(n, c, b)] ∧
  final_err (Rabort Rtype_error) = [] ∧
  final_err (Rabort Rtimeout_error) = []
Proof
  simp[final_call_def, final_err_def, final_ffi_def]
QED

Theorem ext_list_result[simp]:
  ext f (list_result r) = ext f r
Proof
  Cases_on ‘r’ >> simp[ext_def, final_call_def]
QED

Theorem ext_combine_dec_result[simp]:
  ext f (combine_dec_result env r) = ext f r
Proof
  Cases_on ‘r’ >> simp[ext_def, final_call_def, combine_dec_result_def]
QED

(* One call within L *)
Theorem call_FFI_upto:
  ffi_rel_upto L f1 f2 ∧
  (n ≠ ExtCall «» ⇒ calls_of f1.io_events ++ [(n, conf, bytes)] ≼ L) ⇒
  (∀e. call_FFI f1 n conf bytes = FFI_final e ⇔ call_FFI f2 n conf bytes = FFI_final e) ∧
  (∀f1' b. call_FFI f1 n conf bytes = FFI_return f1' b ⇒
           ∃f2'. call_FFI f2 n conf bytes = FFI_return f2' b ∧ ffi_rel_upto L f1' f2')
Proof
  strip_tac >> Cases_on ‘n = ExtCall «»’ >- gvs[call_FFI_def] >>
  fs[ffi_rel_upto_def] >>
  qpat_assum ‘∀cs. _’ (qspec_then ‘[(n,conf,bytes)]’ mp_tac) >>
  impl_tac >- simp[] >>
  REWRITE_TAC[ffi_answers_def] >>
  Cases_on ‘f1.oracle n f1.ffi_state conf bytes’ >>
  Cases_on ‘f2.oracle n f2.ffi_state conf bytes’ >>
  REWRITE_TAC[ffiTheory.oracle_result_case_def] >> simp[] >> strip_tac >> rveq >>
  simp[call_FFI_def] >> IF_CASES_TAC >> simp[] >> rw[] >> simp[] >>
  rename1 ‘f1.oracle _ _ _ _ = Oracle_return s1 l’ >>
  rename1 ‘f2.oracle _ _ _ _ = Oracle_return s2 l’ >>
  ‘MAP FST (ZIP (bytes, l)) = bytes’ by simp[MAP_ZIP] >>
  qpat_x_assum ‘∀cs. _ ⇒ ffi_answers _ _ = _’ (qspec_then ‘(n, conf, bytes) :: cs’ mp_tac) >>
  impl_tac
  >- (qpat_x_assum ‘_ ++ cs ≼ L’ mp_tac >>
      qpat_x_assum ‘f1.io_events = _’ (fn th => REWRITE_TAC[GSYM th]) >>
      simp[calls_of_def, MAP_ZIP] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]) >>
  simp[ffi_answers_def]
QED

(* The calls of one FFI call's outcome *)
Theorem call_FFI_calls:
  call_FFI f n conf bytes = res ∧ n ≠ ExtCall «» ⇒
  calls_of f.io_events ++ [(n, conf, bytes)] =
  case res of
  | FFI_return f' b => calls_of f'.io_events
  | FFI_final e => calls_of f.io_events ++ final_ffi e
Proof
  rw[call_FFI_def] >> every_case_tac >> gvs[calls_of_def, MAP_ZIP, final_ffi_def]
QED

Theorem do_app_ffi_error:
  do_app (refs, f) op vs = SOME (x, Rerr (Rabort (Rffi_error out))) ⇒ ∃s. op = FFI s
Proof
  simp[do_app_cases] >> rw[] >> gvs[AllCaseEqs(), thunk_op_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem do_app_ffi_upto:
  do_app (refs, f1) op vs = SOME ((refs', f1'), r) ∧ ffi_rel_upto L f1 f2 ∧
  ext f1' r ≼ L ⇒
  ∃f2'. do_app (refs, f2) op vs = SOME ((refs', f2'), r) ∧ ffi_rel_upto L f1' f2'
Proof
  strip_tac >> Cases_on ‘∃s. op = FFI s’
  >- (gvs[] >> qpat_x_assum ‘do_app _ _ _ = _’ mp_tac >>
      simp[Once do_app_def, AllCaseEqs()] >> rw[] >>
      ‘s ≠ «» ⇒ calls_of f1.io_events ++ [(ExtCall s, MAP (n2w ∘ ORD) (explode conf), ws)] ≼ L’
        by (strip_tac >> drule call_FFI_calls >> simp[] >> strip_tac >>
            qpat_x_assum ‘ext _ _ ≼ L’ mp_tac >> simp[ext_def, final_call_def] >>
            every_case_tac >> gvs[]) >>
      drule call_FFI_upto >>
      disch_then (qspecl_then [‘ExtCall s’, ‘MAP (n2w ∘ ORD) (explode conf)’, ‘ws’] mp_tac) >> simp[] >>
      strip_tac >> gvs[] >>
      simp[Once do_app_def] >>
      qpat_assum ‘store_lookup _ _ = _’ (fn th => simp[th]) >>
      TRY (qpat_x_assum ‘∀e. outcome = e ⇔ _’
             (assume_tac o REWRITE_RULE[] o Q.SPEC ‘outcome’)) >>
      qpat_assum ‘call_FFI f2 _ _ _ = _’ (fn th => simp[th]) >>
      TRY (qpat_assum ‘store_assign _ _ _ = _’ (fn th => simp[th])) >>
      fs[ffi_rel_upto_def]) >>
  ‘f1' = f1’
    by (‘∀s. op ≠ FFI s’ by metis_tac[] >>
        drule_all semanticPrimitivesPropsTheory.do_app_ffi_unchanged >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  ‘∀out. r ≠ Rerr (Rabort (Rffi_error out))’
    by (rpt strip_tac >> rveq >> drule do_app_ffi_error >> fs[]) >>
  drule_all do_app_SOME_ffi_same >> disch_then (qspec_then ‘f2’ assume_tac) >>
  qexists_tac ‘f2’ >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem dec_clock_ffi[simp]:
  dec_clock (s with ffi := f) = (dec_clock s) with ffi := f ∧
  (dec_clock s).ffi = s.ffi
Proof
  simp[dec_clock_def]
QED

Theorem do_eval_res_ffi:
  do_eval_res vs s = (s1, r) ⇒
  s1.ffi = s.ffi ∧ ∀f : 'b ffi_state. do_eval_res vs (s with ffi := f) = (s1 with ffi := f, r)
Proof
  rw[do_eval_res_def] >> every_case_tac >> gvs[]
QED

Theorem do_app_ffi_upto_imp:
  do_app (refs, f1) op vs = SOME ((refs', f1'), r) ⇒
  ∀L f2. ffi_rel_upto L f1 f2 ⇒ ext f1' r ≼ L ⇒
         ∃f2'. do_app (refs, f2) op vs = SOME ((refs', f2'), r) ∧ ffi_rel_upto L f1' f2'
Proof
  metis_tac[do_app_ffi_upto]
QED

Theorem ext_prefix:
  ext f2 r ≼ L ⇒
  ∀f1 r1. f1.io_events ≼ f2.io_events ∧ final_call r1 = [] ⇒ ext f1 r1 ≼ L
Proof
  rw[ext_def] >> irule IS_PREFIX_TRANS >>
  qexists_tac ‘calls_of f2.io_events ++ final_call r’ >> simp[] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘calls_of f2.io_events’ >>
  simp[calls_of_prefix]
QED


(* Add a ≼ c for every a ≼ b, b ≼ c among the assumptions (one round) *)
val prefix_tm = “isPREFIX : 'a list -> 'a list -> bool”;
fun is_pfx t = (let val (f, args) = strip_comb t
                in length args = 2 andalso same_const f prefix_tm end)
               handle HOL_ERR _ => false;
val trans_round : tactic = fn (asl, w) =>
  let val ps = List.filter is_pfx asl
      fun args t = let val (_, l) = strip_comb t in (hd l, hd (tl l)) end
      val news = List.concat (List.map (fn p1 =>
                   List.mapPartial (fn p2 =>
                     let val (a, b) = args p1 val (b', c) = args p2
                     in if aconv b b' andalso not (aconv a c) then
                          let val th = MATCH_MP IS_PREFIX_TRANS (CONJ (ASSUME p1) (ASSUME p2))
                          in if List.exists (aconv (concl th)) asl then NONE else SOME th end
                        else NONE
                     end handle HOL_ERR _ => NONE) ps) ps)
  in MAP_EVERY (fn th => assume_tac th) news (asl, w) end;

(* MAIN: evaluation runs identically against FFI states that answer the
   same to the calls of the run *)
Theorem evaluate_ffi_upto:
  (∀(s:'a semanticPrimitives$state) env e s' r.
     evaluate s env e = (s',r) ⇒
     ∀L (f2 : 'b ffi_state). ffi_rel_upto L s.ffi f2 ⇒ ext s'.ffi r ≼ L ⇒
       ∃f2'. evaluate (s with ffi := f2) env e = (s' with ffi := f2', r) ∧
             ffi_rel_upto L s'.ffi f2') ∧
  (∀(s:'a semanticPrimitives$state) env v pes errv s' r.
     evaluate_match s env v pes errv = (s',r) ⇒
     ∀L (f2 : 'b ffi_state). ffi_rel_upto L s.ffi f2 ⇒ ext s'.ffi r ≼ L ⇒
       ∃f2'. evaluate_match (s with ffi := f2) env v pes errv = (s' with ffi := f2', r) ∧
             ffi_rel_upto L s'.ffi f2') ∧
  (∀(s:'a semanticPrimitives$state) env ds s' r.
     evaluate_decs s env ds = (s',r) ⇒
     ∀L (f2 : 'b ffi_state). ffi_rel_upto L s.ffi f2 ⇒ ext s'.ffi r ≼ L ⇒
       ∃f2'. evaluate_decs (s with ffi := f2) env ds = (s' with ffi := f2', r) ∧
             ffi_rel_upto L s'.ffi f2')
Proof
  ho_match_mp_tac full_evaluate_ind >> rpt strip_tac >>
  gvs[full_evaluate_def, AllCaseEqs(), PULL_EXISTS] >>
  imp_res_tac evaluate_io_events_mono_imp >>
  imp_res_tac do_app_io_events_mono >>
  gvs[io_events_mono_def] >>
  trans_round >> trans_round >>
  ntac 4 (
    rpt (first_x_assum (drule_then strip_assume_tac) ORELSE
         qpat_x_assum ‘do_app _ _ _ = NONE’
           (assume_tac o GEN_ALL o MATCH_MP do_app_NONE_ffi) ORELSE
         qpat_x_assum ‘do_app _ _ _ = SOME _’
           (fn th => drule_then strip_assume_tac (MATCH_MP do_app_ffi_upto_imp th)) ORELSE
         qpat_x_assum ‘do_eval_res _ _ = _’
           (strip_assume_tac o MATCH_MP do_eval_res_ffi) ORELSE
         qpat_x_assum ‘ext _ _ ≼ L ⇒ _’
           (fn th => mp_tac th >>
                     impl_tac >- FIRST [
                       first_assum ACCEPT_TAC,
                       qpat_assum ‘ext _ _ ≼ L’ (fn th => irule (MATCH_MP ext_prefix th)) >>
                       simp[] >> FIRST [first_assum ACCEPT_TAC, simp[]],
                       fs[ext_def, final_call_def] >> NO_TAC] >>
                     strip_tac)) >>
    gvs[]) >>
  rpt (qpat_x_assum ‘ext _ _ ≼ L ⇒ _’
         (fn th => mp_tac th >> impl_tac >- (fs[ext_def, final_call_def] >> NO_TAC) >>
                   strip_tac)) >>
  gvs[] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   Whole programs
   ------------------------------------------------------------------------ *)

(* f1 and f2 answer the same to every prefix of L *)
Definition agree_upto_def:
  agree_upto L (f1 : 'a ffi_state) (f2 : 'b ffi_state) ⇔
    ∀cs. cs ≼ L ⇒ ffi_answers f1 cs = ffi_answers f2 cs
End

(* The calls of the run with clock k *)
Overload clock_calls = “λst env prog k.
  ext (FST (evaluate_prog_with_clock st env k prog))
      (SND (evaluate_prog_with_clock st env k prog))”

Theorem evaluate_prog_with_clock_upto:
  st.ffi.io_events = [] ∧ f2.io_events = [] ∧
  agree_upto (clock_calls st env prog k) st.ffi f2 ⇒
  ∃f2'. evaluate_prog_with_clock (st with ffi := f2) env k prog =
          (f2', SND (evaluate_prog_with_clock st env k prog)) ∧
        f2'.io_events = (FST (evaluate_prog_with_clock st env k prog)).io_events
Proof
  rw[evaluate_prog_with_clock_def] >>
  Cases_on ‘evaluate_decs (st with clock := k) env prog’ >> gvs[] >>
  rename1 ‘evaluate_decs _ _ _ = (s', r)’ >>
  drule (CONJUNCT2 (CONJUNCT2 evaluate_ffi_upto)) >>
  disch_then (qspecl_then [‘ext s'.ffi r’, ‘f2’] mp_tac) >>
  impl_tac >- gvs[ffi_rel_upto_def, agree_upto_def, calls_of_def] >>
  simp[] >> strip_tac >>
  ‘st with <|ffi := f2; clock := k|> = (st with clock := k) with ffi := f2’
    by simp[semanticPrimitivesTheory.state_component_equality] >>
  simp[] >> fs[ffi_rel_upto_def]
QED

(* MAIN: a program behaves the same against an FFI state that answers the
   same to the calls of each of its clocked runs *)
Theorem semantics_prog_upto:
  st.ffi.io_events = [] ∧ f2.io_events = [] ∧
  (∀k. agree_upto (clock_calls st env prog k) st.ffi f2) ∧
  semantics_prog st env prog b ⇒
  semantics_prog (st with ffi := f2) env prog b
Proof
  strip_tac >>
  ‘∀k. (FST (evaluate_prog_with_clock (st with ffi := f2) env k prog)).io_events =
       (FST (evaluate_prog_with_clock st env k prog)).io_events ∧
       SND (evaluate_prog_with_clock (st with ffi := f2) env k prog) =
       SND (evaluate_prog_with_clock st env k prog)’
    by (gen_tac >>
        qspecl_then [‘st’, ‘f2’, ‘env’, ‘prog’, ‘k’] mp_tac
          (Q.GENL [‘st’, ‘f2’, ‘env’, ‘prog’, ‘k’] evaluate_prog_with_clock_upto) >>
        simp[] >> strip_tac >> simp[]) >>
  Cases_on ‘b’ >> fs[semanticsTheory.semantics_prog_def]
  >~ [‘lprefix_lub _ _’]
  >- (rpt conj_tac
      >- (gen_tac >>
          qpat_x_assum ‘∀k. (FST _).io_events = _ ∧ _’ (qspec_then ‘k’ mp_tac) >>
          qpat_x_assum ‘∀k. ∃ffi. _’ (qspec_then ‘k’ strip_assume_tac) >>
          Cases_on ‘evaluate_prog_with_clock (st with ffi := f2) env k prog’ >> simp[]) >>
      TRY (‘(λk. fromList (FST (evaluate_prog_with_clock (st with ffi := f2) env k prog)).io_events) =
       (λk. fromList (FST (evaluate_prog_with_clock st env k prog)).io_events)’
        by simp[FUN_EQ_THM] >>
      simp[]))
  >> TRY (qexists_tac ‘k’) >>
  qpat_x_assum ‘∀k. (FST _).io_events = _ ∧ _’ (qspec_then ‘k’ mp_tac) >>
  Cases_on ‘evaluate_prog_with_clock (st with ffi := f2) env k prog’ >> gvs[]
QED
