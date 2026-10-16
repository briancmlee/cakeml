(*
  The bodies HTTP server's liveness, re-derived from the library
  (design/34 §2.6): the server only proves its per-handler obligation
  handler_live, and server_with_live (asyncServerWithLive) does the rest.

   - handler_live_http_b: the bridge.  The handler's machine-level theorem
     hmachine_live_p (asyncHttpDrainB) has the four environment facts as
     hypotheses about the machine's states; henv states them on the
     transcript.  hmachine_reading (state HB: an outstanding read),
     hmachine_eof (state HD, not invalid: a read returned EOF) and
     Rj_Wj_SUC (state HA: no read this round) translate one into the other.
   - http_live_b_rounds_via_lib: HttpSpecBodies' liveness for the loop's
     trace, the same statement as asyncHttpLiveB's http_live_b_rounds,
     now from server_with_live.
*)
Theory asyncHttpLiveBLib
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words string
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec HttpSpec
  HttpSpecHeaders HttpSpecBodies asyncHttpParseB asyncM4GRounds asyncM4GTrans
  asyncM4ReadSoon asyncM4Drain asyncRunOkGen asyncServerWith asyncSWProgress
  asyncSWSock asyncHttpServerB asyncHttpParseBExt asyncHttpMachineB
  asyncHttpDrainB asyncHttpLiveB asyncServerWithLive
Libs
  preamble

(* The handler's round bound: hmachine_live_p's *)
Definition http_b_bound_def:
  http_b_bound D = (LENGTH D + 2) * (LENGTH (parse_all_b D) + 3)
End

(* MAIN: the bodies HTTP handler meets the library's per-handler
   obligation: in every environment henv, it writes the responses to the
   complete requests in D *)
Theorem handler_live_http_b:
  handler_live (λfd. http_handler_b files (fd, "")) (responses_to_b files) http_b_bound
Proof
  simp[handler_live_def, http_b_bound_def] >> rpt gen_tac >> strip_tac >>
  rename1 ‘henv _ _ _ _ DD’ >>
  ‘http_handler_b files (fd, "") = hcomp files fd (HA "")’ by simp[hcomp_def] >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum ‘henv _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [henv_def, hread_def]) >>
  mp_tac (Q.INST [‘D’ |-> ‘DD’] hmachine_live_p) >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (rpt strip_tac >> first_x_assum irule >> simp[])
      (* waiting while not readable: nothing unread, and no read this round *)
      >- (rpt strip_tac >>
          ‘Rj files fd g (SUC j) = Rj files fd g j’
            by (drule_all Rj_Wj_SUC >> simp[]) >>
          pop_assum (SUBST1_TAC o SYM) >>
          qpat_x_assum ‘∀j. _ ∧ _ ∧ Readable fd ∉ _ ⇒ _’ irule >> simp[])
      (* reading: the read is outstanding in the transcript *)
      >- (rpt strip_tac >>
          ‘j ≤ LENGTH g’ by simp[] >>
          drule_all hmachine_reading >> strip_tac >>
          qpat_x_assum ‘∀j. _ ∧ _ ∧ MEM (Read fd, NONE) _ ∧ _ ⇒ _’ irule >> simp[])
      (* stopped on an incomplete buffer: end-of-file was read *)
      >> rpt strip_tac >>
      ‘parse_brequest b ≠ BInvalid’ by simp[] >>
      drule_all hmachine_eof >> strip_tac >>
      qpat_x_assum ‘∀j. _ ∧ _ ∧ MEM (Read fd, SOME Eof) _ ⇒ _’ irule >> simp[]) >>
  disch_then (qspecl_then [‘LENGTH DD’, ‘j0’] mp_tac) >>
  simp[]
QED

Theorem responses_to_b_NIL[local]:
  FLAT (responses_to_b files "") = ""
Proof
  simp[Once parse_all_b_def] >> EVAL_TAC
QED

(* MAIN: HttpSpecBodies' liveness for the event loop's trace, from the
   library theorem server_with_live: the same statement as
   http_live_b_rounds (asyncHttpLiveB) *)
Theorem http_live_b_rounds_via_lib:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  http_live_b files s0
    (LFLATTEN (LGENLIST (λi. fromList (HEV files lfdn s0 i)) NONE))
Proof
  rw[http_live_b_def] >>
  qexists_tac ‘FLAT (GENLIST (HEV files lfdn s0) (@N.
     bytes (FLAT (responses_to_b files (FLAT (MAP print_brequest rs)))) ≼
     bytes_written_to c (FLAT (GENLIST (HEV files lfdn s0) N))))’ >>
  simp[rounds_LPREFIX] >>
  SELECT_ELIM_TAC >> conj_tac
  >- (mp_tac (Q.GEN ‘hf’ server_with_live
              |> Q.ISPEC ‘λfd. http_handler_b files (fd, "")’
              |> Q.INST [‘out’ |-> ‘responses_to_b files’, ‘B’ |-> ‘http_b_bound’,
                         ‘D’ |-> ‘FLAT (MAP print_brequest rs)’]) >>
      simp[GSYM http_server_b_def, hok_http_b, handler_live_http_b, responses_to_b_NIL] >>
      disch_then irule >> fs[brequests_def]) >>
  rpt strip_tac >>
  ‘parse_all_b (FLAT (MAP print_brequest rs)) = rs’
    by (irule parse_all_b_printed >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘bytes _ ≼ bytes_written_to _ _’ mp_tac >>
  asm_rewrite_tac[bresponses_def]
QED
