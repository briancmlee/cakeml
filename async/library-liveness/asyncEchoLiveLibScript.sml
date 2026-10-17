(*
  The echo server's liveness, re-derived from the library (design/34
  §2.6): echo proves only its per-handler obligation, and
  server_with_live_flat (asyncServerWithLiveFlat) does the rest.

   - echo_reads: in every environment henv, the echo handler eventually
     reads all of D.  By a measure on what of D is unread: in each window
     of four rounds, either fd is not reported readable (then D has been
     read, henv), or end-of-file was read (then too), or the handler reads
     (handler_progress), and a read with D not all read reads something
     (henv).
   - handler_live_flat_echo: echo writes back what it reads
     (handler_echoes), so it owes D for D.
   - echo_live_via_lib: EchoSpec's liveness for the loop's trace, the same
     statement as asyncM4EchoLive's echo_live_rounds, now from the library.
*)
Theory asyncEchoLiveLib
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words string
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec HttpSpec
  asyncM4GRounds asyncM4GTrans asyncM4LiveProg asyncM4ReadSoon asyncM4Drain
  asyncRunOkGen asyncServerWith asyncSWProgress asyncSWSock
  asyncServerWithLive asyncServerWithLiveFlat
Libs
  preamble

Theorem hok_handler:
  hok handler
Proof
  simp[hok_def, wf_handler, settled_handler, handler_echoes]
QED

(* MAIN: in every environment henv, the echo handler eventually reads all
   of D.  m bounds what of D is still unread at round j. *)
Theorem echo_reads:
  ∀m j. prompt (handler fd) g ∧ henv fd (handler fd) g j0 D ∧ j0 ≤ j ∧
        LENGTH D ≤ LENGTH (hread fd (handler fd) g j) + m ∧
        j + 4 * (m + 1) ≤ LENGTH g ⇒
        ∃j'. j' ≤ LENGTH g ∧ D ≼ hread fd (handler fd) g j'
Proof
  completeInduct_on ‘m’ >> rpt strip_tac >>
  qpat_assum ‘henv _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [henv_def]) >>
  Cases_on ‘D ≼ hread fd (handler fd) g j’
  >- (qexists_tac ‘j’ >> simp[]) >>
  ‘j ≤ LENGTH g’ by fs[] >>
  ‘hread fd (handler fd) g j ≼ D’ by metis_tac[] >>
  ‘LENGTH (hread fd (handler fd) g j) < LENGTH D’
    by (CCONTR_TAC >> fs[NOT_LESS] >> imp_res_tac IS_PREFIX_LENGTH >>
        metis_tac[IS_PREFIX_LENGTH_ANTI, LESS_EQUAL_ANTISYM, IS_PREFIX_REFL]) >>
  ‘0 < m’ by simp[] >>
  (* fd not reported readable in the window: D has been read *)
  Cases_on ‘∃i. j ≤ i ∧ i < j + 3 ∧ Readable fd ∉ (EL i g).ready’
  >- (fs[] >> qexists_tac ‘SUC i’ >> simp[] >>
      qpat_x_assum ‘∀j. _ ∧ _ ∧ Readable fd ∉ _ ⇒ _’ irule >> simp[]) >>
  fs[] >>
  (* end-of-file read: D has been read *)
  Cases_on ‘MEM (Read fd, SOME Eof) (trans (handler fd) (TAKE (j + 3) g))’
  >- (qexists_tac ‘j + 3’ >> simp[] >>
      qpat_x_assum ‘∀j. _ ∧ _ ∧ MEM (Read fd, SOME Eof) _ ⇒ _’ irule >> simp[]) >>
  (* otherwise the handler reads in the window (handler_progress) *)
  ‘nreads fd (handler fd (TAKE j g)).actions <
   nreads fd (handler fd (TAKE (j + 3) g)).actions’
    by (qspecl_then [‘TAKE (j + 3) g’, ‘j’] mp_tac (Q.GEN ‘fd’ handler_progress |> Q.SPEC ‘fd’) >>
        impl_tac
        >- (simp[prompt_TAKE, LENGTH_TAKE] >> rpt strip_tac >>
            simp[EL_TAKE] >> qpat_x_assum ‘∀i. _ ∨ _ ∨ _’ (qspec_then ‘j'’ mp_tac) >> simp[]) >>
        simp[TAKE_TAKE]) >>
  qspecl_then [‘3’] mp_tac
    (Q.GENL [‘m’, ‘i’, ‘h’] nreads_step_wf |> Q.ISPEC ‘handler fd’ |> Q.SPECL [‘j’, ‘g’]) >>
  simp[wf_handler] >> strip_tac >>
  drule new_action_unanswered >> strip_tac >>
  ‘k < LENGTH g ∧ j0 ≤ k’ by simp[] >>
  Cases_on ‘D ≼ hread fd (handler fd) g k’
  >- (qexists_tac ‘k’ >> simp[]) >>
  qpat_x_assum ‘∀j. _ ∧ _ ∧ MEM (Read fd, NONE) _ ∧ _ ⇒ _’ (qspec_then ‘k’ mp_tac) >>
  simp[] >> strip_tac
  >- (qexists_tac ‘SUC k’ >> simp[]) >>
  (* it read something: by induction, with less of D unread *)
  ‘hread fd (handler fd) g j ≼ hread fd (handler fd) g k’ by simp[hread_mono] >>
  imp_res_tac IS_PREFIX_LENGTH >>
  qpat_x_assum ‘∀m'. m' < m ⇒ _’ (qspec_then ‘m − 1’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘SUC k’ mp_tac) >> simp[]
QED

(* MAIN: the echo handler meets the library's (flat) obligation: it owes
   D for D *)
Theorem handler_live_flat_echo:
  handler_live_flat handler (λD. [D]) (λD. 4 * (LENGTH D + 1))
Proof
  simp[handler_live_flat_def] >> rpt gen_tac >> strip_tac >>
  rename1 ‘henv _ _ _ _ DD’ >>
  qspecl_then [‘LENGTH DD’, ‘j0’] mp_tac (Q.INST [‘D’ |-> ‘DD’] echo_reads) >>
  simp[] >> strip_tac >> qexists_tac ‘j'’ >> simp[] >>
  ‘written fd (trans (handler fd) (TAKE j' g)) = read fd (trans (handler fd) (TAKE j' g))’
    by simp[handler_echoes] >>
  fs[hread_def]
QED

(* Strings and bytes: every byte list is the bytes of a string *)
Theorem bytes_of_bytes[local]:
  ∀l : word8 list. bytes (MAP (CHR o w2n) l) = l
Proof
  Induct >> simp[bytes_def] >> gen_tac >>
  ‘w2n h < 256’ by (assume_tac (INST_TYPE [alpha |-> “:8”] w2n_lt) >> fs[dimword_def]) >>
  simp[ORD_CHR_RWT, n2w_w2n] >> fs[bytes_def]
QED

(* MAIN: EchoSpec's liveness for the event loop's trace, from the library
   theorem: the same statement as echo_live_rounds (asyncM4EchoLive) *)
Theorem echo_live_via_lib:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  echo_live s0
    (LFLATTEN (LGENLIST (λi. fromList (grounds_events (EI lfdn) (EM lfdn) s0 i)) NONE))
Proof
  rw[echo_live_def] >>
  mp_tac (Q.GEN ‘hf’ server_with_live_flat |> Q.ISPEC ‘handler’
          |> Q.INST [‘out’ |-> ‘λD. [D]’, ‘B’ |-> ‘λD. 4 * (LENGTH D + 1)’,
                     ‘D’ |-> ‘MAP (CHR o w2n) (sent_upto c n s0)’]) >>
  simp[hok_handler, handler_live_flat_echo, bytes_of_bytes, server_with_handler] >>
  strip_tac >>
  qexists_tac ‘FLAT (GENLIST (grounds_events (EI lfdn) (EM lfdn) s0) N)’ >>
  simp[rounds_LPREFIX]
QED
