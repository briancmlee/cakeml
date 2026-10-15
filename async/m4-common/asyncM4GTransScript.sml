(*
  The three views of a run against the socket world, related (shared by
  echo_safe and echo_live):

   1. the model's transcript of m on the history the world generates
      (asyncTranscript's trans m (ghist ...));
   2. the performed (action, response) pairs, gperf;
   3. the raw I/O events of the loop's trace (grounds_events), as EchoSpec
      projects them per connection (bytes_written_to / bytes_read_from).

  trans_ghist:  1 = 2 with SOME responses, plus the current round's actions
                (their responses have not arrived yet);
  bytes_written_to_rounds / bytes_read_from_rounds:  3 = 2, projected;
  rounds_LPREFIX / LPREFIX_rounds_between:  every finite prefix of the
                loop's infinite trace lies between two round boundaries.

  Everything holds for any interest function ifds and any computation m,
  given that no action of the run is a misuse (grun_ok).
*)
Theory asyncM4GTrans
Ancestors
  asyncCore asyncLevel1 asyncLevel2 asyncChoose asyncCfActModel
  asyncTranscript ffiSpikeSocketFFI ffi llist Marshalling asyncM3World
  asyncM4GRounds asyncM4SockInv EchoSpec
Libs
  preamble

(* The responses of round n *)
Definition gres_def:
  gres ifds m s0 n = FST (sock_acts_tot (gstate ifds m s0 n) (gacts ifds m s0 n))
End

(* The performed (action, response) pairs of the first n rounds *)
Definition gperf_def:
  gperf ifds m s0 n =
    FLAT (GENLIST (λi. ZIP (gacts ifds m s0 i, gres ifds m s0 i)) n)
End

Theorem gperf_SUC:
  gperf ifds m s0 (SUC n) =
  gperf ifds m s0 n ++ ZIP (gacts ifds m s0 n, gres ifds m s0 n)
Proof
  simp[gperf_def, GENLIST, SNOC_APPEND]
QED

Theorem grun_ok_sock_acts:
  grun_ok ifds m s0 ⇒
  ∃evs s'. sock_acts (gstate ifds m s0 n) (gacts ifds m s0 n) =
           SOME (gres ifds m s0 n, evs, s')
Proof
  rw[grun_ok_def, gres_def, sock_acts_tot_def] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >>
  Cases_on ‘sock_acts (gstate ifds m s0 n) (gacts ifds m s0 n)’ >> simp[] >>
  PairCases_on ‘x’ >> simp[]
QED

Theorem LENGTH_gres:
  grun_ok ifds m s0 ⇒ LENGTH (gres ifds m s0 n) = LENGTH (gacts ifds m s0 n)
Proof
  strip_tac >> drule grun_ok_sock_acts >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >>
  imp_res_tac sock_acts_events >> simp[]
QED

(* ------------------------------------------------------------------------
   1 = 2: the model's transcript
   ------------------------------------------------------------------------ *)

Theorem results_EL_ghist:
  i < n ⇒ (EL i (ghist ifds m s0 n)).results = gres ifds m s0 i
Proof
  strip_tac >>
  ‘EL i (ghist ifds m s0 n) = EL i (ghist ifds m s0 (SUC i))’
    by (‘SUC i ≤ n’ by simp[] >>
        drule_then (qspecl_then [‘s0’, ‘m’, ‘ifds’] (SUBST1_TAC o SYM))
          (Q.GENL [‘ifds’, ‘m’, ‘s0’] ghist_TAKE |> SPEC_ALL |>
           Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘k’] |>
           Q.SPECL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘SUC i’]) >>
        simp[EL_TAKE]) >>
  simp[Once ghist_def, grounds_SUC, EL_APPEND2, ssnap_def, gres_def]
QED

Theorem zipr_ZIP:
  ∀as rs. LENGTH rs = LENGTH as ⇒
          zipr as rs = MAP (λ(a, r). (a, SOME r)) (ZIP (as, rs))
Proof
  Induct >> simp[zipr_def] >> Cases_on ‘rs’ >> simp[zipr_def]
QED

Theorem zipr_NIL:
  ∀as. zipr as [] = MAP (λa. (a, NONE)) as
Proof
  Induct >> simp[zipr_def]
QED

(* MAIN: the model's transcript on the history the socket world generates
   is the performed pairs of the first n rounds (with their responses),
   followed by round n's actions (whose responses have not arrived yet) *)
Theorem trans_ghist:
  grun_ok ifds m s0 ⇒
  trans m (ghist ifds m s0 n) =
    MAP (λ(a, r). (a, SOME r)) (gperf ifds m s0 n) ++
    MAP (λa. (a, NONE)) (gacts ifds m s0 n)
Proof
  strip_tac >>
  ‘FLAT (GENLIST (round_trans m (ghist ifds m s0 n)) n) =
   MAP (λ(a, r). (a, SOME r)) (gperf ifds m s0 n)’
    by (simp[gperf_def, MAP_FLAT, MAP_GENLIST, combinTheory.o_DEF] >>
        AP_TERM_TAC >> simp[GENLIST_FUN_EQ] >> rpt strip_tac >>
        simp[round_trans_def, ghist_TAKE, responses_at_def, results_EL_ghist,
             GSYM gacts_def] >>
        irule zipr_ZIP >> simp[LENGTH_gres]) >>
  ‘round_trans m (ghist ifds m s0 n) n = MAP (λa. (a, NONE)) (gacts ifds m s0 n)’
    by simp[round_trans_def, responses_at_def, GSYM gacts_def, zipr_NIL,
            TAKE_LENGTH_ID_rwt] >>
  simp[trans_def, GENLIST, SNOC_APPEND]
QED

(* ------------------------------------------------------------------------
   3 = 2: the raw events, projected per connection
   ------------------------------------------------------------------------ *)

(* The bytes a performed pair wrote to / read from connection c *)
Definition pwritten_def:
  pwritten c (Write c' bs, r : sresp) = (if c' = c then bs else []) ∧
  pwritten c _ = []
End

Definition pread_def:
  pread c (Read c' n, Got (SOME d)) = (if c' = c then d else []) ∧
  pread c _ = []
End

Theorem MAP_SND_ZIP_LENGTH[local]:
  LENGTH xs = LENGTH ys ⇒ MAP SND (ZIP (xs, ys)) = ys
Proof
  simp[MAP_ZIP]
QED

Theorem event_written_act_event:
  sock_do s a = SOME (r, s') ⇒ event_written c (act_event a r) = pwritten c (a, r)
Proof
  Cases_on ‘a’ >>
  rw[sock_do_def, OPTION_MAP_EQ_SOME, pairTheory.EXISTS_PROD] >>
  gvs[act_event_def, event_written_def, pwritten_def]
  >> rename1 ‘fd_bytes cc ++ l’ >>
  ‘TAKE 8 (fd_bytes cc ++ l) = fd_bytes cc ∧ DROP 8 (fd_bytes cc ++ l) = l’
    by (‘LENGTH (fd_bytes cc) = 8’ by simp[] >>
        metis_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]) >>
  simp[]
QED

(* How EchoSpec's event_read decodes M3's read buffer *)
Theorem sread_out_decode[local]:
  d ≠ [] ∧ LENGTH d ≤ n ∧ n < 256 ** 8 ⇒
  HD (sread_out n (SOME d)) = 0w ∧
  9 ≤ LENGTH (sread_out n (SOME d)) ∧
  TAKE (w82n (TAKE 8 (TL (sread_out n (SOME d)))))
       (DROP 9 (sread_out n (SOME d))) = d
Proof
  strip_tac >> simp[sread_out_def, LENGTH_n2w8] >>
  ‘LENGTH (n2w8 (LENGTH d)) = 8’ by simp[LENGTH_n2w8] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  ‘TAKE 8 (n2w8 (LENGTH d) ++ (d ++ REPLICATE (n − LENGTH d) 0w)) =
   n2w8 (LENGTH d) ∧
   DROP 8 (n2w8 (LENGTH d) ++ (d ++ REPLICATE (n − LENGTH d) 0w)) =
   d ++ REPLICATE (n − LENGTH d) 0w’
    by metis_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
  ‘LENGTH d < 256 ** 8’ by metis_tac[LESS_EQ_LESS_TRANS] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> asm_rewrite_tac[] >>
  gs[w82n_n2w8, TAKE_LENGTH_APPEND]
QED

Theorem event_read_act_event:
  sock_do s a = SOME (r, s') ⇒ event_read c (act_event a r) = pread c (a, r)
Proof
  Cases_on ‘a’ >>
  rw[sock_do_def, OPTION_MAP_EQ_SOME, pairTheory.EXISTS_PROD] >>
  gvs[act_event_def, event_read_def, pread_def] >>
  rename1 ‘sock_read cc nn s = SOME (rr, _)’ >>
  ‘∀d. rr = SOME d ⇒ LENGTH d ≤ nn’ by (rw[] >> imp_res_tac sock_read_LENGTH) >>
  ‘LENGTH (sread_out nn rr) = nn + 9’ by simp[LENGTH_sread_out] >>
  simp[MAP_SND_ZIP_LENGTH] >>
  Cases_on ‘rr’ >- simp[sread_out_def, pread_def] >>
  rename1 ‘SOME d’ >> Cases_on ‘d = []’ >- simp[sread_out_def, pread_def] >>
  ‘LENGTH d ≤ nn ∧ nn < 256 ** 8’
    by (‘(256:num) ** 8 = 18446744073709551616’ by EVAL_TAC >> fs[]) >>
  drule_all sread_out_decode >> simp[pread_def]
QED

Theorem event_projections_spoll_event[simp]:
  event_written c (spoll_event fds s) = [] ∧
  event_read c (spoll_event fds s) = []
Proof
  simp[spoll_event_def, event_written_def, event_read_def]
QED

(* The events of a successful round, projected *)
Theorem round_projections:
  sock_acts s acts = SOME (rs, evs, s') ⇒
  MAP (event_written c) evs = MAP (pwritten c) (ZIP (acts, rs)) ∧
  MAP (event_read c) evs = MAP (pread c) (ZIP (acts, rs))
Proof
  strip_tac >> imp_res_tac sock_acts_events >>
  drule sock_acts_responses >> strip_tac >> gvs[] >>
  simp[LIST_EQ_REWRITE, EL_MAP, EL_MAP2, EL_ZIP] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[event_written_act_event, event_read_act_event]
QED

(* MAIN: what EchoSpec's projections see in the first n rounds of the
   loop's trace: exactly the bytes of the performed writes to / reads
   from c *)
Theorem bytes_written_to_rounds:
  grun_ok ifds m s0 ⇒
  bytes_written_to c (FLAT (GENLIST (grounds_events ifds m s0) n)) =
  FLAT (MAP (pwritten c) (gperf ifds m s0 n))
Proof
  strip_tac >> Induct_on ‘n’ >- simp[bytes_written_to_def, gperf_def] >>
  simp[GENLIST, SNOC_APPEND, gperf_SUC] >>
  gvs[bytes_written_to_def, MAP_APPEND, FLAT_APPEND] >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule round_projections >> strip_tac >>
  gvs[grounds_events_alt, sock_acts_tot_def]
QED

Theorem bytes_read_from_rounds:
  grun_ok ifds m s0 ⇒
  bytes_read_from c (FLAT (GENLIST (grounds_events ifds m s0) n)) =
  FLAT (MAP (pread c) (gperf ifds m s0 n))
Proof
  strip_tac >> Induct_on ‘n’ >- simp[bytes_read_from_def, gperf_def] >>
  simp[GENLIST, SNOC_APPEND, gperf_SUC] >>
  gvs[bytes_read_from_def, MAP_APPEND, FLAT_APPEND] >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule round_projections >> strip_tac >>
  gvs[grounds_events_alt, sock_acts_tot_def]
QED

Theorem bytes_written_to_mono:
  l1 ≼ l2 ⇒ bytes_written_to c l1 ≼ bytes_written_to c l2
Proof
  rw[IS_PREFIX_APPEND, bytes_written_to_def] >> simp[]
QED

Theorem bytes_read_from_mono:
  l1 ≼ l2 ⇒ bytes_read_from c l1 ≼ bytes_read_from c l2
Proof
  rw[IS_PREFIX_APPEND, bytes_read_from_def] >> simp[]
QED

(* ------------------------------------------------------------------------
   Finite prefixes of the loop's trace
   ------------------------------------------------------------------------ *)

Theorem LFLATTEN_fromList_GENLIST[local]:
  ∀n. LFLATTEN (fromList (GENLIST (λi. fromList (f i)) n)) =
      fromList (FLAT (GENLIST f n))
Proof
  Induct >> simp[GENLIST, SNOC_APPEND, GSYM LAPPEND_fromList,
                 LFLATTEN_APPEND_FINITE1] >>
  simp[LAPPEND_fromList, FLAT_APPEND, LAPPEND_NIL_2ND]
QED

Theorem LFLATTEN_LGENLIST_chunk:
  LFLATTEN (LGENLIST (λi. fromList (f i)) NONE) =
  LAPPEND (fromList (FLAT (GENLIST f n)))
          (LFLATTEN (LGENLIST (λi. fromList (f (n + i))) NONE))
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV
    [Q.SPEC ‘n’ (Q.GEN ‘n’ LGENLIST_CHUNK_GENLIST)])) >>
  simp[LFLATTEN_APPEND_FINITE1] >>
  simp[LFLATTEN_fromList_GENLIST, combinTheory.o_DEF] >>
  AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

(* MAIN (d): every round boundary is a prefix of the trace *)
Theorem rounds_LPREFIX:
  LPREFIX (fromList (FLAT (GENLIST f n)))
          (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE))
Proof
  ONCE_REWRITE_TAC[LFLATTEN_LGENLIST_chunk] >> simp[LPREFIX_APPEND] >>
  metis_tac[]
QED

Theorem LPREFIX_LTAKE[local]:
  LPREFIX (fromList l) ll ⇒ LTAKE (LENGTH l) ll = SOME l
Proof
  rw[LPREFIX_APPEND] >>
  qspecl_then [‘ll'’, ‘l’, ‘0’] mp_tac LTAKE_LAPPEND_fromList >> simp[]
QED

(* Two finite prefixes of the same lazy list are comparable *)
Theorem LPREFIX_comparable:
  LPREFIX (fromList a) ll ∧ LPREFIX (fromList b) ll ∧ LENGTH a ≤ LENGTH b ⇒
  a ≼ b
Proof
  rw[] >> imp_res_tac LPREFIX_LTAKE >>
  drule_all LTAKE_TAKE_LESS >> rw[] >> gvs[] >>
  ‘a = TAKE (LENGTH a) b’ by gvs[] >> pop_assum SUBST1_TAC >>
  simp[IS_PREFIX_APPEND] >> qexists_tac ‘DROP (LENGTH a) b’ >> simp[]
QED

(* MAIN (for echo_safe): if every round has at least one event, every
   finite prefix of the loop's trace lies between the end of some round
   n and the end of round n + 1 *)
Theorem LPREFIX_rounds_between:
  (∀i. f i ≠ []) ∧
  LPREFIX (fromList evs) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE)) ⇒
  ∃n. FLAT (GENLIST f n) ≼ evs ∧ evs ≼ FLAT (GENLIST f (SUC n))
Proof
  strip_tac >>
  ‘∀n. n ≤ LENGTH (FLAT (GENLIST f n))’
    by (Induct >> simp[GENLIST, SNOC_APPEND] >>
        first_x_assum (qspec_then ‘n’ mp_tac) >> Cases_on ‘f n’ >> simp[]) >>
  (* the last round boundary inside evs *)
  ‘∃n. FLAT (GENLIST f n) ≼ evs ∧ ¬(FLAT (GENLIST f (SUC n)) ≼ evs)’
    by (CCONTR_TAC >> fs[] >>
        ‘∀n. FLAT (GENLIST f n) ≼ evs’ by (Induct >> simp[] >> metis_tac[]) >>
        pop_assum (qspec_then ‘SUC (LENGTH evs)’ assume_tac) >>
        qpat_x_assum ‘∀n. n ≤ _’ (qspec_then ‘SUC (LENGTH evs)’ assume_tac) >>
        imp_res_tac IS_PREFIX_LENGTH >> fs[]) >>
  qexists_tac ‘n’ >> simp[] >>
  Cases_on ‘LENGTH evs ≤ LENGTH (FLAT (GENLIST f (SUC n)))’
  >- (irule LPREFIX_comparable >> metis_tac[rounds_LPREFIX])
  >> ‘FLAT (GENLIST f (SUC n)) ≼ evs’
       by (irule LPREFIX_comparable >> simp[] >> metis_tac[rounds_LPREFIX]) >>
  gvs[]
QED
