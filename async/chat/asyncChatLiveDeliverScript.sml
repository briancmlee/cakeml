(*
  Delivery for the chat server (ChatSpec's third liveness clause).

  Part 1 (here): the chat handler is a live push handler in the library's
  sense (handler_push_live, asyncServerVPushLive), with B = 0: whatever
  lines the hub has told the writer, the writer has already written
  (cout_written).  A Fetch answered in round r is written in round r + 1,
  and the write is in the transcript as soon as it is emitted.
*)
Theory asyncChatLiveDeliver
Ancestors
  pair list rich_list arithmetic option string
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncServerV asyncServerVLive asyncServerVLiveA asyncServerVPushLive
  asyncWithStore asyncWithTap asyncChatSW asyncChatModel asyncChatSafe
  asyncChatLiveV
Libs
  BasicProvers

(* The lines a handler was told, one per non-empty Lines answer *)
Definition cout_def:
  cout (ans : canswer option list) =
    FILTER (λs. s ≠ "") (MAP (λa. case a of SOME (Lines s) => s | _ => "") ans)
End

Theorem cout_simps[simp]:
  cout [] = [] ∧
  cout (a ++ b) = cout a ++ cout b ∧
  cout (SOME (Lines s) :: t) = (if s = "" then cout t else s :: cout t) ∧
  cout (SOME (Pos j) :: t) = cout t ∧
  cout (SOME NotJoined :: t) = cout t ∧
  cout (NONE :: t) = cout t
Proof
  rw[cout_def, FILTER_APPEND]
QED

Theorem kanswers_CONS[local]:
  kanswers chatV ((Kv q, SOME (KvR b)) :: tr) = SOME b :: kanswers chatV tr ∧
  kanswers chatV ((Kv q, NONE) :: tr) = kanswers chatV tr ∧
  kanswers chatV ((Kv q, SOME (SockR y)) :: tr) = NONE :: kanswers chatV tr ∧
  kanswers chatV ((Sock x, r) :: tr) = kanswers chatV tr ∧
  kanswers chatV [] = []
Proof
  rw[kanswers_def, chatV_def] >> Cases_on ‘r’ >> simp[]
QED

Theorem trans_emit_running[local]:
  (∀n. n ≤ LENGTH h ⇒ (emit a (TAKE n h)).result = NONE) ⇒
  trans (emit a) h = [(a, NONE)]
Proof
  rw[trans_emit] >> Cases_on ‘h’ >> gvs[] >>
  first_x_assum (qspec_then ‘1’ mp_tac) >> simp[emit_def] >>
  rename1 ‘oHD s.results’ >> Cases_on ‘s.results’ >> simp[]
QED

Theorem written_untag_CONS[local]:
  written fd (untag ((Kv q, r) :: tr)) = written fd (untag tr) ∧
  written fd (untag ((Sock (Write fd s), r) :: tr)) = s :: written fd (untag tr) ∧
  written fd (untag []) = []
Proof
  simp[untag_def, written_def]
QED

(* The write loop has written every line it was told *)
Theorem wloop_cout:
  ∀hh i. cout (kanswers chatV (trans (wloop (fd, i)) hh)) ≼
         written fd (untag (trans (wloop (fd, i)) hh))
Proof
  gen_tac >> measureInduct_on ‘LENGTH hh’ >> gen_tac >>
  ONCE_REWRITE_TAC[wloop_unfold] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Fetch i))) K0) hh’ >>
  qspecl_then [‘emit (Kv (fd, Fetch i))’, ‘K0’, ‘hh’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (ASM_REWRITE_TAC[] >> drule trans_emit_running >>
      simp[kanswers_CONS, written_untag_CONS]) >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
  rename1 ‘oHD s.results = SOME res’ >>
  Cases_on ‘res’ >> simp[kanswers_CONS, written_untag_CONS, Abbr ‘K0’] >>
  Cases_on ‘b’ >> simp[kanswers_CONS, written_untag_CONS] >>
  rename1 ‘Lines ln’ >> Cases_on ‘ln = ""’ >> simp[] >>
  TRY (first_x_assum irule >> simp[] >> NO_TAC) >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit WR) K1) h2’ >>
  qspecl_then [‘emit WR’, ‘K1’, ‘h2’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (ASM_REWRITE_TAC[] >> drule trans_emit_running >>
      simp[Abbr ‘WR’, kanswers_CONS, written_untag_CONS]) >>
  drule first_done_emit >> strip_tac >>
  gvs[trans_emit, Abbr ‘K1’, Abbr ‘WR’, kanswers_CONS, written_untag_CONS] >>
  first_x_assum irule >> Cases_on ‘h1’ >> Cases_on ‘h1'’ >> gvs[]
QED

(* (the first answer is the Start query's: it is not lines) *)
Theorem writer_cout:
  cout (DROP 1 (kanswers chatV (trans (writer fd) hh))) ≼
  written fd (untag (trans (writer fd) hh))
Proof
  simp[writer_def] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Start))) K0) hh’ >>
  qspecl_then [‘emit (Kv (fd, Start))’, ‘K0’, ‘hh’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (ASM_REWRITE_TAC[] >> drule trans_emit_running >>
      simp[kanswers_CONS, written_untag_CONS]) >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
  rename1 ‘oHD s.results = SOME res’ >>
  Cases_on ‘res’ >> simp[kanswers_CONS, written_untag_CONS, Abbr ‘K0’] >>
  Cases_on ‘b’ >> simp[kanswers_CONS, written_untag_CONS, wloop_cout]
QED

(* The reader's entries count neither as answers nor as writes *)
Theorem kanswers_FILTER_wq[local]:
  ∀tr. EVERY (on_fdc fd) tr ⇒ kanswers chatV (FILTER (wq fd) tr) = kanswers chatV tr
Proof
  Induct >> simp[kanswers_CONS] >> PairCases >> Cases_on ‘h0’ >>
  rw[wq_def, on_fdc_def] >> gvs[kanswers_def, chatV_def] >>
  TRY (Cases_on ‘h1’) >> gvs[] >> metis_tac[PAIR]
QED

Theorem written_FILTER_wq[local]:
  ∀tr. written fd (untag (FILTER (wq fd) tr)) = written fd (untag tr)
Proof
  Induct >> simp[written_untag_CONS] >> PairCases >> Cases_on ‘h0’ >>
  TRY (rename1 ‘Sock a’ >> Cases_on ‘a’) >>
  rw[wq_def] >> gvs[untag_def, written_def] >>
  TRY (PairCases_on ‘q’) >> gvs[]
QED

(* MAIN: the chat handler has written every line the hub told it (after
   the answer to its first query, Start) *)
Theorem chat_handler_cout:
  cout (DROP 1 (kanswers chatV (trans (chat_handler fd) L))) ≼
  written fd (untag (trans (chat_handler fd) L))
Proof
  qspecl_then [‘fd’, ‘L’] assume_tac chat_handler_on_fdc >>
  ONCE_REWRITE_TAC[GSYM written_FILTER_wq] >>
  drule kanswers_FILTER_wq >> disch_then (SUBST1_TAC o SYM) >>
  qspecl_then [‘fd’, ‘L’] strip_assume_tac (Q.GENL [‘fd’, ‘L’] chat_handler_writer) >>
  simp[writer_cout]
QED

(* MAIN: the chat handler is a live push handler, with no delay *)
Theorem handler_push_live_chat:
  handler_push_live chatV chat_handler (λans. cout (DROP 1 ans)) 0
Proof
  rw[handler_push_live_def] >> qexists_tac ‘j0’ >> simp[GSYM untag_sproj] >>
  simp[chat_handler_cout]
QED
