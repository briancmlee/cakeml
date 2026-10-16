(*
  Liveness for PUSH servers (pub/sub, chat), over the library's skeleton
  server_v and any wrapper (additive over library-liveness; written for the
  chat server, generic in V, Wr, hf).

  In a request/response server (handler_live_v, handler_live_va) the output
  owed on a connection is a function of the data its client sent.  In a
  push server it is a function of what the handler has been TOLD: the
  answers to its queries (for chat: the hub's lines), whatever the client
  sent.  The obligation:

     handler_push_live V hf out B: whatever the handler's answers are by
     round j0, out of them is written by some round, if the world answers
     promptly for B more rounds.

  MAIN: server_v_live_every.  For every connection c the server accepted,
  for EVERY round N0, out of c's actual answers by round N0 (conn_answers)
  is written to c by some round N.  No henv and no "nothing owed for no
  data" condition: the hypothesis is only that c was accepted.
*)
Theory asyncServerVPushLive
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words string
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress ffiSpikeSocketFFI EchoSpec HttpSpec
  asyncM3World asyncM4GRounds asyncM4Relabel asyncM4RelabelDist
  asyncM4SockModel asyncM4SockInv asyncM4GTrans asyncM4EchoRunOk
  asyncM4AcceptSoon asyncRunOkGen asyncM4ServerUses
  asyncServerV asyncServerVProgress asyncServerVLive asyncServerVLiveA
Libs
  preamble

(* MAIN (definition): a push handler is live if out of the answers it has
   received by round j0 is eventually written, given prompt answers *)
Definition handler_push_live_def:
  handler_push_live (V : ('act, 'k, 'q, 'res) vocab)
                    (hf : num -> ('act, 'res, 'z) vmach)
                    (out : 'k option list -> string list) B ⇔
    ∀fd g j0.
      prompt (hf fd) g ∧ j0 + B ≤ LENGTH g ⇒
      ∃j. j ≤ LENGTH g ∧
          out (kanswers V (trans (hf fd) (TAKE j0 g))) ≼
            written fd (sproj V (trans (hf fd) (TAKE j g)))
End

(* ------------------------------------------------------------------------
   Answers only grow
   ------------------------------------------------------------------------ *)

Theorem kanswers_APPEND:
  kanswers V (a ++ b) = kanswers V a ++ kanswers V b
Proof
  simp[kanswers_def]
QED

Theorem kanswers_FILTER_NONE[local]:
  ∀tr. EVERY (λp. SND p = NONE) tr ⇒ kanswers V (FILTER P tr) = []
Proof
  Induct >> simp[kanswers_def] >> PairCases >> rw[] >> gvs[kanswers_def]
QED

Theorem zipr_NIL_NONE[local]:
  ∀acts. EVERY (λp. SND p = NONE) (zipr acts [])
Proof
  Induct >> simp[zipr_def]
QED

(* The transcript after k rounds: the first k rounds of the full one, then
   round k's actions, unanswered *)
Theorem trans_TAKE_split:
  k ≤ LENGTH h ⇒
  trans m (TAKE k h) =
    FLAT (GENLIST (round_trans m h) k) ++
    zipr (new_actions (log_of m) (TAKE k h)) []
Proof
  rw[trans_def, GENLIST, SNOC_APPEND, LENGTH_TAKE] >>
  simp[round_trans_def, responses_at_def] >>
  ‘GENLIST (round_trans m (TAKE k h)) k = GENLIST (round_trans m h) k’
    suffices_by simp[TAKE_TAKE] >>
  simp[GENLIST_FUN_EQ, round_trans_def, responses_at_def] >>
  rw[TAKE_TAKE, EL_TAKE]
QED

Theorem kanswers_trans_TAKE:
  kanswers V (FILTER P (trans m (TAKE k h))) ≼ kanswers V (FILTER P (trans m h))
Proof
  Cases_on ‘LENGTH h ≤ k’ >- simp[TAKE_LENGTH_TOO_LONG] >>
  ‘k ≤ LENGTH h’ by simp[] >>
  simp[trans_TAKE_split, FILTER_APPEND, kanswers_APPEND,
       kanswers_FILTER_NONE, zipr_NIL_NONE] >>
  ‘SUC (LENGTH h) = (SUC (LENGTH h) - k) + k’ by simp[] >>
  REWRITE_TAC[trans_def] >> pop_assum SUBST1_TAC >>
  REWRITE_TAC[GENLIST_APPEND, FLAT_APPEND, FILTER_APPEND, kanswers_APPEND] >>
  simp[]
QED

Theorem kanswers_NONE[local]:
  ∀tr. EVERY (λp. SND p = NONE) tr ⇒ kanswers V tr = []
Proof
  Induct >> simp[kanswers_def] >> PairCases >> rw[] >> gvs[kanswers_def]
QED

Theorem kanswers_trans_NIL:
  kanswers V (trans m []) = []
Proof
  simp[trans_def, round_trans_def, responses_at_def] >>
  irule kanswers_NONE >> simp[zipr_NIL_NONE]
QED

Theorem prefix_FLAT[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ FLAT l1 ≼ FLAT l2
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[]
QED

Theorem bytes_prefix_mono[local]:
  ∀s t. s ≼ t ⇒ MAP ((n2w : num -> word8) o ORD) s ≼ MAP (n2w o ORD) t
Proof
  Induct >> simp[] >> Cases_on ‘t’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The theorem
   ------------------------------------------------------------------------ *)

(* MAIN: for every accepted connection c and every round N0, out of c's
   handler's answers by round N0 is eventually written to c *)
Theorem server_v_live_every:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧
  handler_push_live V hf out B ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SPg (Wr (server_v V hf lfdn)) ifds s0 n)) ⇒
  ∀N0. ∃N. bytes (FLAT (out (conn_answers V Wr inner hf lfdn ifds s0 N0 c))) ≼
           bytes_written_to c
             (FLAT (GENLIST (grounds_events ifds (srelabel (Wr (server_v V hf lfdn))) s0)
                            (SUC N)))
Proof
  rpt strip_tac >>
  ‘uses_ok lfdn (Wr (server_v V hf lfdn))’ by metis_tac[uses_ok_wrap] >>
  ‘asyncLevel1$wf (server_v V hf lfdn)’ by metis_tac[hokv_wf, wf_server_v] >>
  qabbrev_tac ‘n1 = n + N0’ >>
  ‘MEM c (wacc (SPg (Wr (server_v V hf lfdn)) ifds s0 n1))’
    by (irule wacc_mono >> qexists_tac ‘n’ >> simp[Abbr ‘n1’]) >>
  (* c's handler's view, B rounds past n1 *)
  qspecl_then [‘n1’, ‘n1 + B’] mp_tac (Q.GENL [‘n’, ‘N’] view_wrap_ans) >>
  impl_tac >- simp[] >> strip_tac >>
  (* c's answers by round N0 are its handler's by its round N0 - a *)
  ‘conn_answers V Wr inner hf lfdn ifds s0 N0 c =
   kanswers V (trans (hf (w2n c)) (TAKE (N0 − a) g))’
    by (Cases_on ‘a ≤ N0’
        >- (simp[conn_answers_def] >>
            first_x_assum (qspec_then ‘N0 − a’ mp_tac) >>
            impl_tac >- simp[Abbr ‘n1’] >> simp[])
        >> ‘N0 − a = 0’ by simp[] >> pop_assum SUBST1_TAC >>
        simp[kanswers_trans_NIL] >>
        first_x_assum (qspec_then ‘0’ mp_tac) >> simp[kanswers_trans_NIL] >>
        strip_tac >>
        ‘∀h. inner (server_v V hf lfdn) (TAKE N0 h) =
             TAKE N0 (inner (server_v V hf lfdn) h)’ by fs[wrap_ok_def] >>
        qabbrev_tac ‘H = MAP sfs (ghist ifds (srelabel (Wr (server_v V hf lfdn))) s0 a)’ >>
        ‘MAP sfs (ghist ifds (srelabel (Wr (server_v V hf lfdn))) s0 N0) = TAKE N0 H’
          by simp[Abbr ‘H’, GSYM MAP_TAKE, ghist_TAKE] >>
        simp[conn_answers_def] >>
        qspecl_then [‘V’, ‘on_fd_v V (w2n c)’, ‘server_v V hf lfdn’, ‘N0’,
                     ‘inner (server_v V hf lfdn) H’]
          mp_tac (Q.GENL [‘V’, ‘P’, ‘m’, ‘k’, ‘h’] kanswers_trans_TAKE) >>
        simp[kanswers_trans_NIL]) >>
  (* so the handler writes out of them by some round j *)
  qpat_x_assum ‘handler_push_live _ _ _ _’
    (mp_tac o REWRITE_RULE [handler_push_live_def]) >>
  disch_then (qspecl_then [‘w2n c’, ‘g’, ‘N0 − a’] mp_tac) >>
  impl_tac >- simp[Abbr ‘n1’] >> strip_tac >>
  qexists_tac ‘a + j’ >> simp[] >>
  (* what the loop wrote to c by round a + j *)
  qspecl_then [‘lfdn’, ‘Wr (server_v V hf lfdn)’, ‘s0’, ‘c’, ‘a + j’, ‘ifds’] mp_tac
    (Q.GENL [‘lfdn’, ‘m’, ‘s0’, ‘c’, ‘n’, ‘ifds’] gen_rounds_bytes) >>
  impl_tac >- simp[] >> strip_tac >> pop_assum kall_tac >> pop_assum SUBST1_TAC >>
  ONCE_REWRITE_TAC[GSYM written_FILTER] >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >> disch_then kall_tac >>
  qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER (on_fd _) _ = _’ (qspec_then ‘j’ mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  simp[bytes_def] >> irule bytes_prefix_mono >> irule prefix_FLAT >> simp[]
QED

(* The same, with the round: answers given by round N0 are written within
   B more rounds (for a connection accepted by N0) *)
Theorem server_v_live_at:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧
  handler_push_live V hf out B ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SPg (Wr (server_v V hf lfdn)) ifds s0 n)) ∧ n ≤ N0 ⇒
  ∃N. N ≤ N0 + B ∧
      bytes (FLAT (out (conn_answers V Wr inner hf lfdn ifds s0 N0 c))) ≼
           bytes_written_to c
             (FLAT (GENLIST (grounds_events ifds (srelabel (Wr (server_v V hf lfdn))) s0)
                            (SUC N)))
Proof
  rpt strip_tac >>
  ‘uses_ok lfdn (Wr (server_v V hf lfdn))’ by metis_tac[uses_ok_wrap] >>
  ‘asyncLevel1$wf (server_v V hf lfdn)’ by metis_tac[hokv_wf, wf_server_v] >>
  ‘MEM c (wacc (SPg (Wr (server_v V hf lfdn)) ifds s0 N0))’
    by (irule wacc_mono >> qexists_tac ‘n’ >> simp[]) >>
  (* c's handler's view, B rounds past N0 *)
  qspecl_then [‘N0’, ‘N0 + B’] mp_tac (Q.GENL [‘n’, ‘N’] view_wrap_ans) >>
  impl_tac >- simp[] >> strip_tac >>
  (* c's answers by round N0 are its handler's by its round N0 - a *)
  ‘conn_answers V Wr inner hf lfdn ifds s0 N0 c =
   kanswers V (trans (hf (w2n c)) (TAKE (N0 − a) g))’
    by (simp[conn_answers_def] >>
        qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER (on_fd_v _ _) _ = _’
          (qspec_then ‘N0 − a’ mp_tac) >>
        impl_tac >- simp[] >> simp[]) >>
  (* so the handler writes out of them by some round j *)
  qpat_x_assum ‘handler_push_live _ _ _ _’
    (mp_tac o REWRITE_RULE [handler_push_live_def]) >>
  disch_then (qspecl_then [‘w2n c’, ‘g’, ‘N0 − a’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac ‘a + j’ >>
  conj_tac >- (qpat_x_assum ‘j ≤ _’ mp_tac >> qpat_x_assum ‘LENGTH g + a = _’ mp_tac >>
               simp[]) >>
  simp[] >>
  (* what the loop wrote to c by round a + j *)
  qspecl_then [‘lfdn’, ‘Wr (server_v V hf lfdn)’, ‘s0’, ‘c’, ‘a + j’, ‘ifds’] mp_tac
    (Q.GENL [‘lfdn’, ‘m’, ‘s0’, ‘c’, ‘n’, ‘ifds’] gen_rounds_bytes) >>
  impl_tac >- simp[] >> strip_tac >> pop_assum kall_tac >> pop_assum SUBST1_TAC >>
  ONCE_REWRITE_TAC[GSYM written_FILTER] >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >> disch_then kall_tac >>
  qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER (on_fd _) _ = _’ (qspec_then ‘j’ mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  simp[bytes_def] >> irule bytes_prefix_mono >> irule prefix_FLAT >> simp[]
QED
