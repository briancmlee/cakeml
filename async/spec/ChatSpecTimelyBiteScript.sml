(*
  ChatSpecTimely bites: what the candidate clauses rule out, how they
  relate to ChatSpec, and that they are satisfiable.  Everything is proved.

  - Relation to ChatSpec: owed_open is a prefix of owed, so ChatSpec's
    chat_live implies chat_live_open; chat_prompt B implies the delivery
    clause of chat_live_open.
  - C-DELAY: for every B, a trace that delivers a line only after B + 1
    more polls fails chat_prompt B (it still delivers eventually).
  - C-JOIN: a server that leaves a connection pending for 2K + 2 polls in
    a world where two connections arrived fails chat_accept_prompt K.
  - C-EOF: in a trace where the server reads c2's end-of-stream and then
    completes a line, ChatSpec's chat_live demands that line on c2, while
    chat_live_open does not (c2 is owed nothing).
  - Non-vacuity: ChatSpecBite's ideal trace (no polls) meets chat_prompt 0,
    chat_accept_prompt 0 and chat_live_open.
*)
Theory ChatSpecTimelyBite
Ancestors
  ChatSpec ChatSpecTimely ChatSpecBite EchoSpec ffiSpikeSocketFFI
  ffiSpikeSocketFair llist
Libs
  preamble

Overload starts_with = “λevs io. LPREFIX (fromList evs) io”

(* A «sock_poll» (its bytes do not matter here) *)
Definition pl_def:
  pl = IO_event (ExtCall «sock_poll») [] []
End

(* A «sock_read» on c that returned end-of-stream *)
Definition eof_def:
  eof c = IO_event (ExtCall «sock_read») (fd_bytes c)
            (ZIP (REPLICATE 10 0w, 2w :: REPLICATE 9 0w))
End

Theorem LPREFIX_fromList_fromList[local]:
  LPREFIX (fromList xs) (fromList ys) ⇔ xs ≼ ys
Proof
  simp[LPREFIX_fromList, from_toList]
QED

(* ------------------------------------------------------------------------
   Relation to ChatSpec
   ------------------------------------------------------------------------ *)

Theorem SPLITP_FST_prefix[local]:
  ∀l. FST (SPLITP P l) ≼ l
Proof
  Induct >> simp[SPLITP] >> rw[]
QED

Theorem owed_open_prefix:
  owed_open d evs ≼ owed d evs
Proof
  simp[owed_open_def] >> irule owed_mono >> simp[SPLITP_FST_prefix]
QED

Theorem chat_live_open_of_chat_live:
  chat_live sk io ⇒ chat_live_open sk io
Proof
  rw[chat_live_def, chat_live_open_def] >> TRY (metis_tac[] >> NO_TAC) >>
  qpat_x_assum ‘∀d evs. _’ drule >>
  disch_then (qspec_then ‘d’ strip_assume_tac) >>
  metis_tac[IS_PREFIX_TRANS, owed_open_prefix]
QED

Theorem chat_prompt_delivers:
  chat_prompt B io ∧ starts_with evs io ⇒
  ∃evs'. starts_with evs' io ∧ owed_open d evs ≼ bytes_written_to d evs'
Proof
  rw[chat_prompt_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   C-DELAY
   ------------------------------------------------------------------------ *)

(* c1 is accepted and sends "a\n"; the server polls B + 1 times, then
   relays it *)
Definition late_evs_def:
  late_evs B = [acc c1; rd c1 LA 100] ++ REPLICATE (B + 1) pl ++ [wr c1 LA]
End

Theorem polls_REPLICATE_pl[local]:
  polls (REPLICATE n pl) = n
Proof
  Induct_on ‘n’ >> fs[polls_def, pl_def, is_poll_def]
QED

Theorem written_REPLICATE_pl[local]:
  bytes_written_to c (REPLICATE n pl) = []
Proof
  Induct_on ‘n’ >> fs[bytes_written_to_def, pl_def, event_written_def]
QED

Theorem prefix_snoc[local]:
  evs ≼ P ++ [x] ⇒ evs = P ++ [x] ∨ evs ≼ P
Proof
  rw[IS_PREFIX_APPEND] >> Cases_on ‘l’ using SNOC_CASES >> gvs[] >>
  disj2_tac >> qexists_tac ‘l'’ >>
  metis_tac[SNOC_APPEND, SNOC_11, APPEND_ASSOC]
QED

Theorem not_polls[local]:
  ¬is_poll (acc c) ∧ ¬is_poll (rd c bs n) ∧ ¬is_poll (wr c bs) ∧
  event_written c1 (acc c) = [] ∧ event_written c1 (rd c bs n) = []
Proof
  simp[is_poll_def, acc_def, rd_def, wr_def, event_written_def]
QED

Theorem written_prefix[local]:
  evs ≼ L ⇒ bytes_written_to c evs ≼ bytes_written_to c L
Proof
  rw[IS_PREFIX_APPEND] >> simp[bytes_written_to_def] >> metis_tac[]
QED

Theorem prefix_written_nil[local]:
  evs ≼ [acc c1; rd c1 LA 100] ++ REPLICATE n pl ⇒ bytes_written_to c1 evs = []
Proof
  strip_tac >>
  ‘bytes_written_to c1 ([acc c1; rd c1 LA 100] ++ REPLICATE n pl) = []’
    by (‘event_written c1 pl = []’ by simp[pl_def, event_written_def] >>
        simp[bytes_written_to_def, not_polls, FLAT_EQ_NIL, EVERY_REPLICATE]) >>
  drule_then (qspec_then ‘c1’ mp_tac) written_prefix >> simp[]
QED

Theorem polls_late[local]:
  polls (late_evs B) = B + 1
Proof
  simp[late_evs_def, polls_def, FILTER_APPEND, not_polls] >>
  simp[GSYM polls_def, polls_REPLICATE_pl]
QED

(* MAIN: for every B, a server that relays a line only after B + 1 polls
   violates chat_prompt B (although it does relay it) *)
Theorem broken_delays:
  ¬chat_prompt B (fromList (late_evs B)) ∧
  owed c1 [acc c1; rd c1 LA 100] ≼ bytes_written_to c1 (late_evs B)
Proof
  ‘owed c1 [acc c1; rd c1 LA 100] = LA’ by EVAL_TAC >>
  ‘owed_open c1 [acc c1; rd c1 LA 100] = LA’ by EVAL_TAC >>
  ‘polls [acc c1; rd c1 LA 100] = 0’ by simp[polls_def, not_polls] >>
  ‘late_evs B = ([acc c1; rd c1 LA 100] ++ REPLICATE (B + 1) pl) ++ [wr c1 LA]’
    by simp[late_evs_def] >>
  conj_tac
  >- (simp[chat_prompt_def, LPREFIX_fromList_fromList] >>
      qexistsl_tac [‘[acc c1; rd c1 LA 100]’, ‘c1’] >>
      conj_tac >- simp[late_evs_def] >>
      qx_gen_tac ‘E’ >> CCONTR_TAC >> fs[] >>
      ‘E ≼ ([acc c1; rd c1 LA 100] ++ REPLICATE (B + 1) pl) ++ [wr c1 LA]’
        by fs[] >>
      drule prefix_snoc >> strip_tac
      >- (‘polls E = B + 1’
            by (qpat_x_assum ‘E = _’ SUBST1_TAC >>
                simp[polls_def, FILTER_APPEND, not_polls] >>
                simp[GSYM polls_def, polls_REPLICATE_pl]) >> fs[])
      >> drule prefix_written_nil >> strip_tac >> fs[])
  >> qpat_x_assum ‘late_evs B = _’ SUBST1_TAC >>
  ‘event_written c1 pl = []’ by simp[pl_def, event_written_def] >>
  ‘FLAT (REPLICATE (B + 1) ([] : word8 list)) = []’
    by simp[FLAT_EQ_NIL, EVERY_REPLICATE] >>
  ‘event_written c1 (wr c1 LA) = LA’ by EVAL_TAC >>
  simp[bytes_written_to_def, not_polls]
QED

(* ------------------------------------------------------------------------
   C-JOIN
   ------------------------------------------------------------------------ *)

Definition late_acc_evs_def:
  late_acc_evs k = REPLICATE (2 * k + 2) pl ++ [acc c1; acc c2]
End

Theorem nconnects_chat_world[local]:
  nconnects 1 chat_world = 2
Proof
  EVAL_TAC
QED

(* MAIN: leaving c1 pending for 2k + 2 polls, when two connections have
   arrived, violates chat_accept_prompt k *)
Theorem broken_accepts_late:
  ¬chat_accept_prompt k chat_world (fromList (late_acc_evs k))
Proof
  simp[chat_accept_prompt_def, connects_upto_chat_world, nconnects_chat_world,
       LPREFIX_fromList_fromList] >>
  qexistsl_tac [‘c1’, ‘1’] >> simp[] >> qx_gen_tac ‘E’ >> CCONTR_TAC >> fs[] >>
  fs[late_acc_evs_def, IS_PREFIX_EQ_TAKE] >>
  Cases_on ‘n ≤ 2 * k + 2’
  >- (‘EVERY ($= pl) (TAKE n (REPLICATE (2 * k + 2) pl))’
        by (irule EVERY_TAKE >> simp[EVERY_REPLICATE]) >>
      ‘¬event_accepts c1 pl’ by simp[pl_def, event_accepts_def] >>
      gvs[TAKE_APPEND1, EVERY_MEM, EXISTS_MEM] >> metis_tac[])
  >> qpat_x_assum ‘polls _ ≤ _’ mp_tac >>
  simp[TAKE_APPEND2, polls_def, FILTER_APPEND, not_polls, nconnects_chat_world] >>
  simp[GSYM polls_def, polls_REPLICATE_pl]
QED

(* ------------------------------------------------------------------------
   C-EOF
   ------------------------------------------------------------------------ *)

(* c1 and c2 are accepted; the server reads c2's end-of-stream, then a line
   from c1, and relays it to c1 only *)
Definition eof_evs_def:
  eof_evs = [acc c1; acc c2; eof c2; rd c1 LA 100; wr c1 LA]
End

Theorem eof_prefixes[local]:
  evs ≼ eof_evs ⇔ ∃k. k ≤ 5 ∧ evs = TAKE k eof_evs
Proof
  eq_tac >> rw[]
  >- (gvs[IS_PREFIX_EQ_TAKE] >> qexists ‘n’ >> gvs[eof_evs_def])
  >> simp[IS_PREFIX_EQ_TAKE] >> qexists ‘k’ >> simp[eof_evs_def]
QED

(* MAIN: chat_live_open lets the server drop the departed c2 (it is owed
   nothing at any point), ChatSpec's chat_live does not (c2 is owed the
   line, and never gets it) *)
Theorem departed_client:
  (∀evs. evs ≼ eof_evs ⇒ owed_open c2 evs = []) ∧
  owed c2 eof_evs = LA ∧
  (∀evs. evs ≼ eof_evs ⇒ bytes_written_to c2 evs = []) ∧
  ¬chat_live sk (fromList eof_evs)
Proof
  ‘∀evs. evs ≼ eof_evs ⇒ owed_open c2 evs = [] ∧ bytes_written_to c2 evs = []’
    by (rw[eof_prefixes] >>
        ‘k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5’ by decide_tac >>
        gvs[] >> EVAL_TAC) >>
  ‘owed c2 eof_evs = LA’ by EVAL_TAC >>
  rpt conj_tac >> TRY (metis_tac[]) >>
  rw[chat_live_def, LPREFIX_fromList_fromList] >> disj2_tac >> disj2_tac >>
  qexistsl_tac [‘c2’, ‘eof_evs’] >> rw[] >>
  Cases_on ‘evs' ≼ eof_evs’ >> simp[] >> res_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   Non-vacuity
   ------------------------------------------------------------------------ *)

Theorem ideal_no_polls[local]:
  evs ≼ ideal_evs ⇒ polls evs = 0
Proof
  strip_tac >>
  ‘polls ideal_evs = 0’
    by simp[polls_def, ideal_evs_def, is_poll_def, acc_def, rd_def, wr_def] >>
  fs[IS_PREFIX_APPEND] >> qpat_x_assum ‘polls _ = 0’ mp_tac >>
  qpat_x_assum ‘_ = ideal_evs’ (SUBST1_TAC o SYM) >> simp[polls_def, FILTER_APPEND]
QED

(* MAIN (non-vacuity): ChatSpecBite's ideal trace, for its fair world,
   meets every candidate clause *)
Theorem chat_timely_satisfiable:
  server_world 3w chat_world ∧
  chat_safe (fromList ideal_evs) ∧ chat_live_open chat_world (fromList ideal_evs) ∧
  chat_prompt 0 (fromList ideal_evs) ∧
  chat_accept_prompt 0 chat_world (fromList ideal_evs)
Proof
  assume_tac chat_spec_satisfiable >> fs[chat_live_open_of_chat_live] >>
  conj_tac
  >- (rw[chat_prompt_def] >>
      qpat_x_assum ‘chat_live _ _’ (strip_assume_tac o REWRITE_RULE[chat_live_def]) >>
      first_x_assum drule >> disch_then (qspec_then ‘d’ strip_assume_tac) >>
      qexists_tac ‘evs'’ >> gvs[LPREFIX_fromList_fromList] >>
      imp_res_tac ideal_no_polls >> simp[] >>
      metis_tac[IS_PREFIX_TRANS, owed_open_prefix])
  >> rw[chat_accept_prompt_def] >>
  qpat_x_assum ‘chat_live _ _’ (strip_assume_tac o REWRITE_RULE[chat_live_def]) >>
  first_x_assum drule >> strip_tac >> qexists_tac ‘evs’ >>
  gvs[LPREFIX_fromList_fromList] >> imp_res_tac ideal_no_polls >> simp[]
QED
