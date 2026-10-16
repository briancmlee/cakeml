(*
  ChatSpecTimely bites: what the candidate clauses rule out, how they
  relate to ChatSpec, and that they are satisfiable.  Everything is proved.

  - Relation to ChatSpec: owed_open is a prefix of owed, so ChatSpec's
    chat_live implies chat_live_open; chat_prompt B implies the delivery
    clause of chat_live_open.
  - C-DELAY: for every B, a trace that delivers a line only after B + 1
    more polls fails chat_prompt B (it still delivers eventually).
  - C-JOIN: a server that leaves a connection pending for 2K + 2 polls in
    a world where two connections arrived fails chat_accept_prompt K; and
    (T2) the bound counts the current backlog: after c1 was accepted
    promptly, leaving c2 pending for K + 2 more polls fails it.
  - T1: a server that reads a line only after 6R + 1 extra polls fails
    chat_read_prompt R (it still reads it).
  - C-EOF: in a trace where the server reads c2's end-of-stream and then
    completes a line, ChatSpec's chat_live demands that line on c2, while
    chat_live_open does not (c2 is owed nothing).
  - Non-vacuity: a trace with the world's polls (one per schedule step),
    for ChatSpecBite's fair world, meets chat_safe, chat_live_open,
    chat_prompt 0, chat_accept_prompt 0 and chat_read_prompt 0.
*)
Theory ChatSpecTimelyBite
Ancestors
  ChatSpec ChatSpecTimely ChatSpecBite EchoSpec ffiSpikeSocketFFI
  ffiSpikeSocketFair llist
Libs
  preamble

Overload starts_with = “λevs io. LPREFIX (fromList evs) io”

(* A «sock_poll» on the listener 3w (its results do not matter here) *)
Definition pl_def:
  pl = IO_event (ExtCall «sock_poll») (fd_bytes 3w) []
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

Theorem arrivals_upto_LNIL[local]:
  arrivals_upto m [||] = []
Proof
  Cases_on ‘m’ >> simp[arrivals_upto_def]
QED

Theorem nconnects_chat_world:
  nconnects n chat_world = if n = 0 then 0 else 2
Proof
  Cases_on ‘n’ >- EVAL_TAC >>
  Cases_on ‘n'’ >- EVAL_TAC >>
  Cases_on ‘n’ >- EVAL_TAC >>
  Cases_on ‘n'’ >- EVAL_TAC >>
  simp[nconnects_def, arrivals_upto_def, chat_world_def, arrivals_upto_LNIL] >>
  EVAL_TAC
QED

Theorem event_accepts_acc[local]:
  event_accepts d (acc c) ⇔ d = c
Proof
  simp[event_accepts_def, acc_def, MAP_ZIP] >>
  metis_tac[bytes_fd_fd_bytes]
QED

Theorem event_accepts_rd_wr[local]:
  ¬event_accepts d (rd c bs n) ∧ ¬event_accepts d (wr c bs)
Proof
  simp[event_accepts_def, rd_def, wr_def]
QED

Theorem read_prefix[local]:
  evs ≼ L ⇒ bytes_read_from c evs ≼ bytes_read_from c L
Proof
  rw[IS_PREFIX_APPEND] >> simp[bytes_read_from_def] >> metis_tac[]
QED

Theorem read_REPLICATE_pl[local]:
  bytes_read_from c (REPLICATE n pl) = []
Proof
  Induct_on ‘n’ >> fs[bytes_read_from_def, pl_def, event_read_def]
QED

Theorem polls_REPLICATE_APPEND[local]:
  polls (REPLICATE n pl ++ l) = n + polls l
Proof
  simp[polls_def, FILTER_APPEND] >> simp[GSYM polls_def, polls_REPLICATE_pl]
QED

Definition late_acc_evs_def:
  late_acc_evs k = REPLICATE (2 * k + 2) pl ++ [acc c1; acc c2]
End

(* MAIN: leaving c1 pending for 2k + 2 polls, when two connections have
   arrived, violates chat_accept_prompt k *)
Theorem broken_accepts_late:
  ¬chat_accept_prompt k chat_world (fromList (late_acc_evs k))
Proof
  ‘is_poll pl ∧ ¬is_accept_ev pl’ by simp[pl_def, is_poll_def, is_accept_ev_def] >>
  ‘[pl] ≼ REPLICATE (2 * k + 2) pl ++ [acc c1; acc c2]’
    by (‘2 * k + 2 = SUC (2 * k + 1)’ by simp[] >> pop_assum SUBST1_TAC >> simp[]) >>
  CCONTR_TAC >> fs[chat_accept_prompt_def] >>
  first_x_assum (qspecl_then [‘c1’, ‘[pl]’] mp_tac) >>
  simp[connects_upto_chat_world, nconnects_chat_world, LPREFIX_fromList_fromList,
       late_acc_evs_def, polls_def, naccepts_def] >>
  qx_gen_tac ‘E’ >> CCONTR_TAC >> fs[] >>
  fs[IS_PREFIX_EQ_TAKE] >>
  Cases_on ‘n ≤ 2 * k + 2’
  >- (‘EVERY ($= pl) (TAKE n (REPLICATE (2 * k + 2) pl))’
        by (irule EVERY_TAKE >> simp[EVERY_REPLICATE]) >>
      ‘¬event_accepts c1 pl’ by simp[pl_def, event_accepts_def] >>
      gvs[TAKE_APPEND1, EVERY_MEM, EXISTS_MEM] >> metis_tac[])
  >> qpat_x_assum ‘LENGTH (FILTER _ _) ≤ _’ mp_tac >>
  simp[TAKE_APPEND2, FILTER_APPEND, not_polls] >>
  simp[GSYM polls_def, polls_REPLICATE_pl]
QED

(* T2: c1 is accepted at once; c2 is left pending for k + 2 more polls *)
Definition late_acc2_evs_def:
  late_acc2_evs k = [pl; acc c1] ++ REPLICATE (k + 2) pl ++ [acc c2]
End

(* MAIN (T2): at the second poll one connection is still waiting, so the
   bound is k polls; leaving c2 pending for k + 2 polls violates
   chat_accept_prompt k (the old bound, k per connection ever arrived,
   allowed it) *)
Theorem broken_accepts_backlog:
  ¬chat_accept_prompt k chat_world (fromList (late_acc2_evs k))
Proof
  ‘is_poll pl ∧ ¬is_accept_ev pl ∧ is_accept_ev (acc c1)’
    by (simp[pl_def, is_poll_def, is_accept_ev_def] >> EVAL_TAC) >>
  CCONTR_TAC >> fs[chat_accept_prompt_def] >>
  first_x_assum (qspecl_then [‘c2’, ‘[pl; acc c1; pl]’] mp_tac) >>
  simp[connects_upto_chat_world, nconnects_chat_world, LPREFIX_fromList_fromList,
       polls_def, naccepts_def, not_polls] >>
  ‘REPLICATE (k + 2) pl = pl :: pl :: REPLICATE k pl’
    by (‘k + 2 = SUC (SUC k)’ by decide_tac >> pop_assum SUBST1_TAC >>
        REWRITE_TAC[REPLICATE]) >>
  conj_tac >- simp[late_acc2_evs_def] >>
  qx_gen_tac ‘E’ >> CCONTR_TAC >> fs[] >>
  fs[late_acc2_evs_def, IS_PREFIX_EQ_TAKE] >>
  ‘¬event_accepts c2 pl ∧ ¬event_accepts c2 (acc c1)’
    by simp[pl_def, event_accepts_def, event_accepts_acc] >>
  Cases_on ‘n ≤ k + 4’
  >- (‘EVERY (λe. ¬event_accepts c2 e) (TAKE n ([pl; acc c1] ++ REPLICATE (k + 2) pl))’
        by (irule EVERY_TAKE >> simp[EVERY_REPLICATE]) >>
      ‘TAKE n ([pl; acc c1] ++ REPLICATE (k + 2) pl ++ [acc c2]) =
       TAKE n ([pl; acc c1] ++ REPLICATE (k + 2) pl)’
        by (REWRITE_TAC[APPEND_ASSOC] >> irule TAKE_APPEND1 >> simp[]) >>
      gvs[EVERY_MEM, EXISTS_MEM] >> metis_tac[])
  >> qpat_x_assum ‘REPLICATE _ _ = _’ kall_tac >>
  qpat_x_assum ‘LENGTH (FILTER _ _) ≤ _’ mp_tac >>
  qpat_x_assum ‘E = _’ SUBST1_TAC >>
  ‘n = (k + 4) + (n − (k + 4))’ by decide_tac >> pop_assum SUBST1_TAC >>
  ONCE_REWRITE_TAC[TAKE_SUM] >>
  ‘TAKE (k + 4) (pl::acc c1::(REPLICATE (k + 2) pl ++ [acc c2])) =
   pl::acc c1::REPLICATE (k + 2) pl’
    by (‘k + 4 = SUC (SUC (k + 2))’ by decide_tac >> pop_assum SUBST1_TAC >>
        simp[TAKE_APPEND1]) >>
  pop_assum SUBST1_TAC >> simp[FILTER_APPEND, not_polls] >>
  simp[GSYM polls_def, polls_REPLICATE_pl] >>
  simp[TAKE_APPEND2, polls_def, FILTER_APPEND, not_polls] >>
  simp[GSYM polls_def, polls_REPLICATE_pl]
QED

(* ------------------------------------------------------------------------
   T1: prompt reads
   ------------------------------------------------------------------------ *)

(* c1 sends "hi\n" at step 2; the server reads it only after 6R + 1 more
   polls *)
Definition late_rd_evs_def:
  late_rd_evs R = [pl; acc c1; acc c2; pl] ++ REPLICATE (6 * R + 1) pl ++ [rd c1 HI 100]
End

(* MAIN (T1): reading c1's line only after 6R + 1 extra polls violates
   chat_read_prompt R (although the line is read) *)
Theorem broken_reads_late:
  ¬chat_read_prompt R chat_world (fromList (late_rd_evs R)) ∧
  HI ≼ bytes_read_from c1 (late_rd_evs R)
Proof
  ‘is_poll pl ∧ ¬is_poll (acc c1) ∧ ¬is_poll (acc c2)’
    by simp[pl_def, is_poll_def, not_polls] >>
  ‘event_read c1 pl = [] ∧ event_read c1 (acc c1) = [] ∧ event_read c1 (acc c2) = [] ∧
   event_read c1 (rd c1 HI 100) = HI’ by EVAL_TAC >>
  ‘∀m. FLAT (REPLICATE m ([] : word8 list)) = []’ by (Induct >> simp[]) >>
  conj_tac
  >- (simp[chat_read_prompt_def, sent_upto_chat_world, nconnects_chat_world,
           LPREFIX_fromList_fromList] >>
      qexistsl_tac [‘c1’, ‘2’] >> simp[] >>
      ‘whole_lines HI = HI’ by EVAL_TAC >> simp[] >>
      qx_gen_tac ‘E’ >> CCONTR_TAC >> fs[] >>
      ‘late_rd_evs R = ([pl; acc c1; acc c2; pl] ++ REPLICATE (6 * R + 1) pl) ++ [rd c1 HI 100]’
        by simp[late_rd_evs_def] >>
      ‘E ≼ ([pl; acc c1; acc c2; pl] ++ REPLICATE (6 * R + 1) pl) ++ [rd c1 HI 100]’
        by metis_tac[] >>
      drule prefix_snoc >> strip_tac
      >- (qpat_x_assum ‘polls E ≤ _’ mp_tac >>
          qpat_x_assum ‘E = _’ SUBST1_TAC >>
          simp[polls_def, FILTER_APPEND, not_polls] >>
          simp[GSYM polls_def, polls_REPLICATE_pl])
      >> ‘bytes_read_from c1 ([pl; acc c1; acc c2; pl] ++ REPLICATE (6 * R + 1) pl) = []’
           by (REWRITE_TAC[bytes_read_from_def, MAP_APPEND, FLAT_APPEND] >> simp[] >>
               simp[GSYM bytes_read_from_def, read_REPLICATE_pl]) >>
      ‘bytes_read_from c1 E ≼ bytes_read_from c1 ([pl; acc c1; acc c2; pl] ++ REPLICATE (6 * R + 1) pl)’
        by (irule read_prefix >> first_assum ACCEPT_TAC) >>
      ‘bytes_read_from c1 E = []’
        by (qpat_x_assum ‘bytes_read_from c1 E ≼ _’ mp_tac >>
            qpat_x_assum ‘bytes_read_from _ _ = []’ SUBST1_TAC >> simp[]) >>
      fs[])
  >> simp[late_rd_evs_def, bytes_read_from_def,
          read_REPLICATE_pl |> REWRITE_RULE[bytes_read_from_def]]
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
   Non-vacuity, with the world's polls
   ------------------------------------------------------------------------ *)

(* One poll per step of chat_world's schedule: both connect; c1's "hi\n"
   arrives; c2's "yo\n" arrives; then the end of the schedule *)
Definition polled_evs_def:
  polled_evs = [pl; acc c1; acc c2;
                pl; rd c1 HI 100; wr c1 HI; wr c2 HI;
                pl; rd c2 YO 100; wr c1 YO; wr c2 YO;
                pl]
End

Theorem polled_prefixes[local]:
  evs ≼ polled_evs ⇔ ∃k. k ≤ 12 ∧ evs = TAKE k polled_evs
Proof
  eq_tac >> rw[]
  >- (gvs[IS_PREFIX_EQ_TAKE] >> qexists ‘n’ >> gvs[polled_evs_def])
  >> simp[IS_PREFIX_EQ_TAKE] >> qexists ‘k’ >> simp[polled_evs_def]
QED

Theorem twelve[local]:
  (k:num) ≤ 12 ⇒ k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
           k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12
Proof
  decide_tac
QED

Theorem polled_others[local]:
  d ≠ c1 ∧ d ≠ c2 ⇒
  ∀k. owed d (TAKE k polled_evs) = [] ∧ bytes_written_to d (TAKE k polled_evs) = [] ∧
      bytes_read_from d (TAKE k polled_evs) = []
Proof
  strip_tac >> gen_tac >>
  ‘¬EXISTS (event_accepts d) polled_evs’
    by (simp[polled_evs_def, event_accepts_acc, event_accepts_rd_wr] >>
        simp[pl_def, event_accepts_def]) >>
  ‘¬EXISTS (event_accepts d) (TAKE k polled_evs)’
    by (fs[EXISTS_NOT_EVERY] >> irule EVERY_TAKE >> first_assum ACCEPT_TAC) >>
  ‘owed d (TAKE k polled_evs) = []’
    by (irule owed_not_accepted >> first_assum ACCEPT_TAC) >>
  ‘∀e. MEM e polled_evs ⇒ event_written d e = [] ∧ event_read d e = []’
    by (rw[polled_evs_def] >>
        simp[pl_def, event_written_def, event_read_def, acc_def, rd_def, wr_def,
             TAKE_APPEND1, TAKE_LENGTH_ID_rwt] >> rw[] >> gvs[]) >>
  simp[bytes_written_to_def, bytes_read_from_def, FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >>
  metis_tac[MEM_TAKE]
QED

Theorem polled_polls[local]:
  polls (TAKE k polled_evs) =
    if k = 0 then 0 else if k ≤ 3 then 1 else if k ≤ 7 then 2 else if k ≤ 11 then 3 else 4
Proof
  Cases_on ‘k ≤ 12’
  >- (drule twelve >> strip_tac >> gvs[] >> EVAL_TAC)
  >> simp[TAKE_LENGTH_TOO_LONG, polled_evs_def] >> EVAL_TAC
QED

Definition rnd_def:
  rnd (k:num) = if k = 0 then (0:num) else if k ≤ 3 then 3 else if k ≤ 7 then 7
                else if k ≤ 11 then 11 else 12
End

(* What each point owes is written by the end of its round, and nothing
   more is ever written *)
Theorem polled_owed[local]:
  k ≤ 12 ⇒
  owed d (TAKE k polled_evs) ≼ bytes_written_to d (TAKE (rnd k) polled_evs) ∧
  bytes_written_to d (TAKE k polled_evs) ≼ owed d (TAKE k polled_evs)
Proof
  strip_tac >>
  Cases_on ‘d = c1’ >- (drule twelve >> strip_tac >> gvs[rnd_def] >> EVAL_TAC) >>
  Cases_on ‘d = c2’ >- (drule twelve >> strip_tac >> gvs[rnd_def] >> EVAL_TAC) >>
  simp[polled_others]
QED

Theorem rnd_polls[local]:
  k ≤ 12 ⇒ rnd k ≤ 12 ∧ polls (TAKE (rnd k) polled_evs) = polls (TAKE k polled_evs)
Proof
  strip_tac >> drule twelve >> strip_tac >> gvs[rnd_def] >> EVAL_TAC
QED

Theorem polled_safe[local]:
  chat_safe (fromList polled_evs)
Proof
  rw[chat_safe_def, LPREFIX_fromList_fromList, polled_prefixes] >>
  metis_tac[polled_owed]
QED

Theorem polled_delivers[local]:
  starts_with evs (fromList polled_evs) ⇒
  ∃evs'. starts_with evs' (fromList polled_evs) ∧ polls evs' ≤ polls evs ∧
         owed_open d evs ≼ bytes_written_to d evs'
Proof
  rw[LPREFIX_fromList_fromList, polled_prefixes] >>
  qexists_tac ‘TAKE (rnd k) polled_evs’ >>
  drule rnd_polls >> strip_tac >> simp[] >>
  conj_tac >- (qexists_tac ‘rnd k’ >> simp[]) >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘owed d (TAKE k polled_evs)’ >>
  simp[owed_open_prefix] >> metis_tac[polled_owed]
QED

Theorem polled_accepts[local]:
  1 ≤ n ∧ (d = c1 ∨ d = c2) ⇒
  ∃evs. starts_with evs (fromList polled_evs) ∧ polls evs ≤ n ∧
        EXISTS (event_accepts d) evs
Proof
  strip_tac >> qexists_tac ‘TAKE 3 polled_evs’ >>
  simp[LPREFIX_fromList_fromList, polled_polls] >>
  gvs[] >> EVAL_TAC
QED

Theorem polled_reads[local]:
  ∃evs. starts_with evs (fromList polled_evs) ∧ polls evs ≤ n ∧
        whole_lines (sent_upto c n chat_world) ≼ bytes_read_from c evs
Proof
  simp[sent_upto_chat_world, LPREFIX_fromList_fromList] >>
  Cases_on ‘c = c1 ∧ 2 ≤ n’
  >- (qexists_tac ‘TAKE (if 3 ≤ n then 9 else 5) polled_evs’ >>
      rw[polled_polls] >> gvs[] >> EVAL_TAC)
  >> Cases_on ‘c = c2 ∧ 3 ≤ n’
  >- (qexists_tac ‘TAKE 9 polled_evs’ >> simp[polled_polls] >> gvs[] >> EVAL_TAC)
  >> qexists_tac ‘[]’ >> simp[polls_def] >>
  rw[] >> gvs[] >> EVAL_TAC
QED

(* MAIN (non-vacuity): a trace with the world's polls meets every clause
   with the tightest bounds *)
Theorem chat_timely_satisfiable:
  server_world 3w chat_world ∧
  chat_safe (fromList polled_evs) ∧ chat_live_open chat_world (fromList polled_evs) ∧
  chat_prompt 0 (fromList polled_evs) ∧
  chat_accept_prompt 0 chat_world (fromList polled_evs) ∧
  chat_read_prompt 0 chat_world (fromList polled_evs)
Proof
  rpt conj_tac
  >- simp[chat_spec_satisfiable]
  >- simp[polled_safe]
  >- (rw[chat_live_open_def, connects_upto_chat_world]
      >- (qspecl_then [‘n’, ‘c1’] mp_tac (Q.GENL [‘n’, ‘d’] polled_accepts) >>
          simp[] >> metis_tac[])
      >- (qspecl_then [‘n’, ‘c2’] mp_tac (Q.GENL [‘n’, ‘d’] polled_accepts) >>
          simp[] >> metis_tac[])
      >- metis_tac[polled_reads]
      >> metis_tac[polled_delivers])
  >- (rw[chat_prompt_def] >> drule polled_delivers >> simp[])
  >- (rw[chat_accept_prompt_def, connects_upto_chat_world] >>
      TRY (qspecl_then [‘polls evs0’, ‘c1’] mp_tac (Q.GENL [‘n’, ‘d’] polled_accepts) >>
           simp[] >> NO_TAC) >>
      qspecl_then [‘polls evs0’, ‘c2’] mp_tac (Q.GENL [‘n’, ‘d’] polled_accepts) >>
      simp[])
  >> rw[chat_read_prompt_def] >> metis_tac[polled_reads, ADD_CLAUSES, MULT_CLAUSES]
QED
