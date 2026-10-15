(*
  ChatSpec bites: the statement rules out plausible bugs, and it is
  satisfiable.  Everything here is proved.

  - Concrete I/O events, built as the socket model's FFI functions produce
    them: acc (a «sock_accept» that returned a connection), rd (a
    «sock_read» that returned data), wr (a «sock_write»).
  - Facts a reader can check the definitions against: what is owed only
    grows (owed_mono), and all clients see slices of ONE sequence
    (chat_safe_one_order).
  - Broken servers: dropping, duplicating or reordering a line (between
    clients, or consistently for everybody against real time), relaying a
    line before its newline was read, inventing a line, sending backlog to
    a late joiner, writing to a connection never accepted: unsafe.
    Starving a client, never accepting, never reading: not live.
  - Non-vacuity: a fair world with two clients, and an ideal trace for it
    that is both safe and live.
*)
Theory ChatSpecBite
Ancestors
  ChatSpec EchoSpec ffiSpikeSocketFFI ffiSpikeSocketFair llist Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   Concrete events
   ------------------------------------------------------------------------ *)

(* A «sock_accept» on the listener 3w that returned connection d *)
Definition acc_def:
  acc d =
    IO_event (ExtCall «sock_accept») (fd_bytes 3w)
      (ZIP (REPLICATE 9 0w, 1w :: fd_bytes d))
End

(* A «sock_read» on c with a buffer of n data bytes that returned bs *)
Definition rd_def:
  rd c bs n =
    IO_event (ExtCall «sock_read») (fd_bytes c)
      (ZIP (REPLICATE (n + 9) 0w,
            0w :: n2w8 (LENGTH bs) ++ bs ++ REPLICATE (n - LENGTH bs) 0w))
End

(* A «sock_write» of bs on c *)
Definition wr_def:
  wr c bs = IO_event (ExtCall «sock_write») (fd_bytes c ++ bs) []
End

Overload c1 = “4w : word64”
Overload c2 = “5w : word64”
(* "a\n", "b\n", and "a" without its newline *)
Overload LA = “[97w; 10w] : word8 list”
Overload LB = “[98w; 10w] : word8 list”
Overload HALF = “[97w] : word8 list”

Overload starts_with = “λevs io. LPREFIX (fromList evs) io”

(* ------------------------------------------------------------------------
   Reading the definitions
   ------------------------------------------------------------------------ *)

Theorem relayed_SNOC:
  relayed (evs ++ [e]) = relayed evs ++ completes evs e
Proof
  simp[relayed_def, GSYM ADD1, GENLIST, SNOC_APPEND, FLAT_SNOC] >>
  simp[EL_APPEND2, TAKE_LENGTH_APPEND] >>
  AP_TERM_TAC >> simp[GENLIST_FUN_EQ] >> rw[] >>
  simp[EL_APPEND1, TAKE_APPEND1]
QED

Theorem relayed_APPEND_prefix[local]:
  ∀l evs. relayed evs ≼ relayed (evs ++ l)
Proof
  ho_match_mp_tac SNOC_INDUCT >> rw[SNOC_APPEND] >>
  ‘evs ++ (l ++ [x]) = (evs ++ l) ++ [x]’ by simp[] >>
  pop_assum SUBST1_TAC >> simp[relayed_SNOC] >>
  metis_tac[IS_PREFIX_APPEND, IS_PREFIX_TRANS, APPEND_ASSOC]
QED

(* The order is never revised: later events only add lines at the end *)
Theorem relayed_mono:
  evs ≼ evs' ⇒ relayed evs ≼ relayed evs'
Proof
  strip_tac >> drule_then strip_assume_tac (iffLR IS_PREFIX_APPEND) >>
  simp[relayed_APPEND_prefix]
QED

Theorem owed_not_accepted:
  ¬EXISTS (event_accepts d) evs ⇒ owed d evs = []
Proof
  rw[owed_def] >>
  ‘SPLITP (event_accepts d) evs = (evs, [])’
    by (irule SPLITP_EVERY >> fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  simp[]
QED

Theorem owed_accepted:
  event_accepts d e ∧ ¬EXISTS (event_accepts d) before ⇒
  owed d (before ++ e :: after) =
    DROP (LENGTH (relayed before)) (relayed (before ++ e :: after))
Proof
  strip_tac >>
  ‘∀before. ¬EXISTS (event_accepts d) before ⇒
            SPLITP (event_accepts d) (before ++ e :: after) = (before, e :: after)’
    by (Induct >> rpt strip_tac >> gvs[rich_listTheory.SPLITP]) >>
  ‘SPLITP (event_accepts d) (before ++ e :: after) = (before, e :: after)’
    by metis_tac[] >>
  ONCE_REWRITE_TAC[owed_def] >> pop_assum SUBST1_TAC >> simp[]
QED

(* What a client is owed only grows *)
Theorem EXISTS_first[local]:
  ∀l. EXISTS P l ⇒ ∃b e a. l = b ++ e :: a ∧ P e ∧ ¬EXISTS P b
Proof
  Induct >> rw[]
  >- (qexistsl [‘[]’, ‘h’, ‘l’] >> simp[])
  >> Cases_on ‘P h’
  >- (qexistsl [‘[]’, ‘h’, ‘l’] >> simp[])
  >> first_x_assum drule >> rw[] >> qexistsl [‘h :: b’, ‘e’, ‘a’] >> simp[]
QED

Theorem DROP_prefix[local]:
  x ≼ y ⇒ DROP n x ≼ DROP n y
Proof
  rw[IS_PREFIX_APPEND] >> simp[DROP_APPEND] >>
  Cases_on ‘n ≤ LENGTH x’ >> simp[DROP_LENGTH_TOO_LONG] >> metis_tac[]
QED

Theorem owed_mono:
  evs ≼ evs' ⇒ owed d evs ≼ owed d evs'
Proof
  strip_tac >> Cases_on ‘EXISTS (event_accepts d) evs’
  >- (drule EXISTS_first >> strip_tac >>
      qpat_x_assum ‘_ ≼ _’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
      ‘evs' = b ++ e :: (a ++ l)’ by simp[] >>
      ‘owed d evs = DROP (LENGTH (relayed b)) (relayed evs) ∧
       owed d evs' = DROP (LENGTH (relayed b)) (relayed evs')’
        by (conj_tac >> qpat_x_assum ‘evs = _’ SUBST1_TAC >>
            qpat_x_assum ‘evs' = b ++ _’ SUBST1_TAC >>
            irule owed_accepted >> fs[]) >>
      rpt (qpat_x_assum ‘owed _ _ = _’ (fn th => REWRITE_TAC[th])) >>
      irule DROP_prefix >> irule relayed_mono >> simp[IS_PREFIX_APPEND])
  >> drule owed_not_accepted >> simp[]
QED

(* MAIN (explanatory): under safety, at every point, every client has been
   sent a slice of ONE sequence, the lines in the order the server
   completed them. *)
Theorem chat_safe_one_order:
  chat_safe io ∧ starts_with evs io ⇒
  ∀d. ∃j. bytes_written_to d evs ≼ DROP j (relayed evs)
Proof
  rw[chat_safe_def] >> first_x_assum drule >> disch_then (qspec_then ‘d’ mp_tac) >>
  rw[owed_def] >> Cases_on ‘SPLITP (event_accepts d) evs’ >> gvs[] >>
  Cases_on ‘r’ >> gvs[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Broken servers violate safety
   ------------------------------------------------------------------------ *)

(* c2 misses c1's first line *)
Theorem broken_drops_a_line:
  starts_with [acc c1; acc c2; rd c1 LA 100; rd c1 LB 100; wr c2 LB] io ⇒
  ¬chat_safe io
Proof
  rw[chat_safe_def] >>
  qexistsl [‘[acc c1; acc c2; rd c1 LA 100; rd c1 LB 100; wr c2 LB]’, ‘c2’] >>
  simp[] >> EVAL_TAC
QED

Theorem broken_duplicates_a_line:
  starts_with [acc c1; rd c1 LA 100; wr c1 (LA ++ LA)] io ⇒ ¬chat_safe io
Proof
  rw[chat_safe_def] >>
  qexistsl [‘[acc c1; rd c1 LA 100; wr c1 (LA ++ LA)]’, ‘c1’] >>
  simp[] >> EVAL_TAC
QED

(* the two clients see the two lines in different orders *)
Theorem broken_reorders_between_clients:
  starts_with [acc c1; acc c2; rd c1 LA 100; rd c2 LB 100;
               wr c1 (LA ++ LB); wr c2 (LB ++ LA)] io ⇒
  ¬chat_safe io
Proof
  rw[chat_safe_def] >>
  qexistsl [‘[acc c1; acc c2; rd c1 LA 100; rd c2 LB 100;
              wr c1 (LA ++ LB); wr c2 (LB ++ LA)]’, ‘c2’] >>
  simp[] >> EVAL_TAC
QED

(* everybody sees the same order, but against real time: "a\n" was read
   in full before any of "b\n" was *)
Theorem broken_consistent_but_against_real_time:
  starts_with [acc c1; acc c2; rd c1 LA 100; rd c2 LB 100;
               wr c1 (LB ++ LA); wr c2 (LB ++ LA)] io ⇒
  ¬chat_safe io
Proof
  rw[chat_safe_def] >>
  qexistsl [‘[acc c1; acc c2; rd c1 LA 100; rd c2 LB 100;
              wr c1 (LB ++ LA); wr c2 (LB ++ LA)]’, ‘c1’] >>
  simp[] >> EVAL_TAC
QED

(* relays "a" before its newline has been read *)
Theorem broken_relays_before_newline:
  starts_with [acc c1; acc c2; rd c1 HALF 100; wr c2 HALF] io ⇒
  ¬chat_safe io
Proof
  rw[chat_safe_def] >>
  qexistsl [‘[acc c1; acc c2; rd c1 HALF 100; wr c2 HALF]’, ‘c2’] >>
  simp[] >> EVAL_TAC
QED

(* completes the line itself *)
Theorem broken_invents_a_newline:
  starts_with [acc c1; rd c1 HALF 100; wr c1 LA] io ⇒ ¬chat_safe io
Proof
  rw[chat_safe_def] >>
  qexistsl [‘[acc c1; rd c1 HALF 100; wr c1 LA]’, ‘c1’] >>
  simp[] >> EVAL_TAC
QED

(* a late joiner gets a line completed before it was accepted *)
Theorem broken_sends_backlog:
  starts_with [acc c1; rd c1 LA 100; acc c2; wr c2 LA] io ⇒ ¬chat_safe io
Proof
  rw[chat_safe_def] >>
  qexistsl [‘[acc c1; rd c1 LA 100; acc c2; wr c2 LA]’, ‘c2’] >>
  simp[] >> EVAL_TAC
QED

(* writes to a connection that was never accepted *)
Theorem broken_writes_unaccepted:
  starts_with [acc c1; rd c1 LA 100; wr c2 LA] io ⇒ ¬chat_safe io
Proof
  rw[chat_safe_def] >>
  qexistsl [‘[acc c1; rd c1 LA 100; wr c2 LA]’, ‘c2’] >>
  simp[] >> EVAL_TAC
QED

(* ------------------------------------------------------------------------
   Broken servers violate liveness
   ------------------------------------------------------------------------ *)

(* Two clients connect; then c1 sends "hi\n"; then c2 sends "yo\n" *)
Overload HI = “[104w; 105w; 10w] : word8 list”
Overload YO = “[121w; 111w; 10w] : word8 list”

Definition chat_world_def:
  chat_world =
    <| listeners := [(3w, [])]
     ; conns := []
     ; sched := [|[Connect 3w c1; Connect 3w c2]; [Data c1 HI]; [Data c2 YO]|] |>
End

Theorem ticks_quiet[local]:
  ∀n s. s.sched = [||] ⇒ ticks n s = s
Proof
  Induct >> rw[ticks_def, tick_def]
QED

Theorem chat_world_sched_wf:
  sched_wf chat_world
Proof
  rw[sched_wf_def] >>
  Cases_on ‘n’ >- (EVAL_TAC >> simp[]) >>
  Cases_on ‘n'’ >- (EVAL_TAC >> simp[]) >>
  Cases_on ‘n’ >- (EVAL_TAC >> simp[]) >>
  simp[ticks_def] >>
  ‘(tick (tick (tick chat_world))).sched = [||]’ by EVAL_TAC >>
  simp[ticks_quiet] >> simp[next_step_def, step_ok_def]
QED

Theorem arrivals_upto_nil[local]:
  arrivals_upto n [||] = []
Proof
  Cases_on ‘n’ >> simp[arrivals_upto_def]
QED

Theorem sent_upto_chat_world:
  sent_upto c n chat_world =
    (if c = c1 ∧ 2 ≤ n then HI else []) ++
    (if c = c2 ∧ 3 ≤ n then YO else [])
Proof
  Cases_on ‘n’ >- EVAL_TAC >>
  Cases_on ‘n'’ >- (EVAL_TAC >> rw[]) >>
  Cases_on ‘n’ >- (EVAL_TAC >> rw[]) >>
  simp[sent_upto_def, chat_world_def, arrivals_upto_def] >>
  Cases_on ‘n'’ >> simp[arrivals_upto_def] >> rw[] >> gvs[]
QED

Theorem connects_upto_chat_world:
  connects_upto d n chat_world ⇔ 1 ≤ n ∧ (d = c1 ∨ d = c2)
Proof
  Cases_on ‘n’ >- simp[connects_upto_def, arrivals_upto_def] >>
  Cases_on ‘n'’ >- (EVAL_TAC >> metis_tac[]) >>
  Cases_on ‘n’ >- (EVAL_TAC >> metis_tac[]) >>
  simp[connects_upto_def, arrivals_upto_def, chat_world_def, arrivals_upto_nil] >>
  metis_tac[]
QED

(* c2 was accepted, c1's line was read, but c2 never hears of it *)
Theorem broken_starves_a_client:
  starts_with [acc c1; acc c2; rd c1 HI 100] io ∧
  (∀evs. starts_with evs io ⇒ bytes_written_to c2 evs = []) ⇒
  ¬chat_live sk io
Proof
  rw[chat_live_def] >> disj2_tac >> disj2_tac >>
  qexistsl [‘c2’, ‘[acc c1; acc c2; rd c1 HI 100]’] >> rw[] >>
  Cases_on ‘starts_with evs' io’ >> simp[] >> res_tac >> simp[] >> EVAL_TAC
QED

Theorem broken_never_accepts:
  (∀evs. starts_with evs io ⇒ ¬EXISTS (event_accepts c2) evs) ⇒
  ¬chat_live chat_world io
Proof
  rw[chat_live_def, connects_upto_chat_world] >> disj1_tac >>
  qexistsl [‘c2’, ‘1’] >> simp[] >> metis_tac[]
QED

Theorem broken_never_reads:
  (∀evs. starts_with evs io ⇒ bytes_read_from c1 evs = []) ⇒
  ¬chat_live chat_world io
Proof
  rw[chat_live_def, sent_upto_chat_world] >> disj2_tac >> disj1_tac >>
  qexistsl [‘c1’, ‘2’] >> rw[] >>
  Cases_on ‘starts_with evs io’ >> simp[] >> res_tac >> simp[] >> EVAL_TAC
QED

(* ------------------------------------------------------------------------
   Non-vacuity
   ------------------------------------------------------------------------ *)

Theorem server_world_chat_world:
  server_world 3w chat_world
Proof
  simp[server_world_def, chat_world_sched_wf] >> EVAL_TAC
QED

(* The ideal run: accept both, read "hi\n" from c1 and relay it to both,
   then read "yo\n" from c2 and relay it to both. *)
Definition ideal_evs_def:
  ideal_evs = [acc c1; acc c2; rd c1 HI 100; wr c1 HI; wr c2 HI;
               rd c2 YO 100; wr c1 YO; wr c2 YO]
End

Theorem LPREFIX_fromList_fromList[local]:
  LPREFIX (fromList xs) (fromList ys) ⇔ xs ≼ ys
Proof
  simp[LPREFIX_fromList, from_toList]
QED

Theorem fd_bytes_11[local]:
  fd_bytes a = fd_bytes b ⇔ a = b
Proof
  metis_tac[bytes_fd_fd_bytes]
QED

Theorem event_accepts_acc[local]:
  event_accepts d (acc c) ⇔ d = c
Proof
  simp[event_accepts_def, acc_def, MAP_ZIP, fd_bytes_11] >> metis_tac[]
QED

Theorem event_accepts_rd_wr[local]:
  ¬event_accepts d (rd c bs n) ∧ ¬event_accepts d (wr c bs)
Proof
  simp[event_accepts_def, rd_def, wr_def]
QED

Theorem event_written_others[local]:
  d ≠ c1 ∧ d ≠ c2 ⇒ ∀e. MEM e ideal_evs ⇒ event_written d e = []
Proof
  rw[ideal_evs_def] >>
  simp[event_written_def, acc_def, rd_def, wr_def, TAKE_APPEND1,
       TAKE_LENGTH_ID_rwt] >> rw[] >> gvs[]
QED

Theorem prefixes_ideal[local]:
  evs ≼ ideal_evs ⇔ ∃k. k ≤ 8 ∧ evs = TAKE k ideal_evs
Proof
  eq_tac >> rw[]
  >- (gvs[IS_PREFIX_EQ_TAKE] >> qexists ‘n’ >> gvs[ideal_evs_def])
  >> simp[IS_PREFIX_EQ_TAKE] >> qexists ‘k’ >> simp[ideal_evs_def]
QED

Theorem ideal_safe:
  chat_safe (fromList ideal_evs)
Proof
  rw[chat_safe_def, LPREFIX_fromList_fromList, prefixes_ideal] >>
  Cases_on ‘d = c1’ >- (‘k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8’
         by decide_tac >> gvs[] >> EVAL_TAC) >>
  Cases_on ‘d = c2’ >- (‘k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8’
         by decide_tac >> gvs[] >> EVAL_TAC) >>
  ‘bytes_written_to d (TAKE k ideal_evs) = []’
    by (simp[bytes_written_to_def, FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >>
        metis_tac[event_written_others, MEM_TAKE]) >>
  simp[]
QED

Theorem ideal_live:
  chat_live chat_world (fromList ideal_evs)
Proof
  rw[chat_live_def, LPREFIX_fromList_fromList, connects_upto_chat_world,
     sent_upto_chat_world]
  >- (qexists ‘ideal_evs’ >> simp[ideal_evs_def, event_accepts_acc])
  >- (qexists ‘ideal_evs’ >> simp[ideal_evs_def, event_accepts_acc])
  >- (qexists ‘ideal_evs’ >> simp[] >> rw[] >> EVAL_TAC)
  >> qexists ‘ideal_evs’ >> simp[] >>
  irule IS_PREFIX_TRANS >> qexists ‘owed d ideal_evs’ >>
  simp[owed_mono] >>
  Cases_on ‘d = c1’ >- (gvs[] >> EVAL_TAC) >>
  Cases_on ‘d = c2’ >- (gvs[] >> EVAL_TAC) >>
  ‘owed d ideal_evs = []’
    by (irule owed_not_accepted >>
        simp[ideal_evs_def, event_accepts_acc, event_accepts_rd_wr]) >>
  simp[]
QED

(* MAIN (non-vacuity): a fair world, and a trace for it that is both safe
   and live *)
Theorem chat_spec_satisfiable:
  server_world 3w chat_world ∧
  chat_safe (fromList ideal_evs) ∧ chat_live chat_world (fromList ideal_evs)
Proof
  simp[server_world_chat_world, ideal_safe, ideal_live]
QED
