(*
  The trace bridge for the chat server: ChatSpec's chat_safe, for the
  loop's trace of srelabel (chat_server lfd), from the model's
  chat_server_safe.

  ChatSpec's quantities (relayed, owed, bytes_written_to) look at a finite
  prefix evs of the trace, which may stop in the middle of a round.  The
  chain:
   1. Polls are invisible: each quantity is the same on FILTER np evs
      (np: not a «sock_poll» event).
   2. The loop's non-poll events are the act_events of the performed
      socket pairs, round after round (gperf), so FILTER np evs is
      MAP aev (TAKE k ps) for the performed pairs ps of rounds 0..n.
   3. The performed pairs correspond to a prefix of the model transcript
      (gen_trans_split's TREL), pair by pair (R0); on corresponding lists,
      relayed is bytes of lines_done, owed d is bytes of owed_m (w2n d),
      and bytes_written_to d is bytes of what the model wrote to w2n d.
   4. chat_server_safe, on that prefix of the model transcript.
*)
Theory asyncChatTrace
Ancestors
  words list rich_list asyncCore asyncLevel1 asyncLevel2 asyncTranscript
  asyncServer asyncServerSafety asyncM4ServerUses asyncM4Relabel
  asyncM4RelabelDist ffiSpikeSocketFFI asyncM3World asyncM4GRounds
  asyncM4SockInv asyncM4SockModel asyncM4GTrans asyncM4EchoRunOk
  asyncM4EchoSafe EchoSpec asyncRunOkGen ChatSpec ChatSpecBite
  asyncWithTap asyncChatSW asyncChatModel asyncChatSafe llist
Libs
  preamble

(* ------------------------------------------------------------------------
   Characters and bytes
   ------------------------------------------------------------------------ *)

Theorem byte_newline[local]:
  ((n2w (ORD c) : word8) = 10w) ⇔ c = #"\n"
Proof
  ‘ORD c < 256’ by simp[ORD_BOUND] >>
  eq_tac >> rw[] >> gvs[] >>
  ‘ORD c = 10’ by gvs[] >>
  ‘c = CHR (ORD c)’ by simp[CHR_ORD] >> pop_assum SUBST1_TAC >> simp[]
QED

Theorem dropWhile_bytes[local]:
  ∀s. dropWhile (λb. b ≠ 10w) (MAP ((n2w : num -> word8) o ORD) s) =
      MAP (n2w o ORD) (dropWhile (λc. c ≠ #"\n") s)
Proof
  Induct >> simp[byte_newline] >> rw[]
QED

Theorem whole_lines_bytes:
  whole_lines (bytes s) = bytes (wls s)
Proof
  simp[whole_lines_def, wls_def, GSYM MAP_REVERSE, dropWhile_bytes]
QED

Theorem bytes_prefix[local]:
  ∀s t. s ≼ t ⇒ bytes s ≼ bytes t
Proof
  Induct >> simp[] >> Cases_on ‘t’ >> simp[]
QED

(* ------------------------------------------------------------------------
   1. Polls are invisible
   ------------------------------------------------------------------------ *)

Definition np_def:
  np (IO_event (ExtCall n) conf bs) = (n ≠ «sock_poll») ∧
  np _ = T
End

Theorem not_np_projections[local]:
  ¬np e ⇒ event_written c e = [] ∧ event_read c e = [] ∧ ¬event_accepts d e
Proof
  Cases_on ‘e’ >> rename1 ‘IO_event f _ _’ >> Cases_on ‘f’ >>
  simp[np_def, event_written_def, event_read_def, event_accepts_def]
QED

Theorem bytes_written_to_FILTER:
  ∀evs. bytes_written_to c (FILTER np evs) = bytes_written_to c evs
Proof
  Induct >> simp[bytes_written_to_def] >> rw[] >>
  gvs[bytes_written_to_def, not_np_projections]
QED

Theorem bytes_read_from_FILTER:
  ∀evs. bytes_read_from c (FILTER np evs) = bytes_read_from c evs
Proof
  Induct >> simp[bytes_read_from_def] >> rw[] >>
  gvs[bytes_read_from_def, not_np_projections]
QED

Theorem bytes_read_from_SNOC[local]:
  bytes_read_from c (evs ++ [e]) = bytes_read_from c evs ++ event_read c e
Proof
  simp[bytes_read_from_def]
QED

Theorem completes_FILTER[local]:
  completes (FILTER np evs) e = completes evs e
Proof
  simp[completes_def, bytes_read_from_SNOC, bytes_read_from_FILTER]
QED

Theorem completes_not_np[local]:
  ¬np e ⇒ completes evs e = []
Proof
  simp[completes_def, bytes_read_from_SNOC, not_np_projections]
QED

Theorem relayed_FILTER:
  ∀evs. relayed (FILTER np evs) = relayed evs
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[] >> rw[SNOC_APPEND, FILTER_APPEND] >>
  Cases_on ‘np x’ >> gvs[relayed_SNOC, completes_FILTER, completes_not_np]
QED

Theorem SPLITP_FILTER[local]:
  ∀l. (∀x. P x ⇒ Q x) ⇒
      SPLITP P (FILTER Q l) = (FILTER Q (FST (SPLITP P l)),
                               FILTER Q (SND (SPLITP P l)))
Proof
  Induct >> simp[SPLITP] >> rw[] >> gvs[SPLITP] >> metis_tac[]
QED

Theorem SPLITP_SND_NIL[local]:
  ∀l. (∀x. P x ⇒ Q x) ⇒
      (FILTER Q (SND (SPLITP P l)) = [] ⇔ SND (SPLITP P l) = [])
Proof
  Induct >> simp[SPLITP] >> rw[] >> gvs[]
QED

Theorem owed_FILTER:
  owed d (FILTER np evs) = owed d evs
Proof
  ‘∀e. event_accepts d e ⇒ np e’ by metis_tac[not_np_projections] >>
  simp[owed_def, SPLITP_FILTER] >>
  drule SPLITP_SND_NIL >> disch_then (qspec_then ‘evs’ assume_tac) >>
  Cases_on ‘SPLITP (event_accepts d) evs’ >> gvs[] >>
  Cases_on ‘r’ >> gvs[] >>
  Cases_on ‘FILTER np (h :: t)’ >> gvs[relayed_FILTER]
QED

(* ------------------------------------------------------------------------
   2. The loop's events
   ------------------------------------------------------------------------ *)

Overload aev = “λ(p : sact # sresp). act_event (FST p) (SND p)”

(* A pair some socket call can produce *)
Definition pok_def:
  pok (p : sact # sresp) ⇔ ∃s s'. sock_do s (FST p) = SOME (SND p, s')
End

Theorem np_act_event[local]:
  np (act_event a r)
Proof
  Cases_on ‘a’ >> Cases_on ‘r’ >> simp[act_event_def, np_def]
QED

Theorem FILTER_round_events[local]:
  grun_ok ifds m s0 ⇒
  FILTER np (grounds_events ifds m s0 i) =
  MAP aev (ZIP (gacts ifds m s0 i, gres ifds m s0 i))
Proof
  strip_tac >> drule grun_ok_sock_acts >>
  disch_then (qspec_then ‘i’ strip_assume_tac) >>
  drule sock_acts_events >> strip_tac >>
  simp[grounds_events_alt, sock_acts_tot_def, FILTER_APPEND] >>
  simp[spoll_event_def, np_def] >>
  ‘FILTER np evs = evs’
    by (simp[FILTER_EQ_ID, EVERY_EL] >> gvs[EL_MAP2, np_act_event]) >>
  gvs[] >> simp[LIST_EQ_REWRITE, EL_MAP2, EL_MAP, EL_ZIP]
QED

Theorem FILTER_rounds:
  grun_ok ifds m s0 ⇒
  ∀n. FILTER np (FLAT (GENLIST (grounds_events ifds m s0) n)) =
      MAP aev (gperf ifds m s0 n)
Proof
  strip_tac >> drule FILTER_round_events >> strip_tac >>
  Induct >- simp[gperf_def] >>
  gvs[GENLIST, SNOC_APPEND, gperf_SUC, FILTER_APPEND, FLAT_APPEND]
QED

Theorem EVERY_pok_gperf:
  grun_ok ifds m s0 ⇒ EVERY pok (gperf ifds m s0 n)
Proof
  strip_tac >> rw[gperf_def, EVERY_MEM, MEM_FLAT, MEM_GENLIST, PULL_EXISTS] >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘i’ strip_assume_tac) >>
  drule sock_acts_responses >> drule sock_acts_events >> rpt strip_tac >>
  gvs[MEM_ZIP, pok_def] >> metis_tac[]
QED

Theorem FILTER_prefix[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ FILTER P l1 ≼ FILTER P l2
Proof
  rw[IS_PREFIX_APPEND] >> simp[FILTER_APPEND]
QED

Theorem prefix_MAP_TAKE[local]:
  l ≼ MAP f ps ⇒ l = MAP f (TAKE (LENGTH l) ps)
Proof
  rw[IS_PREFIX_APPEND] >> gvs[MAP_TAKE, TAKE_LENGTH_APPEND]
QED

(* ------------------------------------------------------------------------
   3. Corresponding lists
   ------------------------------------------------------------------------ *)

(* A model pair and the socket pair it corresponds to *)
Overload R0 = “λ(p0 : action # response option) (p : sact # sresp).
                 sfa (FST p0) = FST p ∧ SND p0 = SOME (sfr (SND p))”

Theorem TREL_LIST_REL:
  ∀tt ps. TREL tt (MAP (λ(a, r). (a, SOME r)) ps) ⇔ LIST_REL R0 tt ps
Proof
  Induct >- (Cases >> simp[]) >>
  rpt gen_tac >> Cases_on ‘ps’ >> simp[] >>
  PairCases_on ‘h’ >> PairCases_on ‘h'’ >> simp[] >> metis_tac[]
QED

Theorem pok_cases[local]:
  pok (a, r) ⇒
  (∀l. a = Accept l ⇒ ∃x. r = Accepted x) ∧
  (∀c n. a = Read c n ⇒ ∃x. r = Got x) ∧
  (∀c bs. a = Write c bs ⇒ r = Wrote)
Proof
  Cases_on ‘a’ >> rw[pok_def, sock_do_def, OPTION_MAP_EQ_SOME, EXISTS_PROD] >>
  gvs[]
QED

(* The fds of the model pairs fit in 64 bits *)
Overload fds_bdd = “λtt. ∀fd. EXISTS (on_fd fd) tt ⇒ fd < dimword(:64)”

Theorem written_read_bytes:
  ∀tt ps. LIST_REL R0 tt ps ∧ EVERY pok ps ∧ fds_bdd tt ⇒
          bytes_written_to c (MAP aev ps) = bytes (FLAT (written (w2n c) tt)) ∧
          bytes_read_from c (MAP aev ps) = bytes (FLAT (read (w2n c) tt))
Proof
  rpt gen_tac >> strip_tac >>
  ‘TREL tt (MAP (λ(a, r). (a, SOME r)) ps)’ by simp[TREL_LIST_REL] >>
  drule_then (qspec_then ‘c’ mp_tac) TREL_written_read >> simp[] >>
  strip_tac >> pop_assum (SUBST1_TAC o SYM) >> pop_assum (SUBST1_TAC o SYM) >>
  simp[bytes_written_to_def, bytes_read_from_def, MAP_MAP_o] >>
  qpat_x_assum ‘EVERY pok ps’ mp_tac >>
  qid_spec_tac ‘ps’ >> Induct >> simp[] >>
  PairCases >> rw[] >> gvs[pok_def] >>
  imp_res_tac event_written_act_event >> imp_res_tac event_read_act_event >>
  simp[] >>
  Cases_on ‘h0’ >> Cases_on ‘h1’ >>
  simp[owritten_def, oread_def, pwritten_def, pread_def] >>
  TRY (rename1 ‘Got ro’ >> Cases_on ‘ro’) >>
  simp[owritten_def, oread_def, pwritten_def, pread_def]
QED

Theorem LIST_REL_SNOC_R[local]:
  LIST_REL R tt (ps ++ [p]) ⇔
  ∃tt' p0. tt = tt' ++ [p0] ∧ LIST_REL R tt' ps ∧ R p0 p
Proof
  simp[LIST_REL_SPLIT2] >> eq_tac >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem fds_bdd_APPEND[local]:
  fds_bdd (a ++ b) ⇔ fds_bdd a ∧ fds_bdd b
Proof
  simp[] >> metis_tac[]
QED

Theorem event_fd_read[local]:
  event_fd (act_event (Read c n) (Got ro)) = c
Proof
  ‘TAKE 8 (fd_bytes c) = fd_bytes c’
    by (‘LENGTH (fd_bytes c) = 8’ by simp[] >> metis_tac[TAKE_LENGTH_ID]) >>
  simp[act_event_def, event_fd_def]
QED

Theorem pread_other[local]:
  (∀l. pread f (Accept l, r) = []) ∧ (∀c bs. pread f (Write c bs, r) = [])
Proof
  simp[pread_def]
QED

Theorem completes_act_event[local]:
  pok p ⇒
  completes evs (aev p) =
    DROP (LENGTH (whole_lines (bytes_read_from (event_fd (aev p)) evs)))
         (whole_lines (bytes_read_from (event_fd (aev p)) evs ++
                       pread (event_fd (aev p)) p))
Proof
  PairCases_on ‘p’ >> rw[pok_def] >> imp_res_tac event_read_act_event >>
  simp[completes_def, bytes_read_from_SNOC]
QED

Theorem relayed_lines_done:
  ∀ps tt. LIST_REL R0 tt ps ∧ EVERY pok ps ∧ fds_bdd tt ⇒
          relayed (MAP aev ps) = bytes (lines_done tt)
Proof
  ho_match_mp_tac SNOC_INDUCT >> conj_tac
  >- simp[relayed_def, lines_done_def] >>
  rw[SNOC_APPEND, LIST_REL_SNOC_R] >> gvs[fds_bdd_APPEND] >>
  ‘fds_bdd tt'’
    by (rpt strip_tac >> simp[] >> metis_tac[]) >>
  first_x_assum (qspec_then ‘tt'’ mp_tac) >> impl_tac >- metis_tac[] >>
  strip_tac >>
  simp[relayed_SNOC, lines_done_SNOC] >>
  PairCases_on ‘x’ >> PairCases_on ‘p0’ >> gvs[] >>
  drule completes_act_event >> simp[] >> disch_then kall_tac >>
  drule pok_cases >> strip_tac >>
  Cases_on ‘p00’ >> gvs[sfa_def]
  >~ [‘comp _ (Read _, _)’]
  >- (rename1 ‘comp _ (Read m, _)’ >> simp[event_fd_read] >>
      ‘m < dimword(:64)’ by (simp[] >> metis_tac[on_fd_def, FST]) >>
      mp_tac (Q.SPECL [‘tt'’, ‘ps’] (Q.SPEC ‘n2w m’ (Q.GEN ‘c’ written_read_bytes))) >>
      impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >> gvs[] >>
      Cases_on ‘x’ >> simp[sfr_def, comp_def, pread_def] >>
      rw[comp_def, pread_def] >>
      TRY (simp[whole_lines_bytes, GSYM MAP_DROP] >> NO_TAC) >>
      qabbrev_tac ‘s = MAP (CHR o w2n) x'’ >>
      ‘x' = bytes s’ by simp[Abbr ‘s’, bytes_round_trip] >>
      pop_assum SUBST1_TAC >>
      REWRITE_TAC[GSYM MAP_APPEND, whole_lines_bytes] >> simp[GSYM MAP_DROP])
  >> simp[pread_other, comp_def] >> TRY (Cases_on ‘x’) >> simp[sfr_def, comp_def]
QED

(* The two notions of "accepts d" agree on corresponding pairs *)
Theorem fd_bytes_11[local]:
  fd_bytes c = fd_bytes d ⇔ c = d
Proof
  eq_tac >> rw[] >> metis_tac[bytes_fd_fd_bytes]
QED

Theorem event_accepts_acc_of[local]:
  R0 p0 p ⇒ (event_accepts d (aev p) ⇔ acc_of (w2n d) p0)
Proof
  PairCases_on ‘p’ >> PairCases_on ‘p0’ >> rw[acc_of_def] >>
  Cases_on ‘p00’ >> gvs[sfa_def] >>
  Cases_on ‘p1’ >> simp[act_event_def, event_accepts_def, sfr_def] >>
  TRY (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def] >> rw[]) >>
  TRY (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >>
       simp[sfr_def, act_event_def, event_accepts_def, MAP_ZIP, fd_bytes_11]) >>
  simp[act_event_def, event_accepts_def] >> metis_tac[]
QED

Theorem SPLITP_LIST_REL[local]:
  ∀R P Q l1 l2. LIST_REL R l1 l2 ∧ (∀x y. R x y ⇒ (P x ⇔ Q y)) ⇒
          ∃i. SPLITP P l1 = (TAKE i l1, DROP i l1) ∧
              SPLITP Q l2 = (TAKE i l2, DROP i l2)
Proof
  ntac 3 gen_tac >> Induct >> simp[SPLITP] >> rpt strip_tac >> gvs[] >>
  rename1 ‘R h y’ >>
  Cases_on ‘Q y’
  >- (‘P h’ by metis_tac[] >> simp[SPLITP] >> qexists_tac ‘0’ >> simp[]) >>
  ‘¬P h’ by metis_tac[] >> simp[SPLITP] >>
  last_x_assum (qspec_then ‘ys’ mp_tac) >> simp[] >> strip_tac >>
  qexists_tac ‘SUC i’ >> simp[]
QED

Theorem LIST_REL_TAKE_DROP[local]:
  LIST_REL R l1 l2 ⇒
  LIST_REL R (TAKE i l1) (TAKE i l2) ∧ (DROP i l1 = [] ⇔ DROP i l2 = [])
Proof
  strip_tac >> imp_res_tac LIST_REL_LENGTH >>
  gvs[LIST_REL_EL_EQN, EL_TAKE, LENGTH_TAKE_EQ] >> rw[] >>
  gvs[DROP_NIL]
QED

Theorem fds_bdd_TAKE[local]:
  fds_bdd tt ⇒ fds_bdd (TAKE i tt)
Proof
  metis_tac[TAKE_DROP, fds_bdd_APPEND]
QED

Theorem owed_owed_m:
  LIST_REL R0 tt ps ∧ EVERY pok ps ∧ fds_bdd tt ⇒
  owed d (MAP aev ps) = bytes (owed_m (w2n d) tt)
Proof
  strip_tac >>
  ‘LIST_REL (λe p0. ∃p. e = aev p ∧ R0 p0 p) (MAP aev ps) tt’
    by (gvs[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]) >>
  qspecl_then [‘λe p0. ∃p. e = aev p ∧ R0 p0 p’, ‘event_accepts d’,
               ‘acc_of (w2n d)’, ‘MAP aev ps’, ‘tt’] mp_tac SPLITP_LIST_REL >>
  impl_tac >- (rw[] >> metis_tac[event_accepts_acc_of]) >>
  strip_tac >> simp[owed_def, owed_m_def] >>
  drule (Q.GEN ‘i’ LIST_REL_TAKE_DROP) >>
  disch_then (qspec_then ‘i’ strip_assume_tac) >>
  ‘DROP i (MAP aev ps) = [] ⇔ DROP i tt = []’
    by (imp_res_tac LIST_REL_LENGTH >> simp[DROP_NIL]) >>
  Cases_on ‘DROP i tt = []’ >> gvs[]
  >- gvs[DROP_LENGTH_TOO_LONG] >>
  Cases_on ‘DROP i (MAP aev ps)’ >> gvs[] >>
  Cases_on ‘DROP i tt’ >> gvs[] >>
  ‘EVERY pok (TAKE i ps)’ by gvs[EVERY_TAKE] >>
  ‘fds_bdd (TAKE i tt)’
    by (rpt strip_tac >> simp[] >> qpat_x_assum ‘∀fd. EXISTS _ tt ⇒ _’ irule >>
        metis_tac[TAKE_DROP, EXISTS_APPEND]) >>
  ‘LIST_REL (λp0 p. R0 p0 p) (TAKE i tt) (TAKE i ps)’
    by metis_tac[LIST_REL_TAKE_DROP] >>
  ‘relayed (MAP aev (TAKE i ps)) = bytes (lines_done (TAKE i tt))’
    by (irule relayed_lines_done >> metis_tac[]) >>
  ‘relayed (MAP aev ps) = bytes (lines_done tt)’
    by (irule relayed_lines_done >> simp[]) >>
  gvs[MAP_TAKE, MAP_DROP]
QED

(* ------------------------------------------------------------------------
   4. The chat server's trace
   ------------------------------------------------------------------------ *)

(* The chat server uses the socket API correctly *)
Theorem chat_server_uses_ok:
  uses_ok lfd (chat_server lfd)
Proof
  simp[uses_ok_def, chat_server_def] >> gen_tac >>
  simp[trans_with_tap, wf_chat_inner] >> simp[chat_inner_def] >>
  metis_tac[cserver_with_uses_accepted, chat_handler_on_fdc]
QED

Theorem MEM_accepted[local]:
  MEM (Accept l, SOME (Accepted fd)) tt ⇒ MEM fd (accepted tt)
Proof
  simp[accepted_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> strip_tac >>
  first_assum (irule_at Any) >> simp[]
QED

(* MAIN: ChatSpec's safety for the loop's trace of the chat server: in a
   world with one listener n2w lfdn and no connections, for any interest
   function, at every point of the run and for every connection d, what
   has been written to d is a prefix of what d is owed: the lines the
   server completed reading after it accepted d, in the order it
   completed them. *)
Theorem chat_comp_safe:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  chat_safe (LFLATTEN (LGENLIST
    (λi. fromList (grounds_events ifds (srelabel (chat_server lfdn)) s0 i))
    NONE))
Proof
  rw[chat_safe_def] >>
  qmatch_asmsub_abbrev_tac ‘LGENLIST (λi. fromList (ev i)) NONE’ >>
  ‘∀i. ev i ≠ []’ by simp[Abbr ‘ev’, grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  assume_tac (Q.INST [‘lfd’ |-> ‘lfdn’] chat_server_uses_ok) >>
  qabbrev_tac ‘m = chat_server lfdn’ >>
  drule_all gen_grun_ok >> disch_then (qspec_then ‘ifds’ assume_tac) >>
  drule_all gen_sinv >>
  disch_then (qspecl_then [‘ifds’, ‘SUC n’] strip_assume_tac) >>
  drule gen_trans_split >> strip_tac >>
  (* 1, 2: the non-poll events are those of a prefix of the performed pairs *)
  ONCE_REWRITE_TAC[GSYM bytes_written_to_FILTER, GSYM owed_FILTER] >>
  ‘FILTER np evs ≼ MAP aev (SPg m ifds s0 (SUC n))’
    by (drule_then (qspec_then ‘SUC n’ (SUBST1_TAC o SYM)) FILTER_rounds >>
        irule FILTER_prefix >> gvs[Abbr ‘ev’]) >>
  drule prefix_MAP_TAKE >>
  qabbrev_tac ‘k = LENGTH (FILTER np evs)’ >> disch_then SUBST1_TAC >>
  (* 3: the corresponding model prefix *)
  gvs[TREL_LIST_REL] >>
  drule (Q.GEN ‘i’ LIST_REL_TAKE_DROP) >>
  disch_then (qspec_then ‘k’ strip_assume_tac) >>
  ‘EVERY pok (TAKE k (SPg m ifds s0 (SUC n)))’
    by (irule EVERY_TAKE >> simp[EVERY_pok_gperf]) >>
  ‘fds_bdd (TSg m ifds s0 (SUC n))’ by metis_tac[gen_fds_bounded] >>
  ‘fds_bdd (TAKE k tt1)’
    by (rpt strip_tac >> qpat_x_assum ‘fds_bdd (TSg _ _ _ _)’ irule >>
        qpat_x_assum ‘TSg _ _ _ _ = _’ SUBST1_TAC >> simp[EXISTS_APPEND] >>
        disj1_tac >> metis_tac[TAKE_DROP, EXISTS_APPEND]) >>
  drule_all written_read_bytes >> disch_then (qspec_then ‘d’ strip_assume_tac) >>
  drule_all owed_owed_m >> disch_then (qspec_then ‘d’ SUBST1_TAC) >>
  simp[] >> irule bytes_prefix >>
  (* 4: the model's safety *)
  irule chat_server_safe >>
  qexistsl [‘MAP sfs (ghist ifds (srelabel m) s0 (SUC n))’, ‘lfdn’] >>
  simp[Abbr ‘m’] >> rpt conj_tac
  >~ [‘fresh _’]
  >- (qpat_x_assum ‘TSg _ _ _ _ = _’ (SUBST1_TAC o SYM) >>
      irule gen_fresh >> simp[] >> qexists_tac ‘lfdn’ >> simp[])
  >~ [‘fds_ok _’]
  >- (rewrite_tac[fds_ok_def] >> gen_tac >> strip_tac >> conj_tac >>
      rpt gen_tac >> strip_tac
      >- (‘on_fd fd p’
            by (rewrite_tac[on_fd_def] >> disj1_tac >> first_assum ACCEPT_TAC) >>
          ‘EXISTS (on_fd fd) (TSg (chat_server lfdn) ifds s0 (SUC n))’
            by (qpat_x_assum ‘TSg _ _ _ _ = _’ SUBST1_TAC >>
                rewrite_tac[EXISTS_MEM] >> qexists_tac ‘p’ >> conj_tac >>
                first_assum ACCEPT_TAC) >>
          qpat_x_assum ‘fds_bdd (TSg _ _ _ _)’ irule >> first_assum ACCEPT_TAC) >>
      ‘MEM fd (accepted (tt1 ++ tt2))’
        by (irule MEM_accepted >> qexists_tac ‘l’ >> gvs[]) >>
      drule TREL_NONE >> strip_tac >> drule accepted_NONE >> strip_tac >>
      ‘accepted tt1 = MAP w2n (wacc (SPg (chat_server lfdn) ifds s0 (SUC n)))’
        by (irule TREL_accepted >> simp[TREL_LIST_REL]) >>
      gvs[MEM_MAP] >> ‘w2n y < dimword(:64)’ by simp[w2n_lt] >> gvs[])
  >> TRY (qpat_x_assum ‘TSg _ _ _ _ = _’ SUBST1_TAC) >>
  simp[IS_PREFIX_APPEND] >> qexists_tac ‘DROP k tt1 ++ tt2’ >> simp[]
QED

(* The bridge for liveness: what a finite prefix of the trace owes d is
   what a prefix of the model transcript at the next round boundary owes *)
Theorem chat_owed_rounds:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  FLAT (GENLIST (grounds_events ifds (srelabel (chat_server lfdn)) s0) n) ≼ evs ∧
  evs ≼ FLAT (GENLIST (grounds_events ifds (srelabel (chat_server lfdn)) s0) (SUC n)) ⇒
  ∃U. U ≼ TSg (chat_server lfdn) ifds s0 (SUC n) ∧
      owed d evs = bytes (owed_m (w2n d) U)
Proof
  strip_tac >>
  assume_tac (Q.INST [‘lfd’ |-> ‘lfdn’] chat_server_uses_ok) >>
  qabbrev_tac ‘m = chat_server lfdn’ >>
  drule_all gen_grun_ok >> disch_then (qspec_then ‘ifds’ assume_tac) >>
  drule_all gen_sinv >>
  disch_then (qspecl_then [‘ifds’, ‘SUC n’] strip_assume_tac) >>
  drule gen_trans_split >> strip_tac >>
  ONCE_REWRITE_TAC[GSYM owed_FILTER] >>
  ‘FILTER np evs ≼ MAP aev (SPg m ifds s0 (SUC n))’
    by (drule_then (qspec_then ‘SUC n’ (SUBST1_TAC o SYM)) FILTER_rounds >>
        irule FILTER_prefix >> first_assum ACCEPT_TAC) >>
  drule prefix_MAP_TAKE >>
  qabbrev_tac ‘k = LENGTH (FILTER np evs)’ >> disch_then SUBST1_TAC >>
  gvs[TREL_LIST_REL] >>
  drule (Q.GEN ‘i’ LIST_REL_TAKE_DROP) >>
  disch_then (qspec_then ‘k’ strip_assume_tac) >>
  ‘EVERY pok (TAKE k (SPg m ifds s0 (SUC n)))’
    by (irule EVERY_TAKE >> simp[EVERY_pok_gperf]) >>
  ‘fds_bdd (TSg m ifds s0 (SUC n))’ by metis_tac[gen_fds_bounded] >>
  ‘fds_bdd (TAKE k tt1)’
    by (rpt strip_tac >> qpat_x_assum ‘fds_bdd (TSg _ _ _ _)’ irule >>
        qpat_x_assum ‘TSg _ _ _ _ = _’ SUBST1_TAC >> simp[EXISTS_APPEND] >>
        disj1_tac >> metis_tac[TAKE_DROP, EXISTS_APPEND]) >>
  qexists_tac ‘TAKE k tt1’ >>
  drule_all owed_owed_m >> disch_then (qspec_then ‘d’ SUBST1_TAC) >>
  qpat_x_assum ‘TSg _ _ _ _ = _’ SUBST1_TAC >>
  simp[IS_PREFIX_APPEND] >> qexists_tac ‘DROP k tt1 ++ tt2’ >> simp[]
QED
