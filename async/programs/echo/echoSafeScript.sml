(*
  EchoSpec's safety, for the loop's trace of the echo server (any
  interest function).

  For a world with one listener n2w lfdn (nothing pending) and no
  connections, the loop running  srelabel (server lfdn)  produces the
  trace  io = LFLATTEN (LGENLIST (λi. fromList (grounds_events ...)) NONE)
  (M4's dynamic-interest loop, or M3's fixed one).  echo_comp_safe:
  echo_safe io, i.e. at every point of the run and on every connection,
  the bytes written are a prefix of the bytes read.

  The chain, at a prefix evs of io lying between round boundaries n and
  n + 1 (LPREFIX_rounds_between):
     written_to c evs ≼ written_to c (rounds 0..n)       [monotone]
                      = bytes (written (w2n c) TS_n)       [events = performed pairs = model]
                      = bytes (read (w2n c) TS_n)          [echo_server_safety, echo_fresh]
                      = read_from c (rounds 0..n-1)         [model = performed pairs = events]
                      ≼ read_from c evs                     [monotone]
  where TS_n is the model server's transcript on the (translated)
  history of the first n rounds, whose last round has its writes but not
  yet its reads' responses.
*)
Theory echoSafe
Ancestors
  words asyncCore asyncLevel1 asyncLevel2 asyncTranscript echoServer
  echoServerSafety echoServerUses relabel relabelDist
  socketWorld loopPollWorld loopRounds loopSockInv
  echoSockModel loopRoundsTrans echoRunOk EchoSpec llist
Libs
  preamble

(* The bytes a socket-transcript pair wrote to / read from c *)
Definition owritten_def:
  owritten c (Write c' bs, ro : sresp option) = (if c' = c then bs else []) ∧
  owritten c _ = []
End

Definition oread_def:
  oread c (Read c' n, SOME (Got (SOME d))) = (if c' = c then d else []) ∧
  oread c _ = []
End

Overload bytes = “λs:string. MAP ((n2w : num -> word8) o ORD) s”

(* MAIN (helper): through the relabelling, the bytes written to / read
   from c in the socket transcript are those of the model transcript on
   fd w2n c, provided every fd the model touches fits in 64 bits. *)
Theorem TREL_written_read:
  ∀tt us. TREL tt us ∧ (∀fd. EXISTS (on_fd fd) tt ⇒ fd < dimword(:64)) ⇒
          FLAT (MAP (owritten c) us) = bytes (FLAT (written (w2n c) tt)) ∧
          FLAT (MAP (oread c) us) = bytes (FLAT (read (w2n c) tt))
Proof
  Induct >- (Cases >> simp[]) >>
  rpt gen_tac >> Cases_on ‘us’ >> simp[] >>
  PairCases_on ‘h’ >> PairCases_on ‘h'’ >> simp[] >> strip_tac >>
  first_x_assum (qspec_then ‘t’ mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  strip_tac >>
  gvs[] >> Cases_on ‘h0’ >> gvs[sfa_def, owritten_def, oread_def]
  >- ((* Read fd *)
      qmatch_goalsub_rename_tac ‘(Read fd, OPTION_MAP sfr _) :: _’ >>
      Cases_on ‘h'1’ >> gvs[oread_def] >>
      rename1 ‘SOME r’ >> Cases_on ‘r’ >> gvs[sfr_def, oread_def] >>
      TRY (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >> gvs[sfr_def]) >>
      rename1 ‘Got ro’ >> Cases_on ‘ro’ >> gvs[sfr_def, oread_def] >>
      rw[] >> gvs[bytes_round_trip, n2w_w2n] >>
      qpat_x_assum ‘∀fd'. _ ⇒ _’ (qspec_then ‘fd’ mp_tac) >> simp[] >>
      rw[] >> gvs[n2w_w2n])
  >- ((* Write fd d *)
      rename1 ‘if n2w fd = c then _ else _’ >>
      rw[] >> gvs[n2w_w2n] >>
      qpat_x_assum ‘∀fd'. _ ⇒ _’ (qspec_then ‘fd’ mp_tac) >> simp[] >>
      rw[] >> gvs[n2w_w2n])
  >> simp[owritten_def, oread_def]
QED

Theorem acc_first_accepted[local]:
  ∀tt. acc_first fd tt ∧ EXISTS (on_fd fd) tt ⇒ MEM fd (accepted tt)
Proof
  Induct >> simp[acc_first_def] >> rpt gen_tac >>
  Cases_on ‘accepts fd h’ >> simp[]
  >- (strip_tac >> gvs[accepts_def, accepted_def]) >>
  strip_tac >> gvs[] >> PairCases_on ‘h’ >>
  Cases_on ‘h0’ >> Cases_on ‘h1’ >> simp[] >> TRY CASE_TAC >> simp[]
QED

(* Every fd the model server touches was handed out by the world *)
Theorem echo_fds_bounded:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀fd. EXISTS (on_fd fd) (TS lfdn ifds s0 n) ⇒ fd < dimword(:64)
Proof
  rpt strip_tac >>
  mp_tac echo_sinv >> impl_tac >- fs[] >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule echo_trans_split >> strip_tac >>
  qspec_then ‘MAP sfs (ghist ifds (srelabel (server lfdn)) s0 n)’
    strip_assume_tac (Q.INST [‘lfd’ |-> ‘lfdn’] server_uses_accepted) >>
  ‘MEM fd (accepted (TS lfdn ifds s0 n))’
    by (irule acc_first_accepted >> simp[]) >>
  drule TREL_accepted >> drule TREL_NONE >> rpt strip_tac >>
  gvs[accepted_NONE, MEM_MAP] >>
  qspec_then ‘y’ mp_tac w2n_lt >> simp[]
QED

(* The socket transcript at round n, in terms of the performed pairs *)
Theorem owritten_rounds[local]:
  grun_ok ifds m s0 ⇒
  FLAT (MAP (owritten c)
         (MAP (λ(a, r). (a, SOME r)) (gperf ifds m s0 n) ++
          MAP (λa. (a, NONE)) (gacts ifds m s0 n))) =
  FLAT (MAP (pwritten c) (gperf ifds m s0 (SUC n)))
Proof
  strip_tac >> simp[gperf_SUC, MAP_MAP_o, combinTheory.o_DEF] >>
  ‘∀ps. MAP (λx. owritten c ((λ(a, r). (a, SOME r)) x)) ps = MAP (pwritten c) ps’
    by (Induct >> simp[FORALL_PROD] >> Cases >> simp[owritten_def, pwritten_def]) >>
  simp[] >>
  ‘∀as rs. LENGTH rs = LENGTH as ⇒
           MAP (λa. owritten c (a, NONE)) as = MAP (pwritten c) (ZIP (as, rs))’
    by (Induct >> simp[] >> Cases_on ‘rs’ >> simp[] >>
        Cases >> simp[owritten_def, pwritten_def]) >>
  AP_TERM_TAC >> first_x_assum irule >> metis_tac[LENGTH_gres]
QED

Theorem oread_rounds[local]:
  FLAT (MAP (oread c)
         (MAP (λ(a, r). (a, SOME r)) ps ++ MAP (λa. (a, NONE)) as)) =
  FLAT (MAP (pread c) ps)
Proof
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  ‘∀as. FLAT (MAP (λa. oread c (a, NONE)) as) = []’
    by (Induct >> simp[] >> Cases >> simp[oread_def]) >>
  simp[] >> AP_TERM_TAC >> simp[MAP_EQ_f, FORALL_PROD] >>
  Cases >> simp[oread_def, pread_def] >> Cases >> simp[oread_def, pread_def] >>
  rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[oread_def, pread_def]
QED

(* MAIN: at every round boundary n, on every connection c, the bytes
   written in rounds 0..n are exactly the bytes read in rounds 0..n-1 *)
Theorem echo_rounds_written_read:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  bytes_written_to c
    (FLAT (GENLIST (grounds_events ifds (srelabel (server lfdn)) s0) (SUC n))) =
  bytes_read_from c
    (FLAT (GENLIST (grounds_events ifds (srelabel (server lfdn)) s0) n))
Proof
  strip_tac >> drule echo_grun_ok >> disch_then (qspec_then ‘ifds’ assume_tac) >>
  simp[bytes_written_to_rounds, bytes_read_from_rounds] >>
  mp_tac echo_sinv >> impl_tac >- fs[] >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule echo_trans_split >> strip_tac >>
  ‘TREL (tt1 ++ tt2)
     (MAP (λ(a, r). (a, SOME r)) (SP lfdn ifds s0 n) ++
      MAP (λa. (a, NONE)) (SA lfdn ifds s0 n))’
    by (simp[MAP_APPEND] >> metis_tac[]) >>
  drule_then (qspec_then ‘c’ mp_tac) TREL_written_read >>
  impl_tac >- (qpat_x_assum ‘_ = tt1 ++ tt2’ (SUBST1_TAC o SYM) >>
               metis_tac[echo_fds_bounded]) >>
  simp[owritten_rounds, oread_rounds] >> strip_tac >>
  qspecl_then [‘MAP sfs (ghist ifds (srelabel (server lfdn)) s0 n)’, ‘lfdn’]
    mp_tac (Q.GENL [‘h’, ‘lfd’] echo_server_safety) >>
  impl_tac >- metis_tac[echo_fresh] >>
  simp[] >> disch_then (qspec_then ‘w2n c’ mp_tac) >>
  disch_then (fn th => REWRITE_TAC[GSYM MAP_APPEND, GSYM FLAT_APPEND, th])
QED

(* MAIN: EchoSpec's safety for the echo server's trace: in a world with
   one listener n2w lfdn and no connections, for any interest function,
   at every point of the run and on every connection, the bytes the
   server has written are a prefix of the bytes it has read. *)
Theorem echo_comp_safe:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  echo_safe (LFLATTEN (LGENLIST
    (λi. fromList (grounds_events ifds (srelabel (server lfdn)) s0 i)) NONE))
Proof
  rw[echo_safe_def] >>
  qmatch_asmsub_abbrev_tac ‘LGENLIST (λi. fromList (ev i)) NONE’ >>
  ‘∀i. ev i ≠ []’ by simp[Abbr ‘ev’, grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  irule IS_PREFIX_TRANS >>
  qexists_tac ‘bytes_read_from c (FLAT (GENLIST ev n))’ >>
  simp[bytes_read_from_mono] >>
  irule IS_PREFIX_TRANS >>
  qexists_tac ‘bytes_written_to c (FLAT (GENLIST ev (SUC n)))’ >>
  simp[bytes_written_to_mono, Abbr ‘ev’] >>
  drule echo_rounds_written_read >> simp[]
QED
