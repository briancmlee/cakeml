(*
  HttpKvSpec's safety (linearizability) for the loop's trace of the
  key-value server, kv_server (asyncKvModel), in any interest function.

  At a point evs of the trace, between the starts of rounds n and n+1:
   - the order: the queries the store has answered by round n, in the
     order it answered them (kv_queries), followed by the complete
     requests not queried yet, connection by connection;
   - commit points: a query first answered in round k commits at the start
     of round k (the position LENGTH (rounds 0..k-1) in the trace); a
     request not queried yet commits at the end of evs;
   - commit points give real time, because a query of round k reads its
     request in rounds < k and its response is written in rounds > k.

  The construction is asyncKvOrderGen's kv_safeG_rounds, once for every
  key view; kv_comp_safe is its instance per connection (keys word64,
  projections bytes_read_from / bytes_written_to, the model's fd w2n c).
  This file supplies the instance's round facts (kv_rounds).

  The bridge between model rounds and trace positions is asyncRunOkGen's
  gen_rounds_bytes, used at every round k ≤ n: the bytes read in rounds
  < k are those of the transcript after k rounds, the bytes written in
  rounds ≤ k those of the transcript after k rounds.
*)
Theory asyncKvSafe
Ancestors
  words asyncCore asyncLevel1 asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncM4ServerUses asyncM4Relabel asyncM4RelabelDist
  ffiSpikeSocketFFI asyncM3World asyncM4GRounds asyncM4SockInv
  asyncM4SockModel asyncM4GTrans asyncRunOkGen EchoSpec HttpSpec
  HttpSpecBodies HttpKvSpec asyncHttpParse asyncHttpParseH asyncHttpParseB
  asyncWithStore asyncServerWithK asyncKvHandler asyncKvModel asyncKvOrder
  asyncKvLabel asyncKvTraceLemmas asyncKvOrderGen llist ffi
Libs
  preamble

(* ------------------------------------------------------------------------
   Lists
   ------------------------------------------------------------------------ *)

Theorem prefix_MAP[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ MAP f l1 ≼ MAP f l2
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[]
QED

(* Connections of fds below 2^64, as words *)
(* A connection with something read appears in the trace's read events *)
Definition ev_conn_def:
  ev_conn (IO_event f conf b) = bytes_fd conf
End

Theorem conns_of_trace[local]:
  ∃CS. ALL_DISTINCT CS ∧ ∀c. bytes_read_from c evs ≠ [] ⇒ MEM c CS
Proof
  qexists_tac ‘nub (MAP ev_conn evs)’ >> simp[all_distinct_nub] >>
  rw[bytes_read_from_def] >> gs[FLAT_EQ_NIL, EVERY_MEM, MEM_MAP] >>
  rename1 ‘MEM ev evs’ >> qexists_tac ‘ev’ >> simp[] >>
  Cases_on ‘ev’ >> rename1 ‘IO_event f conf b’ >> Cases_on ‘f’ >>
  gvs[event_read_def, ev_conn_def] >> every_case_tac >> gvs[]
QED

Theorem read_on_fd[local]:
  ∀tr. FLAT (read fd tr) ≠ [] ⇒ EXISTS (on_fd fd) tr
Proof
  Induct >> simp[read_def] >> PairCases >> simp[] >>
  every_case_tac >> rw[] >> gvs[GSYM read_def, on_fd_def]
QED

(* ------------------------------------------------------------------------
   The theorem
   ------------------------------------------------------------------------ *)

(* The server's rounds, in the loop's run *)
Overload KEV = “λlfdn ifds s0. grounds_events ifds (srelabel (kv_server lfdn)) s0”
Overload KHH = “λlfdn ifds s0 k. MAP sfs (ghist ifds (srelabel (kv_server lfdn)) s0 k)”
Overload KTS = “λlfdn ifds s0 k. trans (kv_server lfdn) (KHH lfdn ifds s0 k)”
Overload KG = “λlfdn ifds s0 k. kv_queries lfdn (KHH lfdn ifds s0 k)”
Overload KP = “λlfdn ifds s0 k. FLAT (GENLIST (KEV lfdn ifds s0) k)”

(* The bridge, at every round *)
Theorem kv_rounds_bytes[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  bytes_written_to c (KP lfdn ifds s0 (SUC k)) =
    HttpSpec$bytes (FLAT (written (w2n c) (KTS lfdn ifds s0 k))) ∧
  bytes_read_from c (KP lfdn ifds s0 k) =
    HttpSpec$bytes (FLAT (read (w2n c) (KTS lfdn ifds s0 k)))
Proof
  strip_tac >>
  ‘uses_ok lfdn (kv_server lfdn)’ by simp[kv_server_uses_ok] >>
  drule_all gen_rounds_bytes >>
  disch_then (qspecl_then [‘k’, ‘ifds’, ‘c’] mp_tac) >> simp[bytes_def]
QED

Theorem kv_rounds_fresh[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  fresh (KTS lfdn ifds s0 k)
Proof
  strip_tac >> ‘uses_ok lfdn (kv_server lfdn)’ by simp[kv_server_uses_ok] >>
  drule_all gen_fresh >> simp[]
QED

Theorem kv_rounds_serves[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  MAP SND (FILTER (λq. FST q = fd) (KG lfdn ifds s0 k)) ≼
    parse_all_b (FLAT (read fd (KTS lfdn ifds s0 k))) ∧
  written fd (KTS lfdn ifds s0 k) ≼
    MAP print_response (fd_answers fd (KG lfdn ifds s0 k))
Proof
  strip_tac >> irule kv_server_serves >> simp[kv_rounds_fresh]
QED

Theorem kv_rounds_mono[local]:
  k1 ≤ k2 ⇒
  KG lfdn ifds s0 k1 ≼ KG lfdn ifds s0 k2 ∧ KP lfdn ifds s0 k1 ≼ KP lfdn ifds s0 k2
Proof
  strip_tac >> conj_tac
  >- (‘KHH lfdn ifds s0 k1 = TAKE k1 (KHH lfdn ifds s0 k2)’
        by simp[GSYM MAP_TAKE, ghist_TAKE] >>
      pop_assum SUBST1_TAC >> simp[kv_queries_TAKE]) >>
  irule FLAT_GENLIST_prefix >> simp[]
QED

Theorem kv_rounds_bounded[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ MEM q (KG lfdn ifds s0 k) ⇒
  FST q < dimword(:64)
Proof
  strip_tac >>
  ‘MAP SND (FILTER (λq'. FST q' = FST q) (KG lfdn ifds s0 k)) ≼
   parse_all_b (FLAT (read (FST q) (KTS lfdn ifds s0 k)))’
    by metis_tac[kv_rounds_serves] >>
  ‘FLAT (read (FST q) (KTS lfdn ifds s0 k)) ≠ []’
    by (strip_tac >> fs[parse_all_b_NIL] >>
        fs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  drule read_on_fd >> strip_tac >>
  ‘uses_ok lfdn (kv_server lfdn)’ by simp[kv_server_uses_ok] >>
  drule_all gen_fds_bounded >> simp[]
QED

(* MAIN: HttpKvSpec's safety for the key-value server's trace: in a world
   with one listener n2w lfdn and no connections, for any interest
   function, the trace is linearizable *)
Theorem kv_comp_safe:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  kv_safe (LFLATTEN (LGENLIST
    (λi. fromList (grounds_events ifds (srelabel (kv_server lfdn)) s0 i)) NONE))
Proof
  strip_tac >> REWRITE_TAC[kv_safe_G] >>
  qspecl_then [‘bytes_read_from’, ‘bytes_written_to’, ‘KEV lfdn ifds s0’,
               ‘KG lfdn ifds s0’, ‘λk c. FLAT (read (w2n c) (KTS lfdn ifds s0 k))’,
               ‘λk c. written (w2n c) (KTS lfdn ifds s0 k)’, ‘n2w’, ‘w2n’] mp_tac
    (Q.GENL [‘RD’, ‘WR’, ‘EV’, ‘G’, ‘RS’, ‘WS’, ‘kmap’, ‘kinv’] kv_safeG_rounds) >>
  impl_tac >- (
    rw[kv_rounds_def]
    >- simp[grounds_events_alt]
    >- metis_tac[kv_rounds_mono]
    >- metis_tac[bytes_read_from_prefix]
    >- metis_tac[bytes_written_to_prefix]
    >- simp[bytes_written_to_def]
    >- metis_tac[kv_rounds_bytes]
    >- metis_tac[kv_rounds_bytes]
    >- metis_tac[kv_rounds_serves]
    >- metis_tac[kv_rounds_serves]
    >- (‘FST q < dimword(:64)’ by metis_tac[kv_rounds_bounded] >> fs[])
    >> metis_tac[conns_of_trace]) >>
  simp[]
QED
