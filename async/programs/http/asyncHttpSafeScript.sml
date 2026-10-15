(*
  HttpSpec's safety, for the loop's trace of the HTTP server (any interest
  function): the HTTP analogue of asyncM4EchoSafe's echo_comp_safe.

  For a world with one listener n2w lfdn (nothing pending) and no
  connections, the loop running  srelabel (http_server files lfdn)
  produces the trace  io = LFLATTEN (LGENLIST (λi. fromList (grounds_events ...)) NONE).
  http_comp_safe: http_safe files io.

  The chain, at a prefix evs of io lying between round boundaries n and
  n + 1 (LPREFIX_rounds_between), on connection c, where TS is the model
  server's transcript on the translated history of n rounds and
  s is evs's read bytes as a string (so  s = print_request rs ++ rest'):
     written_to c evs ≼ written_to c (rounds 0..n)
                      = bytes (written (w2n c) TS)              [gen_rounds_bytes]
                      ≼ bytes (responses_to files (read (w2n c) TS))
                                                               [http_server_safety, gen_fresh]
                      ≼ bytes (responses_to files s)            [read (w2n c) TS ≼ s; parse_all_mono]
                      = responses files rs                      [parse_all_requests]
*)
Theory asyncHttpSafe
Ancestors
  words asyncCore asyncLevel1 asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncM4ServerUses asyncM4Relabel asyncM4RelabelDist
  ffiSpikeSocketFFI asyncM3World asyncM4GRounds asyncM4SockInv
  asyncM4SockModel asyncM4GTrans asyncM4EchoRunOk asyncM4EchoSafe EchoSpec
  asyncServerWith HttpSpec asyncHttpParse asyncHttpServer asyncServerWithUses
  asyncRunOkGen llist
Libs
  preamble

(* ------------------------------------------------------------------------
   Strings and bytes
   ------------------------------------------------------------------------ *)

Theorem bytes_11[local]:
  ∀s t. MAP ((n2w : num -> word8) o ORD) s = MAP (n2w o ORD) t ⇔ s = t
Proof
  Induct >> Cases_on ‘t’ >> simp[] >> rpt strip_tac >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >>
  simp[ORD_11] >> metis_tac[ORD_11]
QED

Theorem bytes_prefix[local]:
  ∀s t. MAP ((n2w : num -> word8) o ORD) s ≼ MAP (n2w o ORD) t ⇔ s ≼ t
Proof
  Induct >> Cases_on ‘t’ >> simp[] >> rpt strip_tac >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >>
  simp[] >> metis_tac[ORD_11]
QED

Theorem chars_of_bytes[local]:
  MAP ((n2w : num -> word8) o ORD) (MAP (CHR o w2n) (bs : word8 list)) = bs
Proof
  simp[bytes_round_trip]
QED

(* bytes s = bytes p ++ rest splits s *)
Theorem bytes_split[local]:
  ∀p s rest. MAP ((n2w : num -> word8) o ORD) s = MAP (n2w o ORD) p ++ rest ⇒
             ∃s'. s = p ++ s' ∧ MAP (n2w o ORD) s' = rest
Proof
  Induct >> simp[] >> rpt strip_tac >> Cases_on ‘s’ >> gvs[] >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >> gvs[ORD_11] >>
  metis_tac[]
QED

Theorem prefix_FLAT[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ FLAT l1 ≼ FLAT l2
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[]
QED

Theorem prefix_MAP[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ MAP f l1 ≼ MAP f l2
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The parser is monotone
   ------------------------------------------------------------------------ *)

(* MAIN (helper): reading more can only add complete requests at the end *)
Theorem parse_all_mono:
  ∀s t. parse_all s ≼ parse_all (s ++ t)
Proof
  gen_tac >> completeInduct_on ‘LENGTH s’ >> rw[] >>
  Cases_on ‘parse_request s’ >> simp[Once parse_all_def] >>
  drule parse_extend >> disch_then (qspec_then ‘t’ assume_tac) >>
  simp[Once parse_all_def] >>
  ‘STRLEN s' < STRLEN s’ by metis_tac[parse_complete_shorter] >>
  first_x_assum (qspec_then ‘STRLEN s'’ mp_tac) >> simp[]
QED

Theorem parse_all_prefix[local]:
  s ≼ t ⇒ parse_all s ≼ parse_all t
Proof
  rw[] >> gvs[IS_PREFIX_APPEND] >>
  metis_tac[parse_all_mono, IS_PREFIX_APPEND]
QED

(* ------------------------------------------------------------------------
   http_safe for the loop's trace
   ------------------------------------------------------------------------ *)

(* What has been read, as complete requests rs and a rest without a full
   request, parses to exactly rs *)
Theorem read_requests_parse[local]:
  MAP ((n2w : num -> word8) o ORD) s = requests rs ++ rest ∧
  EVERY valid_request rs ∧ no_full_request rest ⇒
  parse_all s = rs
Proof
  rw[requests_def, bytes_def] >> drule bytes_split >> strip_tac >> gvs[] >>
  irule parse_all_requests >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[no_full_request_def] >> first_x_assum drule >>
  simp[requests_def, bytes_def, IS_PREFIX_APPEND]
QED

(* MAIN: HttpSpec's safety for the HTTP server's trace: in a world with one
   listener n2w lfdn and no connections, for any interest function, at
   every point of the run and on every connection, if the bytes read so
   far are complete valid requests rs followed by a rest without a full
   request, the bytes written are a prefix of the responses to rs. *)
Theorem http_comp_safe:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  http_safe files (LFLATTEN (LGENLIST
    (λi. fromList (grounds_events ifds (srelabel (http_server files lfdn)) s0 i))
    NONE))
Proof
  rw[http_safe_def] >>
  qmatch_asmsub_abbrev_tac ‘LGENLIST (λi. fromList (ev i)) NONE’ >>
  ‘∀i. ev i ≠ []’ by simp[Abbr ‘ev’, grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  ‘uses_ok lfdn (http_server files lfdn)’
    by simp[uses_ok_def, http_server_uses_accepted] >>
  drule_all gen_rounds_bytes >>
  disch_then (qspecl_then [‘n’, ‘ifds’, ‘c’] strip_assume_tac) >>
  ‘fresh (trans (http_server files lfdn)
           (MAP sfs (ghist ifds (srelabel (http_server files lfdn)) s0 n)))’
    by metis_tac[gen_fresh] >>
  drule http_server_safety >> disch_then (qspec_then ‘w2n c’ assume_tac) >>
  qabbrev_tac ‘TT = trans (http_server files lfdn)
                      (MAP sfs (ghist ifds (srelabel (http_server files lfdn)) s0 n))’ >>
  (* what was read, as a string *)
  qabbrev_tac ‘s = MAP (CHR o w2n) (bytes_read_from c evs)’ >>
  ‘MAP ((n2w : num -> word8) o ORD) s = bytes_read_from c evs’
    by simp[Abbr ‘s’, chars_of_bytes] >>
  ‘parse_all s = rs’ by (irule read_requests_parse >> gvs[]) >>
  ‘FLAT (read (w2n c) TT) ≼ s’
    by (‘bytes_read_from c (FLAT (GENLIST ev n)) =
         MAP (n2w o ORD) (FLAT (read (w2n c) TT))’ by fs[Abbr ‘ev’] >>
        ONCE_REWRITE_TAC[GSYM bytes_prefix] >>
        pop_assum (SUBST1_TAC o SYM) >>
        qpat_x_assum ‘MAP _ s = _’ SUBST1_TAC >>
        irule bytes_read_from_mono >> simp[]) >>
  (* the chain *)
  irule IS_PREFIX_TRANS >>
  qexists_tac ‘bytes_written_to c (FLAT (GENLIST ev (SUC n)))’ >>
  simp[bytes_written_to_mono] >>
  gvs[Abbr ‘ev’, responses_def, bytes_def] >>
  simp[bytes_prefix] >>
  irule IS_PREFIX_TRANS >>
  qexists_tac ‘FLAT (MAP (print_response o handle files) (parse_all (FLAT (read (w2n c) TT))))’ >>
  rpt conj_tac >>
  FIRST [irule prefix_FLAT >> gvs[] >> NO_TAC,
         irule prefix_FLAT >> irule prefix_MAP >> irule parse_all_prefix >>
         simp[]]
QED
