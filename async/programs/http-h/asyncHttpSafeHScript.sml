(*
  HttpSpecHeaders' safety, for the loop's trace of the header-tolerant HTTP
  server (any interest function): asyncHttpSafe's http_comp_safe for
  http_server_h, with HttpSpecHeaders' hrequests / hresponses /
  no_full_hrequest in place of HttpSpec's.  The chain is the same:
     written_to c evs ≼ written_to c (rounds 0..n)
                      = bytes (written (w2n c) TT)                     [gen_rounds_bytes]
                      ≼ bytes (responses_to_h files (read (w2n c) TT)) [http_server_safety_h, gen_fresh]
                      ≼ bytes (responses_to_h files s)                 [parse_all_h_mono]
                      = hresponses files rs                            [parse_all_hrequests]
*)
Theory asyncHttpSafeH
Ancestors
  words asyncCore asyncLevel1 asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncM4ServerUses asyncM4Relabel asyncM4RelabelDist
  ffiSpikeSocketFFI asyncM3World asyncM4GRounds asyncM4SockInv
  asyncM4SockModel asyncM4GTrans asyncM4EchoRunOk asyncM4EchoSafe EchoSpec
  asyncServerWith HttpSpec asyncHttpParse asyncHttpServer asyncServerWithUses
  asyncRunOkGen HttpSpecHeaders asyncHttpParseH asyncHttpServerH llist
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

(* The header-tolerant server uses the socket API correctly *)
Theorem http_server_h_uses_accepted:
  ∀hh. accepts_on lfd (trans (http_server_h files lfd) hh) ∧
       ∀fd. acc_first fd (trans (http_server_h files lfd) hh)
Proof
  simp[http_server_h_def] >> gen_tac >>
  irule server_with_uses_accepted >> simp[] >>
  metis_tac[http_handler_serves_h]
QED

Theorem parse_all_h_prefix[local]:
  s ≼ t ⇒ parse_all_h s ≼ parse_all_h t
Proof
  rw[] >> gvs[IS_PREFIX_APPEND] >>
  metis_tac[parse_all_h_mono, IS_PREFIX_APPEND]
QED

(* ------------------------------------------------------------------------
   http_safe for the loop's trace
   ------------------------------------------------------------------------ *)

(* What has been read, as complete requests rs and a rest without a full
   request, parses to exactly rs *)
Theorem read_hrequests_parse[local]:
  MAP ((n2w : num -> word8) o ORD) s = hrequests rs ++ rest ∧
  EVERY valid_hrequest rs ∧ no_full_hrequest rest ⇒
  parse_all_h s = rs
Proof
  rw[hrequests_def, bytes_def] >> drule bytes_split >> strip_tac >> gvs[] >>
  irule parse_all_hrequests >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[no_full_hrequest_def] >> first_x_assum drule >>
  simp[hrequests_def, bytes_def, IS_PREFIX_APPEND]
QED

(* MAIN: HttpSpecHeaders' safety for the HTTP server's trace: in a world with one
   listener n2w lfdn and no connections, for any interest function, at
   every point of the run and on every connection, if the bytes read so
   far are complete valid requests rs (with any headers) followed by a rest without a full
   request, the bytes written are a prefix of the responses to rs. *)
Theorem http_comp_safe_h:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  http_safe_h files (LFLATTEN (LGENLIST
    (λi. fromList (grounds_events ifds (srelabel (http_server_h files lfdn)) s0 i))
    NONE))
Proof
  rw[http_safe_h_def] >>
  qmatch_asmsub_abbrev_tac ‘LGENLIST (λi. fromList (ev i)) NONE’ >>
  ‘∀i. ev i ≠ []’ by simp[Abbr ‘ev’, grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  ‘uses_ok lfdn (http_server_h files lfdn)’
    by simp[uses_ok_def, http_server_h_uses_accepted] >>
  drule_all gen_rounds_bytes >>
  disch_then (qspecl_then [‘n’, ‘ifds’, ‘c’] strip_assume_tac) >>
  ‘fresh (trans (http_server_h files lfdn)
           (MAP sfs (ghist ifds (srelabel (http_server_h files lfdn)) s0 n)))’
    by metis_tac[gen_fresh] >>
  drule http_server_safety_h >> disch_then (qspec_then ‘w2n c’ assume_tac) >>
  qabbrev_tac ‘TT = trans (http_server_h files lfdn)
                      (MAP sfs (ghist ifds (srelabel (http_server_h files lfdn)) s0 n))’ >>
  (* what was read, as a string *)
  qabbrev_tac ‘s = MAP (CHR o w2n) (bytes_read_from c evs)’ >>
  ‘MAP ((n2w : num -> word8) o ORD) s = bytes_read_from c evs’
    by simp[Abbr ‘s’, chars_of_bytes] >>
  ‘parse_all_h s = rs’ by (irule read_hrequests_parse >> gvs[]) >>
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
  gvs[Abbr ‘ev’, hresponses_def, bytes_def] >>
  simp[bytes_prefix] >>
  irule IS_PREFIX_TRANS >>
  qexists_tac ‘FLAT (MAP (print_response o handle files o hpath) (parse_all_h (FLAT (read (w2n c) TT))))’ >>
  rpt conj_tac >>
  FIRST [irule prefix_FLAT >> gvs[] >> NO_TAC,
         irule prefix_FLAT >> irule prefix_MAP >> irule parse_all_h_prefix >>
         simp[]]
QED
