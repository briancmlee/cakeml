(*
  asyncProtoSafe: the generic proto_safe for the loop's trace of
  proto_server (any interest function), proved once for every protocol
  with proto_ok (design/32 §2.2, phase 2).  asyncHttpSafeH's chain, with
  the protocol's preqs / presps / no_full:
     written_to c evs ≼ written_to c (rounds 0..n)
                      = bytes (written (w2n c) TT)                        [gen_rounds_bytes]
                      ≼ bytes (proto_responses_to P resp (read (w2n c) TT)) [proto_server_safety, gen_fresh]
                      ≼ bytes (proto_responses_to P resp s)               [proto_all_prefix]
                      = presps resp rs                                    [proto_all_requests]
*)
Theory asyncProtoSafe
Ancestors
  words asyncCore asyncLevel1 asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncM4ServerUses asyncM4Relabel asyncM4RelabelDist
  ffiSpikeSocketFFI asyncM3World asyncM4GRounds asyncM4SockInv
  asyncM4SockModel asyncM4GTrans asyncM4EchoRunOk asyncM4EchoSafe EchoSpec
  asyncServerWith HttpSpec asyncServerWithUses asyncRunOkGen
  asyncProto asyncProtoServer llist
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

(* The server uses the socket API correctly *)
Theorem proto_server_uses_accepted:
  proto_ok P ⇒
  ∀hh. accepts_on lfd (trans (proto_server P resp lfd) hh) ∧
       ∀fd. acc_first fd (trans (proto_server P resp lfd) hh)
Proof
  strip_tac >> simp[proto_server_def] >> gen_tac >>
  irule server_with_uses_accepted >> simp[] >>
  metis_tac[proto_handler_serves]
QED

(* ------------------------------------------------------------------------
   proto_safe for the loop's trace
   ------------------------------------------------------------------------ *)

(* What has been read, as complete requests rs and a rest without a full
   request, parses to exactly rs *)
Theorem read_requests_parse[local]:
  proto_ok P ∧
  MAP ((n2w : num -> word8) o ORD) s = preqs P rs ++ rest ∧
  EVERY P.valid rs ∧ no_full P rest ⇒
  proto_all P s = rs
Proof
  rw[preqs_def, bytes_def] >> drule bytes_split >> strip_tac >> gvs[] >>
  irule proto_all_requests >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[no_full_def] >> first_x_assum drule >>
  simp[preqs_def, bytes_def, IS_PREFIX_APPEND]
QED

(* MAIN: safety for the server's trace, for every protocol: in a world with
   one listener n2w lfdn and no connections, for any interest function, at
   every point of the run and on every connection, if the bytes read so
   far are complete valid requests rs followed by a rest without a full
   request, the bytes written are a prefix of the responses to rs. *)
Theorem proto_comp_safe:
  proto_ok P ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  proto_safe P resp (LFLATTEN (LGENLIST
    (λi. fromList (grounds_events ifds (srelabel (proto_server P resp lfdn)) s0 i))
    NONE))
Proof
  rw[proto_safe_def] >>
  qmatch_asmsub_abbrev_tac ‘LGENLIST (λi. fromList (ev i)) NONE’ >>
  ‘∀i. ev i ≠ []’ by simp[Abbr ‘ev’, grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  ‘uses_ok lfdn (proto_server P resp lfdn)’
    by simp[uses_ok_def, proto_server_uses_accepted] >>
  drule_all gen_rounds_bytes >>
  disch_then (qspecl_then [‘n’, ‘ifds’, ‘c’] strip_assume_tac) >>
  ‘fresh (trans (proto_server P resp lfdn)
           (MAP sfs (ghist ifds (srelabel (proto_server P resp lfdn)) s0 n)))’
    by metis_tac[gen_fresh] >>
  drule_all proto_server_safety >> disch_then (qspec_then ‘w2n c’ assume_tac) >>
  qabbrev_tac ‘TT = trans (proto_server P resp lfdn)
                      (MAP sfs (ghist ifds (srelabel (proto_server P resp lfdn)) s0 n))’ >>
  (* what was read, as a string *)
  qabbrev_tac ‘s = MAP (CHR o w2n) (bytes_read_from c evs)’ >>
  ‘MAP ((n2w : num -> word8) o ORD) s = bytes_read_from c evs’
    by simp[Abbr ‘s’, chars_of_bytes] >>
  ‘proto_all P s = rs’ by (irule read_requests_parse >> gvs[]) >>
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
  gvs[Abbr ‘ev’, presps_def, bytes_def] >>
  simp[bytes_prefix] >>
  irule IS_PREFIX_TRANS >>
  qexists_tac ‘FLAT (MAP resp (proto_all P (FLAT (read (w2n c) TT))))’ >>
  rpt conj_tac >>
  FIRST [irule prefix_FLAT >> gvs[] >> NO_TAC,
         irule prefix_FLAT >> irule prefix_MAP >> irule proto_all_prefix >>
         simp[]]
QED
