(*
  protoServer: the server for any framed request protocol, in the
  async model (design/32 §2.2, phase 2).  The HTTP handler with the
  protocol's parser P.parse and an arbitrary response function resp:

     proto_handler P resp (fd, buf) =
       case P.parse buf of
         PComplete req rest => write (resp req); continue with rest
       | PIncomplete        => wait until readable, read, continue
       | PInvalid           => stop

  The handler's body (proto_body) is a separate definition, so that a
  Level 2 version (server_with2) can reuse its shape.

  Proved once, for every P with proto_ok P and every resp:
  proto_handler_serves (one connection) and proto_server_safety (the
  whole server, every connection).
*)
Theory protoServer
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript echoServer
  echoServerSafety skeleton protoInterface
Libs
  BasicProvers

Definition proto_body_def:
  proto_body P resp r p =
    case p of
      (fd, buf) =>
        case P.parse buf of
          PComplete req rest =>
            bind (emit (Write fd (resp req))) (λw. r (fd, rest))
        | PIncomplete =>
            bind (readable fd) (λu.
            bind (emit (Read fd)) (λres.
              case res of
                Data d => r (fd, buf ++ d)
              | Eof => return ()
              | _ => r (fd, buf)))
        | PInvalid => return ()
End

Theorem proto_body_contractive:
  contractive (proto_body P resp)
Proof
  rw[contractive_def] >> PairCases_on ‘p’ >> simp[proto_body_def] >>
  Cases_on ‘P.parse p1’ >> simp[guarded_const]
  >- (ho_match_mp_tac guarded_bind >> simp[emit_needs_snapshot, nonexpansive_call])
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> Cases >> simp[nonexpansive_call, nonexpansive_const]
QED

Definition proto_handler_def:
  proto_handler P resp = fix (proto_body P resp)
End

(* MAIN: the handler satisfies its recursive equation *)
Theorem proto_handler_unfold:
  proto_handler P resp (fd, buf) =
    case P.parse buf of
      PComplete req rest =>
        bind (emit (Write fd (resp req))) (λw. proto_handler P resp (fd, rest))
    | PIncomplete =>
        bind (readable fd) (λu.
        bind (emit (Read fd)) (λres.
          case res of
            Data d => proto_handler P resp (fd, buf ++ d)
          | Eof => return ()
          | _ => proto_handler P resp (fd, buf)))
    | PInvalid => return ()
Proof
  simp[proto_handler_def, Once (MATCH_MP fix_unfold proto_body_contractive)]
  >> simp[proto_body_def]
QED

(* Any handler whose body is proto_body is proto_handler (fix is unique);
   used to re-derive the existing servers' theorems through this one *)
Theorem proto_handler_fix:
  (∀r p. b r p = proto_body P resp r p) ⇒ fix b = proto_handler P resp
Proof
  strip_tac >> ‘b = proto_body P resp’ by simp[FUN_EQ_THM] >>
  simp[proto_handler_def]
QED

Theorem wf_proto_handler:
  wf (proto_handler P resp p)
Proof
  simp[proto_handler_def] >> irule wf_fix >> simp[proto_body_contractive]
  >> rw[] >> PairCases_on ‘p’ >> simp[proto_body_def] >> CASE_TAC >> simp[wf_return]
  >- (irule wf_bind >> simp[wf_emit])
  >> irule wf_bind >> simp[readable_def, wf_wait]
  >> irule wf_bind >> simp[wf_emit] >> Cases >> simp[wf_return]
QED

Theorem settled_proto_handler:
  settled (proto_handler P resp p)
Proof
  simp[proto_handler_def] >> irule settled_fix >> simp[proto_body_contractive]
  >> rw[] >> PairCases_on ‘p’ >> simp[proto_body_def] >> CASE_TAC
  >> simp[settled_return]
  >- (irule settled_bind >> simp[wf_emit, settled_emit])
  >> irule settled_bind >> simp[readable_def, wf_wait, settled_wait]
  >> irule settled_bind >> simp[wf_emit, settled_emit] >> Cases
  >> simp[settled_return]
QED

(* The server: the echo server's skeleton with the protocol's handler *)
Definition proto_server_def:
  proto_server P resp lfd = server_with (λfd. proto_handler P resp (fd, "")) lfd
End

Theorem wf_proto_server:
  wf (proto_server P resp lfd)
Proof
  simp[proto_server_def] >> irule wf_server_with >> simp[wf_proto_handler]
QED

Theorem settled_proto_server:
  settled (proto_server P resp lfd)
Proof
  simp[proto_server_def] >> irule settled_server_with >>
  simp[wf_proto_handler, settled_proto_handler]
QED

(* ------------------------------------------------------------------------
   Safety
   ------------------------------------------------------------------------ *)

(* The intended responses to the complete requests at the front of s *)
Overload proto_responses_to = “λP resp s. MAP resp (proto_all P s)”

(* MAIN: one connection.  The handler only reads and writes its own fd, and
   what it has written is a prefix of the responses to the complete requests
   in its buffer followed by everything it has read. *)
Theorem proto_handler_serves:
  proto_ok P ⇒
  ∀fd hh buf.
    EVERY (on_fd fd) (trans (proto_handler P resp (fd, buf)) hh) ∧
    written fd (trans (proto_handler P resp (fd, buf)) hh) ≼
    proto_responses_to P resp
      (buf ++ CONCAT (read fd (trans (proto_handler P resp (fd, buf)) hh)))
Proof
  strip_tac >> gen_tac >> gen_tac >> measureInduct_on ‘LENGTH hh’ >> gen_tac >>
  ONCE_REWRITE_TAC[proto_handler_unfold] >>
  Cases_on ‘P.parse buf’ >> simp[]
  >- ((* a complete request: write its response, continue with the rest *)
      rename1 ‘PComplete req rest’ >>
      qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Write fd rsp)) K0) hh’ >>
      qspecl_then [‘emit (Write fd rsp)’, ‘K0’, ‘hh’] mp_tac
        (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
      simp[wf_emit, settled_emit] >> strip_tac
      >- (simp[trans_emit] >> drule_all proto_all_complete >> simp[Abbr ‘rsp’])
      >> drule first_done_emit >> strip_tac >> gvs[trans_emit, Abbr ‘K0’] >>
      first_x_assum (qspec_then ‘h2’ mp_tac) >> simp[] >>
      disch_then (qspec_then ‘rest’ strip_assume_tac) >> simp[] >>
      drule_all proto_extend >>
      disch_then (qspec_then ‘CONCAT (read fd (trans (proto_handler P resp (fd, rest)) h2))’ assume_tac) >>
      drule_all proto_all_complete >> simp[])
  (* incomplete: wait until fd is readable, read, continue *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable fd) K0) hh’
  >> qspecl_then [‘readable fd’, ‘K0’, ‘hh’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac >> simp[]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Read fd)) K1) h2’
  >> qspecl_then [‘emit (Read fd)’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- (simp[trans_emit] >> Cases_on ‘h2’ >> simp[]
      >> first_x_assum (qspec_then ‘1’ mp_tac) >> simp[emit_def]
      >> Cases_on ‘oHD h.results’ >> simp[])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’]
  >> Cases_on ‘res’ >> simp[]
  (* data d: continue with buf ++ d *)
  >> TRY (rename1 ‘Data d’ >>
          first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[] >>
          disch_then (qspec_then ‘buf ++ d’ strip_assume_tac) >> simp[] >>
          fs[GSYM APPEND_ASSOC] >> NO_TAC)
  (* would block, or a stray response: continue with buf *)
  >> first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[]
QED

(* MAIN: the whole server.  If the connections the world hands out are
   distinct, then on every connection fd, the strings the server has
   written to fd are a prefix of the responses to the complete requests it
   has read from fd so far, in order. *)
Theorem proto_server_safety:
  proto_ok P ∧ fresh (trans (proto_server P resp lfd) hh) ⇒
  ∀fd. written fd (trans (proto_server P resp lfd) hh) ≼
       proto_responses_to P resp (CONCAT (read fd (trans (proto_server P resp lfd) hh)))
Proof
  rw[proto_server_def] >>
  drule proto_handler_serves >> strip_tac >>
  mp_tac (server_with_isolates
          |> INST_TYPE [alpha |-> “:unit”]
          |> INST [mk_var ("h", “:num -> (event, echoServer$response) snapshot list ->
                                 (action, unit option) asyncCore$outcome”) |->
                   “λfd. proto_handler P resp (fd, "")”]
          |> BETA_RULE) >>
  impl_tac >- simp[] >>
  disch_then drule >> strip_tac >>
  qpat_x_assum ‘∀fd. FILTER _ _ = _ ∨ _’ (qspec_then ‘fd’ strip_assume_tac) >>
  ONCE_REWRITE_TAC[GSYM written_FILTER, GSYM read_FILTER] >> simp[]
  >> qpat_x_assum ‘∀resp fd hh buf. _’ (qspecl_then [‘resp’, ‘fd’, ‘L’, ‘""’] mp_tac)
  >> simp[]
QED

(* MAIN: the same in the spec's terms.  If what the server has read from fd
   is printed valid requests rs followed by a rest that does not start with
   a printed valid request, what it has written to fd is a prefix of the
   responses to rs. *)
Theorem proto_server_safety_requests:
  proto_ok P ∧ fresh (trans (proto_server P resp lfd) hh) ∧
  CONCAT (read fd (trans (proto_server P resp lfd) hh)) =
    FLAT (MAP P.print rs) ++ rest ∧
  EVERY P.valid rs ∧
  (∀r more. P.valid r ⇒ rest ≠ P.print r ++ more) ⇒
  written fd (trans (proto_server P resp lfd) hh) ≼ MAP resp rs
Proof
  strip_tac >> drule_all proto_server_safety >>
  disch_then (qspec_then ‘fd’ mp_tac) >> simp[proto_all_requests]
QED
