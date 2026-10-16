(*
  The key-value server's connection handler, in the vocabulary of
  with_store (withStore, skeletonK).

     kv_handler (fd, buf):
       a complete request req at the front of buf
                       → query the store with Kv (fd, req), write the
                         printed answer, continue with the rest of buf;
       incomplete      → wait until fd is readable, read, continue;
       invalid         → stop.

  This is asyncHttpServerB's handler with the response computed by the
  store instead of by bhandle: one extra round per request (the query).

  MAIN: kv_handler_serves, the handler's invariant on any history.  It only
  touches fd; its queries are a prefix of the requests in what it has read;
  and what it has written is a prefix of the printed answers it got.
*)
Theory kvHandler
Ancestors
  pair list rich_list arithmetic option string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript echoServer
  echoServerSafety withStore skeletonK
  HttpGetSpec HttpHeadersSpec HttpSpec httpGetParse httpHeadersParse
  httpParse
Libs
  BasicProvers

Definition kv_body_def:
  kv_body r p =
    case p of
      (fd, buf) =>
        case parse_brequest buf of
          BComplete req rest =>
            bind (emit (Kv (fd, req))) (λa.
              case a of
                KvR ans =>
                  bind (emit (Sock (Write fd (print_response ans))))
                       (λw. r (fd, rest))
              | _ => return ())
        | BIncomplete =>
            bind (readable fd) (λu.
            bind (emit (Sock (Read fd))) (λres.
              case res of
                SockR (Data d) => r (fd, buf ++ d)
              | SockR Eof => return ()
              | _ => r (fd, buf)))
        | BInvalid => return ()
End

Theorem kv_body_contractive:
  contractive kv_body
Proof
  rw[contractive_def] >> PairCases_on ‘p’ >> simp[kv_body_def] >>
  Cases_on ‘parse_brequest p1’ >> simp[guarded_const]
  >- (ho_match_mp_tac guarded_bind >> simp[emit_needs_snapshot] >>
      gen_tac >> every_case_tac >> simp[nonexpansive_const] >>
      ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const, nonexpansive_call])
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> gen_tac >> every_case_tac >> simp[nonexpansive_call, nonexpansive_const]
QED

Definition kv_handler_def:
  kv_handler = fix kv_body
End

(* MAIN: the handler satisfies its recursive equation *)
Theorem kv_handler_unfold:
  kv_handler (fd, buf) =
    case parse_brequest buf of
      BComplete req rest =>
        bind (emit (Kv (fd, req))) (λa.
          case a of
            KvR ans =>
              bind (emit (Sock (Write fd (print_response ans))))
                   (λw. kv_handler (fd, rest))
          | _ => return ())
    | BIncomplete =>
        bind (readable fd) (λu.
        bind (emit (Sock (Read fd))) (λres.
          case res of
            SockR (Data d) => kv_handler (fd, buf ++ d)
          | SockR Eof => return ()
          | _ => kv_handler (fd, buf)))
    | BInvalid => return ()
Proof
  simp[kv_handler_def, Once (MATCH_MP fix_unfold kv_body_contractive)] >>
  simp[kv_body_def]
QED

Theorem wf_kv_handler:
  wf (kv_handler p)
Proof
  simp[kv_handler_def] >> irule wf_fix >> simp[kv_body_contractive] >>
  rw[] >> PairCases_on ‘p’ >> simp[kv_body_def] >> CASE_TAC >> simp[wf_return]
  >- (irule wf_bind >> simp[wf_emit] >> gen_tac >> every_case_tac >>
      simp[wf_return] >> irule wf_bind >> simp[wf_emit]) >>
  irule wf_bind >> simp[readable_def, wf_wait] >>
  irule wf_bind >> simp[wf_emit] >> gen_tac >> every_case_tac >> simp[wf_return]
QED

Theorem settled_kv_handler:
  settled (kv_handler p)
Proof
  simp[kv_handler_def] >> irule settled_fix >> simp[kv_body_contractive] >>
  rw[] >> PairCases_on ‘p’ >> simp[kv_body_def] >> CASE_TAC >> simp[settled_return]
  >- (irule settled_bind >> simp[wf_emit, settled_emit] >> gen_tac >>
      every_case_tac >> simp[settled_return] >>
      irule settled_bind >> simp[wf_emit, settled_emit]) >>
  irule settled_bind >> simp[readable_def, wf_wait, settled_wait] >>
  irule settled_bind >> simp[wf_emit, settled_emit] >> gen_tac >>
  every_case_tac >> simp[settled_return]
QED

(* ------------------------------------------------------------------------
   The invariant
   ------------------------------------------------------------------------ *)

(* Reads and writes of fd in an inner transcript *)
Definition readk_def:
  readk fd tr = read fd (untag tr)
End

Definition writtenk_def:
  writtenk fd tr = written fd (untag tr)
End

Theorem readk_writtenk_simps[simp]:
  readk fd [] = [] ∧ writtenk fd [] = [] ∧
  readk fd (l1 ++ l2) = readk fd l1 ++ readk fd l2 ∧
  writtenk fd (l1 ++ l2) = writtenk fd l1 ++ writtenk fd l2 ∧
  readk fd [(Kv q, r)] = [] ∧ writtenk fd [(Kv q, r)] = [] ∧
  readk fd [(Sock (Write g d), r)] = [] ∧
  writtenk fd [(Sock (Write g d), r)] = (if g = fd then [d] else []) ∧
  writtenk fd [(Sock (Read g), r)] = [] ∧
  readk fd [(Sock (Read fd), SOME (SockR r0))] =
    (case r0 of Data d => [d] | _ => []) ∧
  readk fd [(Sock (Read g), SOME (KvR b))] = [] ∧
  readk fd [(Sock (Read g), NONE)] = []
Proof
  simp[readk_def, writtenk_def, untag_def, read_def, written_def] >>
  every_case_tac >> simp[]
QED

Theorem readk_CONS:
  readk fd (p :: l) = readk fd [p] ++ readk fd l
Proof
  simp[readk_def, untag_def, read_def]
QED

Theorem writtenk_CONS:
  writtenk fd (p :: l) = writtenk fd [p] ++ writtenk fd l
Proof
  simp[writtenk_def, untag_def, written_def]
QED

Theorem kvs_CONS[simp]:
  kvs ((Kv q, r) :: l) = (q, r) :: kvs l ∧ kvs ((Sock a, r) :: l) = kvs l
Proof
  simp[kvs_def]
QED

(* The answers got, in order, until the first query without one *)
Definition got_def:
  got [] = [] ∧
  got ((q, SOME (KvR a)) :: E) = a :: got E ∧
  got (_ :: E) = []
End

(* MAIN: the handler's invariant, on any history hh *)
Theorem kv_handler_serves:
  ∀hh buf.
    EVERY (on_fdk fd) (trans (kv_handler (fd, buf)) hh) ∧
    MAP SND (queries (MAP FST (trans (kv_handler (fd, buf)) hh))) ≼
      parse_all_b (buf ++ CONCAT (readk fd (trans (kv_handler (fd, buf)) hh))) ∧
    writtenk fd (trans (kv_handler (fd, buf)) hh) ≼
      MAP print_response (got (kvs (trans (kv_handler (fd, buf)) hh)))
Proof
  gen_tac >> measureInduct_on ‘LENGTH hh’ >> gen_tac >>
  ONCE_REWRITE_TAC[kv_handler_unfold] >>
  Cases_on ‘parse_brequest buf’ >> simp[]
  >- ((* a complete request: query the store *)
      rename1 ‘BComplete req rest’ >>
      ‘∀X. parse_all_b (buf ++ X) = req :: parse_all_b (rest ++ X)’
        by (gen_tac >> irule parse_all_b_Complete >> simp[parse_bextend]) >>
      qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, req))) K0) hh’ >>
      qspecl_then [‘emit (Kv (fd, req))’, ‘K0’, ‘hh’] mp_tac
        (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
      simp[wf_emit, settled_emit] >> strip_tac
      >- simp[trans_emit, on_fdk_def, kvs_def, got_def] >>
      drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
      simp[on_fdk_def, Abbr ‘K0’] >>
      ONCE_REWRITE_TAC[readk_CONS, writtenk_CONS] >> simp[] >>
      Cases_on ‘x’ >> simp[got_def] >>
      qmatch_goalsub_abbrev_tac ‘trans (bind (emit Wr) K1) h2’ >>
      qspecl_then [‘emit Wr’, ‘K1’, ‘h2’] mp_tac
        (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
      simp[wf_emit, settled_emit] >> strip_tac
      >- (simp[trans_emit, Abbr ‘Wr’, on_fdk_def] >>
          simp[writtenk_def, readk_def, untag_def, written_def, read_def, kvs_def,
               got_def] >>
          every_case_tac >> simp[]) >>
      drule first_done_emit >> strip_tac >> gvs[trans_emit, Abbr ‘K1’, Abbr ‘Wr’] >>
      first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[] >>
      disch_then (qspec_then ‘rest’ strip_assume_tac) >>
      ONCE_REWRITE_TAC[readk_CONS, writtenk_CONS] >>
      simp[on_fdk_def] >>
      simp[readk_def, writtenk_def, untag_def, read_def, written_def] >>
      fs[readk_def, writtenk_def])
  (* incomplete: wait until fd is readable, read, continue *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable fd) K0) hh’
  >> qspecl_then [‘readable fd’, ‘K0’, ‘hh’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac
  >- simp[kvs_def, got_def]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Sock (Read fd))) K1) h2’
  >> qspecl_then [‘emit (Sock (Read fd))’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- (simp[trans_emit, on_fdk_def, kvs_def, got_def, readk_def, untag_def] >>
      every_case_tac >> simp[read_def])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’, on_fdk_def]
  >> ONCE_REWRITE_TAC[readk_CONS, writtenk_CONS]
  >> Cases_on ‘res’ >> simp[]
  >- (rename1 ‘SockR r0’ >> Cases_on ‘r0’ >> simp[]
      >> TRY (rename1 ‘Data d’ >>
              first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[] >>
              disch_then (qspec_then ‘buf ++ d’ strip_assume_tac) >> simp[] >>
              fs[] >> NO_TAC)
      >> TRY (simp[kvs_def, got_def] >> NO_TAC)
      >> first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[])
  >> first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[]
QED
