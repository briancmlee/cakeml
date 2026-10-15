(*
  Liveness of the header-tolerant HTTP server's I/O, against HttpSpecHeaders'
  http_live_h, for the event loop's run in the socket world (the trace of
  http_semantics_prog_headers):

     io = LFLATTEN (LGENLIST (λi. fromList (grounds_events (EI lfdn)
                      (srelabel (http_server_h files lfdn)) s0 i)) NONE)

  The route is spike/m4-liveness's for echo (asyncM4Drain, asyncM4EchoLive):
   - a connection with data sent on it is eventually handed out to the
     server (sw_conn_accepted, asyncSWSock);
   - after that, its handler runs on its own history g (sw_handler_view),
     and the machine-level theorem with bounded reads (hmachine_live_p,
     asyncHttpDrainH) applies; its environment facts come from the socket
     world: readiness is reported truthfully (ready_EL_ghist), a read of a
     connection with unread data reads something (sock_acts_read_nonempty),
     end-of-file comes after all the data (grounds_eof), and what has been
     read is a prefix of what was sent (grounds_acct).
*)
Theory asyncHttpLiveH
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words string
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec HttpSpec
  HttpSpecHeaders asyncM3World asyncM4GRounds asyncM4Relabel asyncM4RelabelDist
  asyncM4SockModel asyncM4SockInv asyncM4GTrans asyncM4Loop asyncM4EchoRunOk
  asyncM4Sched asyncM4Account asyncM4LiveProg asyncM4LiveWorld asyncM4ReadSoon
  asyncM4Queue asyncM4AcceptSoon asyncM4Drain asyncRunOkGen asyncServerWith
  asyncSWProgress asyncSWSock asyncHttpParseH asyncHttpServerH asyncHttpSafeH
  asyncHttpParseHExt asyncHttpMachineH asyncHttpDrainH
Libs
  preamble

(* The server, its socket-vocabulary version, and the loop's rounds *)
Overload HM = “λfiles lfdn. http_server_h files lfdn”
Overload HG = “λfiles lfdn s0 k. gstate (EI lfdn) (srelabel (http_server_h files lfdn)) s0 k”
Overload HP = “λfiles lfdn s0 k. gperf (EI lfdn) (srelabel (http_server_h files lfdn)) s0 k”
Overload HA_ = “λfiles lfdn s0 k. gacts (EI lfdn) (srelabel (http_server_h files lfdn)) s0 k”
Overload HH = “λfiles lfdn s0 k. MAP sfs (ghist (EI lfdn) (srelabel (http_server_h files lfdn)) s0 k)”
Overload HEV = “λfiles lfdn s0. grounds_events (EI lfdn) (srelabel (http_server_h files lfdn)) s0”

(* ------------------------------------------------------------------------
   The server is well behaved
   ------------------------------------------------------------------------ *)

Theorem hok_http_h:
  hok (λfd. http_handler_h files (fd, ""))
Proof
  simp[hok_def, wf_http_handler_h, settled_http_handler_h, http_handler_serves_h]
QED

Theorem uses_ok_http_h:
  uses_ok lfd (http_server_h files lfd)
Proof
  simp[uses_ok_def, http_server_h_uses_accepted]
QED

Theorem grun_ok_http_h:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  grun_ok (EI lfdn) (srelabel (http_server_h files lfdn)) s0
Proof
  strip_tac >> irule gen_grun_ok >> metis_tac[uses_ok_http_h]
QED

(* ------------------------------------------------------------------------
   Strings and bytes
   ------------------------------------------------------------------------ *)

Theorem LENGTH_bytes[simp]:
  LENGTH (bytes s) = LENGTH s
Proof
  simp[bytes_def]
QED

Theorem bytes_APPEND[simp]:
  bytes (s ++ t) = bytes s ++ bytes t
Proof
  simp[bytes_def]
QED

(* bytes is injective character by character, so it preserves and
   reflects prefixes *)
Theorem bytes_prefix:
  ∀s t. bytes s ≼ bytes t ⇔ s ≼ t
Proof
  Induct >> simp[bytes_def] >> gen_tac >> Cases >> simp[] >>
  ‘∀c. ORD c < 256’ by simp[ORD_BOUND] >>
  ‘(n2w (ORD h) : word8 = n2w (ORD h')) ⇔ h = h'’
    by (simp[n2w_11, ORD_11] >> metis_tac[ORD_11]) >>
  fs[bytes_def]
QED

(* ------------------------------------------------------------------------
   What has been sent on c, against what the server has read from it
   ------------------------------------------------------------------------ *)

(* grounds_acct, in the form used below *)
Theorem sent_split:
  s0.conns = [] ∧ sched_wf s0 ∧ grun_ok ifds m s0 ⇒
  ∃inc. sent_upto c k s0 = pread_all c (gperf ifds m s0 k) ++ inc ∧
        (∀cn. ALOOKUP (gstate ifds m s0 k).conns c = SOME cn ⇒ inc = cn.incoming) ∧
        (ALOOKUP (gstate ifds m s0 k).conns c = NONE ⇒ inc = [])
Proof
  strip_tac >> drule_all grounds_acct >> disch_then (qspecl_then [‘c’, ‘k’] mp_tac) >>
  simp[acct_def] >> CASE_TAC >> simp[]
QED

(* ------------------------------------------------------------------------
   The handler of c, on the loop's rounds
   ------------------------------------------------------------------------ *)

(* MAIN: c, handed out by round n, is served by its own handler, running on
   a history g from the round a ≤ n in which c was handed out; at round
   a + j the handler has read what the server has read from c, and has
   written what the server's events up to the end of round a + j wrote *)
Theorem http_h_view:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (HP files lfdn s0 n)) ∧ n ≤ M ⇒
  ∃a g. a ≤ n ∧ LENGTH g + a = M ∧ prompt (hcomp files (w2n c) (HA "")) g ∧
    (∀i. i < LENGTH g ⇒ (EL i g).ready = (EL (a + i) (HH files lfdn s0 M)).ready) ∧
    ∀j. j ≤ LENGTH g ⇒
      FILTER (on_fd (w2n c)) (TSg (http_server_h files lfdn) (EI lfdn) s0 (a + j)) =
        trans (hcomp files (w2n c) (HA "")) (TAKE j g) ∧
      bytes (Rj files (w2n c) g j) = pread_all c (HP files lfdn s0 (a + j)) ∧
      bytes (FLAT (Wj files (w2n c) g j)) =
        bytes_written_to c (FLAT (GENLIST (HEV files lfdn s0) (SUC (a + j))))
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (srelabel (http_server_h files lfdn)) s0’
    by metis_tac[grun_ok_http_h] >>
  ‘∀k. k ≤ M ⇒ TAKE k (HH files lfdn s0 M) = HH files lfdn s0 k’
    by simp[GSYM MAP_TAKE, ghist_TAKE] >>
  ‘∀k. accepted (TSg (http_server_h files lfdn) (EI lfdn) s0 k) =
       MAP w2n (wacc (HP files lfdn s0 k))’
    by metis_tac[TSg_accepted, uses_ok_http_h] >>
  ‘MEM c (wacc (HP files lfdn s0 M))’
    by (irule wacc_mono >> qexists_tac ‘n’ >> simp[]) >>
  qspec_then ‘HH files lfdn s0 M’ mp_tac
    (Q.INST [‘fd’ |-> ‘w2n (c : word64)’, ‘lfd’ |-> ‘lfdn’] sw_handler_view
     |> Q.GEN ‘hf’ |> Q.ISPEC ‘λfd. http_handler_h files (fd, "")’) >>
  simp[GSYM http_server_h_def, hok_http_h] >>
  impl_tac
  >- (rpt conj_tac
      >- metis_tac[gen_fresh, uses_ok_http_h]
      >- (irule prompt_ghist >> simp[])
      >> simp[MEM_MAP] >> metis_tac[]) >>
  strip_tac >>
  ‘a ≤ n’
    by (first_x_assum (qspec_then ‘n’ mp_tac) >> simp[MEM_MAP] >> metis_tac[]) >>
  qexists_tac ‘a’ >> qexists_tac ‘g’ >> simp[hcomp_def] >>
  rpt gen_tac >> strip_tac >>
  ‘FILTER (on_fd (w2n c)) (TSg (http_server_h files lfdn) (EI lfdn) s0 (a + j)) =
   trans (http_handler_h files (w2n c, "")) (TAKE j g)’
    by (‘a + j ≤ M’ by fs[] >>
        ‘TAKE (a + j) (HH files lfdn s0 M) = HH files lfdn s0 (a + j)’ by fs[] >>
        qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER _ _ = _’ (qspec_then ‘j’ mp_tac) >>
        asm_rewrite_tac[] >> simp[]) >>
  simp[] >> pop_assum (SUBST1_TAC o SYM) >>
  simp[read_FILTER, written_FILTER] >>
  ‘bytes_read_from c (FLAT (GENLIST (HEV files lfdn s0) (a + j))) =
   pread_all c (HP files lfdn s0 (a + j))’
    by (irule bytes_read_from_rounds >> first_assum ACCEPT_TAC) >>
  (* gen_rounds_bytes's bytes is asyncM4EchoSafe's overload, MAP (n2w o ORD) *)
  mp_tac (Q.INST [‘n’ |-> ‘a + j : num’] gen_rounds_bytes
          |> Q.GENL [‘m’, ‘ifds’]
          |> Q.ISPEC ‘http_server_h files lfdn’ |> Q.SPEC ‘EI lfdn’) >>
  impl_tac >- simp[uses_ok_http_h] >> strip_tac >>
  simp[bytes_def] >> metis_tac[]
QED
