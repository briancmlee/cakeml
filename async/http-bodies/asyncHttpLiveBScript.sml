(*
  Liveness of the bodies HTTP server's I/O, against HttpSpecBodies'
  http_live_b, for the event loop's run in the socket world (the trace of
  http_semantics_prog_bodies):

     io = LFLATTEN (LGENLIST (λi. fromList (grounds_events (EI lfdn)
                      (srelabel (http_server_b files lfdn)) s0 i)) NONE)

  The route is spike/m4-liveness's for echo (asyncM4Drain, asyncM4EchoLive):
   - a connection with data sent on it is eventually handed out to the
     server (sw_conn_accepted, asyncSWSock);
   - after that, its handler runs on its own history g (sw_handler_view),
     and the machine-level theorem with bounded reads (hmachine_live_p,
     asyncHttpDrainB) applies; its environment facts come from the socket
     world: readiness is reported truthfully (ready_EL_ghist), a read of a
     connection with unread data reads something (sock_acts_read_nonempty),
     end-of-file comes after all the data (grounds_eof), and what has been
     read is a prefix of what was sent (grounds_acct).
*)
Theory asyncHttpLiveB
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words string
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec HttpSpec
  HttpSpecHeaders HttpSpecBodies asyncHttpParseB asyncM3World asyncM4GRounds asyncM4Relabel asyncM4RelabelDist
  asyncM4SockModel asyncM4SockInv asyncM4GTrans asyncM4Loop asyncM4EchoRunOk
  asyncM4Sched asyncM4Account asyncM4LiveProg asyncM4LiveWorld asyncM4ReadSoon
  asyncM4Queue asyncM4AcceptSoon asyncM4Drain asyncRunOkGen asyncServerWith
  asyncSWProgress asyncSWSock asyncHttpParseH asyncHttpServerB asyncHttpSafeB
  asyncHttpParseBExt asyncHttpMachineB asyncHttpDrainB
Libs
  preamble

(* The server, its socket-vocabulary version, and the loop's rounds *)
Overload HM = “λfiles lfdn. http_server_b files lfdn”
Overload HG = “λfiles lfdn s0 k. gstate (EI lfdn) (srelabel (http_server_b files lfdn)) s0 k”
Overload HP = “λfiles lfdn s0 k. gperf (EI lfdn) (srelabel (http_server_b files lfdn)) s0 k”
Overload HA_ = “λfiles lfdn s0 k. gacts (EI lfdn) (srelabel (http_server_b files lfdn)) s0 k”
Overload HH = “λfiles lfdn s0 k. MAP sfs (ghist (EI lfdn) (srelabel (http_server_b files lfdn)) s0 k)”
Overload HEV = “λfiles lfdn s0. grounds_events (EI lfdn) (srelabel (http_server_b files lfdn)) s0”

(* ------------------------------------------------------------------------
   The server is well behaved
   ------------------------------------------------------------------------ *)

Theorem hok_http_b:
  hok (λfd. http_handler_b files (fd, ""))
Proof
  simp[hok_def, wf_http_handler_b, settled_http_handler_b, http_handler_serves_b]
QED

Theorem uses_ok_http_b:
  uses_ok lfd (http_server_b files lfd)
Proof
  simp[uses_ok_def, http_server_b_uses_accepted]
QED

Theorem grun_ok_http_b:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  grun_ok (EI lfdn) (srelabel (http_server_b files lfdn)) s0
Proof
  strip_tac >> irule gen_grun_ok >> metis_tac[uses_ok_http_b]
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
Theorem http_b_view:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (HP files lfdn s0 n)) ∧ n ≤ M ⇒
  ∃a g. a ≤ n ∧ LENGTH g + a = M ∧ prompt (hcomp files (w2n c) (HA "")) g ∧
    (∀i. i < LENGTH g ⇒ (EL i g).ready = (EL (a + i) (HH files lfdn s0 M)).ready) ∧
    ∀j. j ≤ LENGTH g ⇒
      FILTER (on_fd (w2n c)) (TSg (http_server_b files lfdn) (EI lfdn) s0 (a + j)) =
        trans (hcomp files (w2n c) (HA "")) (TAKE j g) ∧
      bytes (Rj files (w2n c) g j) = pread_all c (HP files lfdn s0 (a + j)) ∧
      bytes (FLAT (Wj files (w2n c) g j)) =
        bytes_written_to c (FLAT (GENLIST (HEV files lfdn s0) (SUC (a + j))))
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (srelabel (http_server_b files lfdn)) s0’
    by metis_tac[grun_ok_http_b] >>
  ‘∀k. k ≤ M ⇒ TAKE k (HH files lfdn s0 M) = HH files lfdn s0 k’
    by simp[GSYM MAP_TAKE, ghist_TAKE] >>
  ‘∀k. accepted (TSg (http_server_b files lfdn) (EI lfdn) s0 k) =
       MAP w2n (wacc (HP files lfdn s0 k))’
    by metis_tac[TSg_accepted, uses_ok_http_b] >>
  ‘MEM c (wacc (HP files lfdn s0 M))’
    by (irule wacc_mono >> qexists_tac ‘n’ >> simp[]) >>
  qspec_then ‘HH files lfdn s0 M’ mp_tac
    (Q.INST [‘fd’ |-> ‘w2n (c : word64)’, ‘lfd’ |-> ‘lfdn’] sw_handler_view
     |> Q.GEN ‘hf’ |> Q.ISPEC ‘λfd. http_handler_b files (fd, "")’) >>
  simp[GSYM http_server_b_def, hok_http_b] >>
  impl_tac
  >- (rpt conj_tac
      >- metis_tac[gen_fresh, uses_ok_http_b]
      >- (irule prompt_ghist >> simp[])
      >> simp[MEM_MAP] >> metis_tac[]) >>
  strip_tac >>
  ‘a ≤ n’
    by (first_x_assum (qspec_then ‘n’ mp_tac) >> simp[MEM_MAP] >> metis_tac[]) >>
  qexists_tac ‘a’ >> qexists_tac ‘g’ >> simp[hcomp_def] >>
  rpt gen_tac >> strip_tac >>
  ‘FILTER (on_fd (w2n c)) (TSg (http_server_b files lfdn) (EI lfdn) s0 (a + j)) =
   trans (http_handler_b files (w2n c, "")) (TAKE j g)’
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
          |> Q.ISPEC ‘http_server_b files lfdn’ |> Q.SPEC ‘EI lfdn’) >>
  impl_tac >- simp[uses_ok_http_b] >> strip_tac >>
  simp[bytes_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Liveness on an accepted connection
   ------------------------------------------------------------------------ *)

(* MAIN: on a connection c handed out by round n, the responses to the
   complete requests in any prefix D of what was sent on c by round n are
   eventually written to c *)
Theorem http_accepted_live_b:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ MEM c (wacc (HP files lfdn s0 n)) ∧
  bytes D ≼ sent_upto c n s0 ⇒
  ∃N. bytes (FLAT (responses_to_b files D)) ≼
      bytes_written_to c (FLAT (GENLIST (HEV files lfdn s0) N))
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (srelabel (http_server_b files lfdn)) s0’
    by metis_tac[grun_ok_http_b] >>
  qabbrev_tac ‘B = (LENGTH D + 2) * (LENGTH (parse_all_b D) + 3)’ >>
  mp_tac (Q.INST [‘M’ |-> ‘n + B : num’] http_b_view) >> impl_tac >- simp[] >>
  strip_tac >>
  qabbrev_tac ‘fd = w2n (c : word64)’ >>
  ‘n2w fd = c’ by simp[Abbr ‘fd’] >>
  qabbrev_tac ‘j0 = n − a’ >>
  (* what was sent on c, round by round, against what the handler read *)
  ‘∀j. j ≤ LENGTH g ⇒
       ∃inc. sent_upto c (a + j) s0 = bytes (Rj files fd g j) ++ inc ∧
             (∀cn. ALOOKUP (HG files lfdn s0 (a + j)).conns c = SOME cn ⇒
                   inc = cn.incoming) ∧
             (ALOOKUP (HG files lfdn s0 (a + j)).conns c = NONE ⇒ inc = [])’
    by (rpt strip_tac >>
        mp_tac (Q.GEN ‘m’ sent_split |> Q.ISPEC ‘srelabel (http_server_b files lfdn)’
                |> Q.INST [‘ifds’ |-> ‘EI lfdn’, ‘k’ |-> ‘a + j : num’]) >>
        simp[] >> metis_tac[]) >>
  (* from round n on, D has been sent *)
  ‘∀j. j0 ≤ j ⇒ bytes D ≼ sent_upto c (a + j) s0’
    by (rpt strip_tac >> irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c n s0’ >>
        simp[] >> ‘a + j = n + (a + j − n)’ by simp[Abbr ‘j0’] >>
        pop_assum SUBST1_TAC >> simp[sent_upto_prefix]) >>
  (* the machine-level theorem *)
  mp_tac hmachine_live_p >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      (* what has been read and D are comparable *)
      >- (rpt strip_tac >> REWRITE_TAC[GSYM bytes_prefix] >>
          first_x_assum (qspec_then ‘j’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
          first_x_assum (qspec_then ‘j’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
          metis_tac[prefixes_is_prefix_total, IS_PREFIX_APPEND3, IS_PREFIX_TRANS])
      (* not reported readable: nothing unread, so D has been read *)
      >- (rpt strip_tac >>
          ‘a + j < n + B ∧ j + 1 ≤ LENGTH g ∧ j0 ≤ j + 1 ∧ j < LENGTH g’ by fs[] >>
          ‘Rj files fd g (j + 1) = Rj files fd g j’
            by (drule_all Rj_Wj_SUC >> fs[ADD1]) >>
          ‘MEM c (wacc (HP files lfdn s0 (a + j)))’
            by (irule wacc_mono >> qexists_tac ‘n’ >> fs[Abbr ‘j0’]) >>
          ‘MEM c (EI lfdn (ghist (EI lfdn) (srelabel (HM files lfdn)) s0 (a + j)))’
            by (irule interest_accepted >> simp[]) >>
          ‘¬is_ready (HG files lfdn s0 (a + (j + 1))) c’
            by (strip_tac >> qpat_x_assum ‘Readable fd ∉ _’ mp_tac >>
                qpat_x_assum ‘∀i. i < LENGTH g ⇒ _’ (qspec_then ‘j’ mp_tac) >>
                impl_tac >- simp[] >> disch_then SUBST1_TAC >>
                simp[EL_MAP, snap_map_def, sfe_def, ready_EL_ghist, MEM_FILTER] >>
                qexists_tac ‘c’ >> fs[Abbr ‘fd’, ADD1]) >>
          qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ ∃inc. _’ (qspec_then ‘j + 1’ mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          ‘inc = []’
            by (Cases_on ‘ALOOKUP (HG files lfdn s0 (a + (j + 1))).conns c’ >> fs[] >>
                fs[is_ready_def] >> gvs[]) >>
          qpat_x_assum ‘∀j. j0 ≤ j ⇒ bytes D ≼ _’ (qspec_then ‘j + 1’ mp_tac) >>
          impl_tac >- simp[] >>
          qpat_x_assum ‘sent_upto _ _ _ = _’ SUBST1_TAC >>
          qpat_x_assum ‘Rj _ _ _ (j + 1) = _’ SUBST1_TAC >>
          qpat_x_assum ‘inc = []’ SUBST1_TAC >>
          REWRITE_TAC[APPEND_NIL, bytes_prefix])
      (* a read, with D not all read: there was unread data, so it reads some *)
      >- (rpt strip_tac >> disj2_tac >>
          ‘j ≤ LENGTH g ∧ j + 1 ≤ LENGTH g ∧ j0 ≤ j’ by fs[] >>
          drule_all hmachine_reading >> strip_tac >>
          qpat_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER _ _ = _ ∧ _’ (qspec_then ‘j’ mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          ‘MEM (Read fd, NONE) (TSg (HM files lfdn) (EI lfdn) s0 (a + j))’
            by (qpat_x_assum ‘FILTER _ _ = _’ (fn th =>
                  qpat_x_assum ‘MEM _ (trans _ _)’ (mp_tac o REWRITE_RULE [GSYM th])) >>
                simp[MEM_FILTER]) >>
          ‘reads_c c (HA_ files lfdn s0 (a + j))’
            by (qpat_x_assum ‘n2w fd = c’ (SUBST1_TAC o SYM) >>
                irule TSg_read_none >> metis_tac[uses_ok_http_b]) >>
          qpat_assum ‘∀j. j ≤ LENGTH g ⇒ ∃inc. _’ (qspec_then ‘j’ mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          ‘inc ≠ []’
            by (strip_tac >> qpat_x_assum ‘¬(D ≼ _)’ mp_tac >>
                REWRITE_TAC[GSYM bytes_prefix] >>
                qpat_x_assum ‘∀j. j0 ≤ j ⇒ bytes D ≼ _’ (qspec_then ‘j’ mp_tac) >>
                impl_tac >- simp[] >>
                qpat_x_assum ‘sent_upto _ _ _ = _’ SUBST1_TAC >>
                qpat_x_assum ‘inc = []’ SUBST1_TAC >>
                REWRITE_TAC[APPEND_NIL] >> metis_tac[]) >>
          ‘∃cn. ALOOKUP (HG files lfdn s0 (a + j)).conns c = SOME cn ∧ cn.incoming ≠ []’
            by (Cases_on ‘ALOOKUP (HG files lfdn s0 (a + j)).conns c’ >- fs[] >>
                qpat_x_assum ‘∀cn. _ ⇒ inc = _’ (qspec_then ‘x’ mp_tac) >> simp[] >>
                strip_tac >> fs[]) >>
          drule grun_ok_sock_acts >>
          disch_then (qspec_then ‘a + j’ strip_assume_tac) >>
          drule_all sock_acts_read_nonempty >> strip_tac >>
          qpat_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER _ _ = _ ∧ _’ (qspec_then ‘j + 1’ mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          ‘STRLEN (Rj files fd g j) = LENGTH (pread_all c (HP files lfdn s0 (a + j))) ∧
           STRLEN (Rj files fd g (SUC j)) =
             LENGTH (pread_all c (HP files lfdn s0 (a + j + 1)))’
            by metis_tac[LENGTH_bytes, ADD1, ADD_ASSOC] >>
          simp[GSYM ADD1, gperf_SUC] >>
          Cases_on ‘pread_all c (ZIP (gacts (EI lfdn) (srelabel (HM files lfdn)) s0 (a + j),
                                      gres (EI lfdn) (srelabel (HM files lfdn)) s0 (a + j)))’ >>
          fs[])
      (* stopped at end-of-file: nothing unread, so D has been read *)
      >> rpt strip_tac >>
      ‘parse_brequest b ≠ BInvalid’ by simp[] >>
      drule_all hmachine_eof >> strip_tac >>
      qpat_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER _ _ = _ ∧ _’ (qspec_then ‘j’ mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      ‘MEM (Read fd, SOME Eof) (TSg (HM files lfdn) (EI lfdn) s0 (a + j))’
        by (qpat_x_assum ‘FILTER _ _ = _’ (fn th =>
              qpat_x_assum ‘MEM _ (trans _ _)’ (mp_tac o REWRITE_RULE [GSYM th])) >>
            simp[MEM_FILTER]) >>
      ‘∃k. MEM (Read c k, Got (SOME [])) (HP files lfdn s0 (a + j))’
        by (qpat_x_assum ‘n2w fd = c’ (SUBST1_TAC o SYM) >>
            irule TSg_eof >> metis_tac[uses_ok_http_b]) >>
      ‘∃cn. ALOOKUP (HG files lfdn s0 (a + j)).conns c = SOME cn ∧ cn.incoming = []’
        by metis_tac[grounds_eof] >>
      qpat_assum ‘∀j. j ≤ LENGTH g ⇒ ∃inc. _’ (qspec_then ‘j’ mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      ‘inc = []’ by metis_tac[] >>
      qpat_x_assum ‘∀j. j0 ≤ j ⇒ bytes D ≼ _’ (qspec_then ‘j’ mp_tac) >>
      impl_tac >- simp[] >>
      qpat_x_assum ‘sent_upto _ _ _ = _’ SUBST1_TAC >>
      qpat_x_assum ‘inc = []’ SUBST1_TAC >>
      REWRITE_TAC[APPEND_NIL, bytes_prefix]) >>
  disch_then (qspecl_then [‘LENGTH D’, ‘j0’] mp_tac) >>
  impl_tac >- (simp[Abbr ‘j0’, Abbr ‘B’]) >>
  strip_tac >>
  qexists_tac ‘SUC (a + j')’ >>
  first_x_assum (qspec_then ‘j'’ mp_tac) >> simp[] >> strip_tac >>
  ‘FLAT (responses_to_b files D) ≼ FLAT (Wj files fd g j')’
    by (rw[IS_PREFIX_APPEND] >> fs[IS_PREFIX_APPEND] >> simp[FLAT_APPEND] >> metis_tac[]) >>
  metis_tac[bytes_prefix]
QED

(* ------------------------------------------------------------------------
   HttpSpecBodies' liveness
   ------------------------------------------------------------------------ *)

Theorem print_brequest_nonempty[local]:
  print_brequest r ≠ []
Proof
  Cases_on ‘r’ >> simp[print_brequest_def]
QED

(* The complete requests in printed requests are those requests *)
Theorem parse_all_b_printed:
  EVERY valid_brequest rs ⇒ parse_all_b (FLAT (MAP print_brequest rs)) = rs
Proof
  strip_tac >>
  qspecl_then [‘rs’] mp_tac (Q.INST [‘rest’ |-> ‘[]’] parse_all_brequests) >>
  simp[] >> disch_then irule >> rpt strip_tac >>
  ‘print_brequest r = []’ by (Cases_on ‘print_brequest r’ >> fs[]) >>
  fs[print_brequest_nonempty]
QED

(* MAIN: the event loop's I/O satisfies HttpSpecBodies' liveness: the
   responses to all complete requests a client sends in the first n steps
   are eventually written on its connection *)
Theorem http_live_b_rounds:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  http_live_b files s0
    (LFLATTEN (LGENLIST (λi. fromList (HEV files lfdn s0 i)) NONE))
Proof
  rw[http_live_b_def] >>
  ‘grun_ok (EI lfdn) (srelabel (http_server_b files lfdn)) s0’
    by metis_tac[grun_ok_http_b] >>
  (* no requests: nothing to answer *)
  Cases_on ‘rs = []’
  >- (qexists_tac ‘FLAT (GENLIST (HEV files lfdn s0) 0)’ >>
      simp[rounds_LPREFIX, bresponses_def, bytes_def]) >>
  (* otherwise something was sent on c, so c is a connection by round n *)
  ‘sent_upto c n s0 ≠ []’
    by (Cases_on ‘rs’ >> fs[brequests_def, bytes_def] >>
        strip_tac >> fs[print_brequest_nonempty]) >>
  ‘is_conn (HG files lfdn s0 n) c’
    by (drule_all grounds_acct >> disch_then (qspecl_then [‘c’, ‘n’] mp_tac) >>
        simp[acct_def, is_conn_def] >> CASE_TAC >> simp[]) >>
  (* it is handed out at some round N0 *)
  ‘∃N0. MEM c (wacc (HP files lfdn s0 N0))’
    by (mp_tac (Q.GEN ‘hf’ sw_conn_accepted
                |> Q.ISPEC ‘λfd. http_handler_b files (fd, "")’) >>
        simp[GSYM http_server_b_def, hok_http_b, uses_ok_http_b]) >>
  ‘MEM c (wacc (HP files lfdn s0 (n + N0)))’
    by (irule wacc_mono >> qexists_tac ‘N0’ >> simp[]) >>
  ‘bytes (FLAT (MAP print_brequest rs)) ≼ sent_upto c (n + N0) s0’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c n s0’ >>
        fs[sent_upto_prefix, brequests_def]) >>
  (* then everything sent by round n + N0 is answered *)
  mp_tac (Q.INST [‘D’ |-> ‘FLAT (MAP print_brequest rs)’, ‘n’ |-> ‘n + N0 : num’]
            http_accepted_live_b) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac ‘FLAT (GENLIST (HEV files lfdn s0) N)’ >> simp[rounds_LPREFIX] >>
  ‘parse_all_b (FLAT (MAP print_brequest rs)) = rs’
    by (irule parse_all_b_printed >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘bytes _ ≼ bytes_written_to _ _’ mp_tac >>
  asm_rewrite_tac[bresponses_def]
QED
