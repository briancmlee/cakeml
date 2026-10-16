(*
  Liveness carried by the library (design/34 §2): for the generic server
  server_with hf, run by the event loop in a fair socket world, liveness
  of the socket trace follows from ONE per-handler obligation.

   - hread fd h g j: what handler h has read from fd after j snapshots of
     its history g.
   - henv fd h g j0 D: the four facts the socket world guarantees about a
     handler's own fd, from round j0 on, for data D that has been sent:
       1. what has been read and D are comparable (both are prefixes of
          what was sent);
       2. not reported readable: nothing is unread (D is read by the next
          snapshot);
       3. an outstanding read, with D not all read, reads all of D or
          something;
       4. after end-of-file, all of D has been read.
     They are stated on the handler's transcript, so they do not mention
     any server's internal state.
   - handler_live hf out B: in every such environment, given B D rounds,
     the handler writes out D, the output owed for D.  This is what each
     server proves (for HTTP: hmachine_live_p, via a bridge).

  Main theorems:
   - sw_view: the handler of a connection c handed out by round n, on the
     loop's rounds, for ANY interest function (lifted from http_b_view);
   - sw_henv: the socket world gives henv on that view, for any interest
     function that covers the accepted fds (lifted from the environment
     derivation inside http_accepted_live_b);
   - sw_accepted_live: handler_live ⇒ on an accepted connection, out D is
     eventually written, for any prefix D of what was sent;
   - server_with_live: for the dynamic-interest loop (interest [lfd], run_i), every
     connection: everything owed for what a client sent is eventually
     written.
*)
Theory skeletonLive
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words string
  asyncCore asyncLevel1 asyncTranscript echoServer echoServerSafety
  echoProgress socketWorld socketFair EchoSpec HttpGetSpec
  loopPollWorld loopRounds relabel relabelDist
  echoSockModel loopSockInv loopRoundsTrans loopPollDyn echoRunOk
  echoLiveSched echoLiveAccount echoLiveProg echoLiveWorld echoLiveReadSoon
  echoLiveQueue echoLiveAcceptSoon echoLiveDrain skeletonRunOk skeleton
  skeletonUses skeletonProgress skeletonSock
Libs
  preamble

(* ------------------------------------------------------------------------
   The per-handler interface
   ------------------------------------------------------------------------ *)

(* What handler h has read from fd after j snapshots of its history g *)
Definition hread_def:
  hread fd h g j = CONCAT (read fd (trans h (TAKE j g)))
End

(* The environment of a handler on its own fd, from round j0, for data D
   that has been sent (design/34 §2.2) *)
Definition henv_def:
  henv fd h g j0 D ⇔
    (∀j. j0 ≤ j ∧ j ≤ LENGTH g ⇒ hread fd h g j ≼ D ∨ D ≼ hread fd h g j) ∧
    (∀j. j0 ≤ j ∧ j < LENGTH g ∧ Readable fd ∉ (EL j g).ready ⇒
         D ≼ hread fd h g (SUC j)) ∧
    (∀j. j0 ≤ j ∧ j < LENGTH g ∧ MEM (Read fd, NONE) (trans h (TAKE j g)) ∧
         ¬(D ≼ hread fd h g j) ⇒
         D ≼ hread fd h g (SUC j) ∨
         LENGTH (hread fd h g j) < LENGTH (hread fd h g (SUC j))) ∧
    (∀j. j0 ≤ j ∧ j ≤ LENGTH g ∧ MEM (Read fd, SOME Eof) (trans h (TAKE j g)) ⇒
         D ≼ hread fd h g j)
End

(* The per-handler obligation: in every such environment, B D rounds are
   enough to write out D (design/34 §2.3) *)
Definition handler_live_def:
  handler_live hf out B ⇔
    ∀fd g j0 D.
      prompt (hf fd) g ∧ henv fd (hf fd) g j0 D ∧ j0 + B D ≤ LENGTH g ⇒
      ∃j. j ≤ LENGTH g ∧ out D ≼ written fd (trans (hf fd) (TAKE j g))
End

(* ------------------------------------------------------------------------
   The server is well behaved
   ------------------------------------------------------------------------ *)

Theorem uses_ok_sw:
  hok hf ⇒ uses_ok lfd (server_with hf lfd)
Proof
  strip_tac >> simp[uses_ok_def] >> irule server_with_uses_accepted >>
  metis_tac[hok_own]
QED

Theorem grun_ok_sw:
  hok hf ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  grun_ok ifds (srelabel (server_with hf lfdn)) s0
Proof
  strip_tac >> irule gen_grun_ok >> metis_tac[uses_ok_sw]
QED

(* ------------------------------------------------------------------------
   Strings and bytes
   ------------------------------------------------------------------------ *)

Theorem LENGTH_bytes_sw[simp]:
  LENGTH (bytes s) = LENGTH s
Proof
  simp[bytes_def]
QED

(* bytes is injective character by character, so it preserves and
   reflects prefixes *)
Theorem bytes_prefix_sw:
  ∀s t. bytes s ≼ bytes t ⇔ s ≼ t
Proof
  Induct >> simp[bytes_def] >> gen_tac >> Cases >> simp[] >>
  ‘∀c. ORD c < 256’ by simp[ORD_BOUND] >>
  ‘(n2w (ORD h) : word8 = n2w (ORD h')) ⇔ h = h'’
    by (simp[n2w_11, ORD_11] >> metis_tac[ORD_11]) >>
  fs[bytes_def]
QED

(* grounds_acct, in the form used below *)
Theorem sent_split_sw:
  s0.conns = [] ∧ sched_wf s0 ∧ grun_ok ifds m s0 ⇒
  ∃inc. sent_upto c k s0 = pread_all c (gperf ifds m s0 k) ++ inc ∧
        (∀cn. ALOOKUP (gstate ifds m s0 k).conns c = SOME cn ⇒ inc = cn.incoming) ∧
        (ALOOKUP (gstate ifds m s0 k).conns c = NONE ⇒ inc = [])
Proof
  strip_tac >> drule_all grounds_acct >> disch_then (qspecl_then [‘c’, ‘k’] mp_tac) >>
  simp[acct_def] >> CASE_TAC >> simp[]
QED

(* ------------------------------------------------------------------------
   The handler of an accepted connection, on the loop's rounds
   ------------------------------------------------------------------------ *)

(* The loop's rounds of server_with hf, for interest function ifds *)
Overload SWM = “λhf lfdn. srelabel (server_with hf lfdn)”
Overload SWH = “λhf ifds lfdn s0 k. MAP sfs (ghist ifds (srelabel (server_with hf lfdn)) s0 k)”
Overload SWP = “λhf ifds lfdn s0 k. gperf ifds (srelabel (server_with hf lfdn)) s0 k”
Overload SWG = “λhf ifds lfdn s0 k. gstate ifds (srelabel (server_with hf lfdn)) s0 k”
Overload SWA = “λhf ifds lfdn s0 k. gacts ifds (srelabel (server_with hf lfdn)) s0 k”
Overload SWEV = “λhf ifds lfdn s0. grounds_events ifds (srelabel (server_with hf lfdn)) s0”

(* gen_rounds_bytes for server_with hf (its bytes is echoSafe's
   overload, MAP (n2w o ORD); here it is HttpGetSpec's bytes) *)
Theorem sw_rounds_bytes:
  hok hf ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀c n.
    bytes_written_to c (FLAT (GENLIST (grounds_events ifds (srelabel (server_with hf lfdn)) s0) (SUC n))) =
      bytes (FLAT (written (w2n c) (TSg (server_with hf lfdn) ifds s0 n))) ∧
    bytes_read_from c (FLAT (GENLIST (grounds_events ifds (srelabel (server_with hf lfdn)) s0) n)) =
      bytes (FLAT (read (w2n c) (TSg (server_with hf lfdn) ifds s0 n)))
Proof
  rw[bytes_def] >> metis_tac[gen_rounds_bytes, uses_ok_sw]
QED

(* MAIN: c, handed out by round n, is served by its own handler hf (w2n c),
   on a history g from the round a ≤ n in which c was handed out; at round
   a + j the handler has read what the server has read from c, and has
   written what the server's events up to the end of round a + j wrote.
   For any interest function. *)
Theorem sw_view:
  hok hf ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SWP hf ifds lfdn s0 n)) ∧ n ≤ M ⇒
  ∃a g. a ≤ n ∧ LENGTH g + a = M ∧ prompt (hf (w2n c)) g ∧
    (∀i. i < LENGTH g ⇒ (EL i g).ready = (EL (a + i) (SWH hf ifds lfdn s0 M)).ready) ∧
    ∀j. j ≤ LENGTH g ⇒
      FILTER (on_fd (w2n c)) (TSg (server_with hf lfdn) ifds s0 (a + j)) =
        trans (hf (w2n c)) (TAKE j g) ∧
      bytes (hread (w2n c) (hf (w2n c)) g j) = pread_all c (SWP hf ifds lfdn s0 (a + j)) ∧
      bytes (FLAT (written (w2n c) (trans (hf (w2n c)) (TAKE j g)))) =
        bytes_written_to c (FLAT (GENLIST (SWEV hf ifds lfdn s0) (SUC (a + j))))
Proof
  strip_tac >>
  ‘grun_ok ifds (SWM hf lfdn) s0’ by metis_tac[grun_ok_sw] >>
  ‘uses_ok lfdn (server_with hf lfdn)’ by metis_tac[uses_ok_sw] >>
  ‘∀k. k ≤ M ⇒ TAKE k (SWH hf ifds lfdn s0 M) = SWH hf ifds lfdn s0 k’
    by simp[GSYM MAP_TAKE, ghist_TAKE] >>
  ‘∀k. accepted (TSg (server_with hf lfdn) ifds s0 k) =
       MAP w2n (wacc (SWP hf ifds lfdn s0 k))’
    by metis_tac[TSg_accepted] >>
  ‘MEM c (wacc (SWP hf ifds lfdn s0 M))’
    by (irule wacc_mono >> qexists_tac ‘n’ >> simp[]) >>
  qspec_then ‘SWH hf ifds lfdn s0 M’ mp_tac
    (Q.INST [‘fd’ |-> ‘w2n (c : word64)’, ‘lfd’ |-> ‘lfdn’] sw_handler_view) >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- metis_tac[gen_fresh]
      >- (irule prompt_ghist >> simp[])
      >> simp[MEM_MAP] >> metis_tac[]) >>
  strip_tac >>
  ‘a ≤ n’
    by (first_x_assum (qspec_then ‘n’ mp_tac) >> simp[MEM_MAP] >> metis_tac[]) >>
  qexists_tac ‘a’ >> qexists_tac ‘g’ >> simp[] >>
  rpt gen_tac >> strip_tac >>
  ‘FILTER (on_fd (w2n c)) (TSg (server_with hf lfdn) ifds s0 (a + j)) =
   trans (hf (w2n c)) (TAKE j g)’
    by (‘a + j ≤ M’ by fs[] >>
        ‘TAKE (a + j) (SWH hf ifds lfdn s0 M) = SWH hf ifds lfdn s0 (a + j)’ by fs[] >>
        qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER _ _ = _’ (qspec_then ‘j’ mp_tac) >>
        asm_rewrite_tac[] >> simp[]) >>
  simp[hread_def] >> pop_assum (SUBST1_TAC o SYM) >>
  simp[read_FILTER, written_FILTER] >>
  ‘bytes_read_from c (FLAT (GENLIST (SWEV hf ifds lfdn s0) (a + j))) =
   pread_all c (SWP hf ifds lfdn s0 (a + j))’
    by (irule bytes_read_from_rounds >> first_assum ACCEPT_TAC) >>
  (* gen_rounds_bytes's bytes is echoSafe's overload, MAP (n2w o ORD) *)
  drule_all sw_rounds_bytes >> strip_tac >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   The socket world gives the handler its environment
   ------------------------------------------------------------------------ *)

(* The loop polls every handed-out fd *)
Definition interest_covers_def:
  interest_covers ifds m s0 ⇔
    ∀k c. MEM c (wacc (gperf ifds m s0 k)) ⇒ MEM c (ifds (ghist ifds m s0 k))
End

(* The dynamic-interest loop (run_i) covers the handed-out fds *)
Theorem interest_covers_EI:
  grun_ok (EI lfdn) m s0 ⇒ interest_covers (EI lfdn) m s0
Proof
  rw[interest_covers_def] >> irule interest_accepted >> simp[]
QED

(* MAIN: on the view of a connection c handed out by round n, the socket
   world gives the handler its environment henv for any prefix D of what
   was sent on c by round n (design/34 §2.2) *)
Theorem sw_view_henv:
  hok hf ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ sched_wf s0 ∧
  interest_covers ifds (SWM hf lfdn) s0 ∧
  MEM c (wacc (SWP hf ifds lfdn s0 n)) ∧ bytes D ≼ sent_upto c n s0 ∧ n ≤ M ⇒
  ∃a g. a ≤ n ∧ LENGTH g + a = M ∧ prompt (hf (w2n c)) g ∧
    henv (w2n c) (hf (w2n c)) g (n − a) D ∧
    ∀j. j ≤ LENGTH g ⇒
      bytes (FLAT (written (w2n c) (trans (hf (w2n c)) (TAKE j g)))) =
        bytes_written_to c (FLAT (GENLIST (SWEV hf ifds lfdn s0) (SUC (a + j))))
Proof
  strip_tac >>
  ‘grun_ok ifds (SWM hf lfdn) s0’ by metis_tac[grun_ok_sw] >>
  ‘uses_ok lfdn (server_with hf lfdn)’ by metis_tac[uses_ok_sw] >>
  drule_all sw_view >> strip_tac >>
  qexists_tac ‘a’ >> qexists_tac ‘g’ >> simp[] >>
  qabbrev_tac ‘fd = w2n (c : word64)’ >>
  ‘n2w fd = c’ by simp[Abbr ‘fd’] >>
  qabbrev_tac ‘j0 = n − a’ >>
  (* what was sent on c, round by round, against what the handler read *)
  ‘∀j. j ≤ LENGTH g ⇒
       ∃inc. sent_upto c (a + j) s0 = bytes (hread fd (hf fd) g j) ++ inc ∧
             (∀cn. ALOOKUP (SWG hf ifds lfdn s0 (a + j)).conns c = SOME cn ⇒
                   inc = cn.incoming) ∧
             (ALOOKUP (SWG hf ifds lfdn s0 (a + j)).conns c = NONE ⇒ inc = [])’
    by (rpt strip_tac >>
        ‘∃inc. sent_upto c (a + j) s0 = pread_all c (SWP hf ifds lfdn s0 (a + j)) ++ inc ∧
               (∀cn. ALOOKUP (SWG hf ifds lfdn s0 (a + j)).conns c = SOME cn ⇒
                     inc = cn.incoming) ∧
               (ALOOKUP (SWG hf ifds lfdn s0 (a + j)).conns c = NONE ⇒ inc = [])’
          by (irule sent_split_sw >> simp[]) >>
        qexists_tac ‘inc’ >> simp[] >> metis_tac[]) >>
  (* from round n on, D has been sent *)
  ‘∀j. j0 ≤ j ⇒ bytes D ≼ sent_upto c (a + j) s0’
    by (rpt strip_tac >> irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c n s0’ >>
        simp[] >> ‘a + j = n + (a + j − n)’ by simp[Abbr ‘j0’] >>
        pop_assum SUBST1_TAC >> simp[sent_upto_prefix]) >>
  simp[henv_def] >> rpt conj_tac >> rpt strip_tac
  (* what has been read and D are comparable *)
  >- (REWRITE_TAC[GSYM bytes_prefix_sw] >>
      first_x_assum (qspec_then ‘j’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
      first_x_assum (qspec_then ‘j’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
      metis_tac[prefixes_is_prefix_total, IS_PREFIX_APPEND3, IS_PREFIX_TRANS])
  (* not reported readable: nothing unread at the next round *)
  >- (‘a + j < M ∧ j + 1 ≤ LENGTH g ∧ j0 ≤ j + 1’ by fs[] >>
      ‘MEM c (wacc (SWP hf ifds lfdn s0 (a + j)))’
        by (irule wacc_mono >> qexists_tac ‘n’ >> fs[Abbr ‘j0’]) >>
      ‘MEM c (ifds (ghist ifds (SWM hf lfdn) s0 (a + j)))’
        by fs[interest_covers_def] >>
      ‘¬is_ready (SWG hf ifds lfdn s0 (a + (j + 1))) c’
        by (strip_tac >> qpat_x_assum ‘Readable fd ∉ _’ mp_tac >>
            qpat_x_assum ‘∀i. i < LENGTH g ⇒ _’ (qspec_then ‘j’ mp_tac) >>
            impl_tac >- simp[] >> disch_then SUBST1_TAC >>
            simp[EL_MAP, snap_map_def, sfe_def, ready_EL_ghist, MEM_FILTER] >>
            qexists_tac ‘c’ >> fs[Abbr ‘fd’, ADD1]) >>
      qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ ∃inc. _’ (qspec_then ‘j + 1’ mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      ‘inc = []’
        by (Cases_on ‘ALOOKUP (SWG hf ifds lfdn s0 (a + (j + 1))).conns c’ >> fs[] >>
            fs[is_ready_def] >> gvs[]) >>
      qpat_x_assum ‘∀j. j0 ≤ j ⇒ bytes D ≼ _’ (qspec_then ‘j + 1’ mp_tac) >>
      impl_tac >- simp[] >>
      qpat_x_assum ‘sent_upto _ _ _ = _’ SUBST1_TAC >>
      qpat_x_assum ‘inc = []’ SUBST1_TAC >>
      REWRITE_TAC[APPEND_NIL, bytes_prefix_sw, ADD1])
  (* an outstanding read, with D not all read: there was unread data *)
  >- (disj2_tac >>
      ‘j ≤ LENGTH g ∧ j + 1 ≤ LENGTH g’ by fs[] >>
      qpat_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER _ _ = _ ∧ _’ (qspec_then ‘j’ mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      ‘MEM (Read fd, NONE) (TSg (server_with hf lfdn) ifds s0 (a + j))’
        by (qpat_x_assum ‘FILTER _ _ = _’ (fn th =>
              qpat_x_assum ‘MEM _ (trans _ _)’ (mp_tac o REWRITE_RULE [GSYM th])) >>
            simp[MEM_FILTER]) >>
      ‘reads_c c (SWA hf ifds lfdn s0 (a + j))’
        by (qpat_x_assum ‘n2w fd = c’ (SUBST1_TAC o SYM) >>
            irule TSg_read_none >> metis_tac[]) >>
      qpat_assum ‘∀j. j ≤ LENGTH g ⇒ ∃inc. _’ (qspec_then ‘j’ mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      ‘inc ≠ []’
        by (strip_tac >> qpat_x_assum ‘¬(D ≼ _)’ mp_tac >>
            REWRITE_TAC[GSYM bytes_prefix_sw] >>
            qpat_x_assum ‘∀j. j0 ≤ j ⇒ bytes D ≼ _’ (qspec_then ‘j’ mp_tac) >>
            impl_tac >- simp[] >>
            qpat_x_assum ‘sent_upto _ _ _ = _’ SUBST1_TAC >>
            qpat_x_assum ‘inc = []’ SUBST1_TAC >>
            REWRITE_TAC[APPEND_NIL] >> metis_tac[]) >>
      ‘∃cn. ALOOKUP (SWG hf ifds lfdn s0 (a + j)).conns c = SOME cn ∧ cn.incoming ≠ []’
        by (Cases_on ‘ALOOKUP (SWG hf ifds lfdn s0 (a + j)).conns c’ >- fs[] >>
            qpat_x_assum ‘∀cn. _ ⇒ inc = _’ (qspec_then ‘x’ mp_tac) >> simp[] >>
            strip_tac >> fs[]) >>
      drule grun_ok_sock_acts >>
      disch_then (qspec_then ‘a + j’ strip_assume_tac) >>
      drule_all sock_acts_read_nonempty >> strip_tac >>
      qpat_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER _ _ = _ ∧ _’ (qspec_then ‘j + 1’ mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      ‘STRLEN (hread fd (hf fd) g j) = LENGTH (pread_all c (SWP hf ifds lfdn s0 (a + j))) ∧
       STRLEN (hread fd (hf fd) g (SUC j)) =
         LENGTH (pread_all c (SWP hf ifds lfdn s0 (a + j + 1)))’
        by metis_tac[LENGTH_bytes_sw, ADD1, ADD_ASSOC] >>
      simp[GSYM ADD1, gperf_SUC] >>
      Cases_on ‘pread_all c (ZIP (gacts ifds (SWM hf lfdn) s0 (a + j),
                                  gres ifds (SWM hf lfdn) s0 (a + j)))’ >>
      fs[])
  (* after end-of-file, nothing is unread *)
  >> qpat_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER _ _ = _ ∧ _’ (qspec_then ‘j’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  ‘MEM (Read fd, SOME Eof) (TSg (server_with hf lfdn) ifds s0 (a + j))’
    by (qpat_x_assum ‘FILTER _ _ = _’ (fn th =>
          qpat_x_assum ‘MEM _ (trans _ _)’ (mp_tac o REWRITE_RULE [GSYM th])) >>
        simp[MEM_FILTER]) >>
  ‘∃k. MEM (Read c k, Got (SOME [])) (SWP hf ifds lfdn s0 (a + j))’
    by (qpat_x_assum ‘n2w fd = c’ (SUBST1_TAC o SYM) >>
        irule TSg_eof >> metis_tac[]) >>
  ‘∃cn. ALOOKUP (SWG hf ifds lfdn s0 (a + j)).conns c = SOME cn ∧ cn.incoming = []’
    by metis_tac[grounds_eof] >>
  qpat_assum ‘∀j. j ≤ LENGTH g ⇒ ∃inc. _’ (qspec_then ‘j’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  ‘inc = []’ by metis_tac[] >>
  qpat_x_assum ‘∀j. j0 ≤ j ⇒ bytes D ≼ _’ (qspec_then ‘j’ mp_tac) >>
  impl_tac >- simp[] >>
  qpat_x_assum ‘sent_upto _ _ _ = _’ SUBST1_TAC >>
  qpat_x_assum ‘inc = []’ SUBST1_TAC >>
  REWRITE_TAC[APPEND_NIL, bytes_prefix_sw]
QED

(* ------------------------------------------------------------------------
   Liveness
   ------------------------------------------------------------------------ *)

(* MAIN: per-handler liveness gives liveness on an accepted connection, for
   any interest function that covers the handed-out fds: the output owed
   for any prefix D of what was sent on c by round n is eventually written
   to c *)
Theorem sw_accepted_live:
  hok hf ∧ handler_live hf out B ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ sched_wf s0 ∧
  interest_covers ifds (SWM hf lfdn) s0 ∧
  MEM c (wacc (SWP hf ifds lfdn s0 n)) ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N. bytes (FLAT (out D)) ≼ bytes_written_to c (FLAT (GENLIST (SWEV hf ifds lfdn s0) N))
Proof
  strip_tac >>
  mp_tac (Q.INST [‘M’ |-> ‘n + B D : num’] sw_view_henv) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘handler_live _ _ _’ (mp_tac o REWRITE_RULE [handler_live_def]) >>
  disch_then (qspecl_then [‘w2n c’, ‘g’, ‘n − a’, ‘D’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac ‘SUC (a + j)’ >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> impl_tac >- simp[] >>
  disch_then (SUBST1_TAC o SYM) >>
  REWRITE_TAC[bytes_prefix_sw] >>
  qpat_x_assum ‘out D ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >> simp[]
QED

(* MAIN: the library liveness theorem (design/34 §2.4).  For the
   dynamic-interest loop (run_i, interest [lfd]) in any fair socket world:
   if every handler meets handler_live, then for every connection c and
   every prefix D of what its client sent by round n, the output owed for
   D is eventually written to c. *)
Theorem server_with_live:
  hok hf ∧ handler_live hf out B ∧ FLAT (out "") = "" ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N. bytes (FLAT (out D)) ≼
      bytes_written_to c (FLAT (GENLIST (SWEV hf (EI lfdn) lfdn s0) N))
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (SWM hf lfdn) s0’ by metis_tac[grun_ok_sw] >>
  ‘uses_ok lfdn (server_with hf lfdn)’ by metis_tac[uses_ok_sw] >>
  (* nothing owed *)
  Cases_on ‘D = ""’
  >- (qexists_tac ‘0’ >> gvs[bytes_def]) >>
  (* otherwise something was sent on c, so c is a connection by round n *)
  ‘sent_upto c n s0 ≠ []’ by (strip_tac >> Cases_on ‘D’ >> fs[bytes_def]) >>
  ‘is_conn (SWG hf (EI lfdn) lfdn s0 n) c’
    by (drule_all grounds_acct >> disch_then (qspecl_then [‘c’, ‘n’] mp_tac) >>
        simp[acct_def, is_conn_def] >> CASE_TAC >> simp[]) >>
  (* it is handed out at some round N0 *)
  ‘∃N0. MEM c (wacc (SWP hf (EI lfdn) lfdn s0 N0))’
    by (irule sw_conn_accepted >> simp[] >> metis_tac[]) >>
  ‘MEM c (wacc (SWP hf (EI lfdn) lfdn s0 (n + N0)))’
    by (irule wacc_mono >> qexists_tac ‘N0’ >> simp[]) >>
  ‘bytes D ≼ sent_upto c (n + N0) s0’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c n s0’ >>
        simp[sent_upto_prefix]) >>
  (* then everything sent by round n + N0 is answered *)
  irule (Q.INST [‘n’ |-> ‘n + N0 : num’, ‘ifds’ |-> ‘EI lfdn’] sw_accepted_live) >>
  simp[interest_covers_EI] >> metis_tac[]
QED
