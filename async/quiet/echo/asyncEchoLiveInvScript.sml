(*
  What #46's live list holds, along the polling run of the echo program.

  The blocking echo program (layer 8, echo_live) selects on a live list:
  the listener, plus each connection it accepted, minus each connection
  whose EOF it read (lstep, live_of).  On the polling run it is

     LIVE N = live_of [listener] (the performed pairs of rounds < N).

  live_inv: every fd in it is the listener, or a connection the server
  accepted and whose EOF it has not read (and the list has no
  duplicates).  Reads are only on accepted connections, and no fd is
  accepted twice in this world.

  With the server's declared interest covered by the live list
  (sel_covers_echo, #46), this makes the live list EXACTLY what the echo
  server waits for: an echo handler runs until it reads EOF.  That is why
  the shipped blocking echo program goes to sleep (asyncEchoSleeps), and
  why the same live list is wrong for HTTP, whose handler can stop before
  EOF (#56).

  MAIN: live_inv.
*)
Theory asyncEchoLiveInv
Ancestors
  pair list rich_list arithmetic option llist alist words
  ffiSpikeSocketFFI asyncM3World asyncM4GRounds asyncM4GTrans asyncM4SockInv
  asyncM4SockModel asyncM4EchoRunOk asyncM4LiveEcho asyncM4ReadSoon
  asyncEchoMeasure asyncEchoStable
Libs
  preamble

Overload LIVE = “λlfdn s0 N.
  live_of [n2w lfdn : word64]
    (MAP (λ(a, r). (a, SOME r)) (SP lfdn (EI lfdn) s0 N))”

Theorem remove_one_MEM[local]:
  ∀l. MEM w (remove_one c l) ⇒ MEM w l
Proof
  Induct >> rw[remove_one_def] >> metis_tac[]
QED

Theorem remove_one_distinct[local]:
  ∀l. ALL_DISTINCT l ⇒ ALL_DISTINCT (remove_one c l) ∧ ¬MEM c (remove_one c l)
Proof
  Induct >> rw[remove_one_def] >> metis_tac[remove_one_MEM]
QED

(* One round's pairs: reads only of fds in A, fresh accepts *)
Theorem live_round[local]:
  ∀P l A.
    (∀c k r. MEM (Read c k, r) P ⇒ MEM c A) ∧
    ALL_DISTINCT (A ++ wacc P) ∧ ¬MEM L (A ++ wacc P) ∧
    ALL_DISTINCT l ∧ (∀w. MEM w l ⇒ w = L ∨ MEM w A) ⇒
    ALL_DISTINCT (live_of l (MAP (λ(a, r). (a, SOME r)) P)) ∧
    ∀w. MEM w (live_of l (MAP (λ(a, r). (a, SOME r)) P)) ⇒
        (MEM w l ∧ ∀k. ¬MEM (Read w k, Got (SOME [])) P) ∨ MEM w (wacc P)
Proof
  Induct >- simp[live_of_def] >>
  rpt gen_tac >> PairCases_on ‘h’ >> rename1 ‘(a, r)’ >> strip_tac >>
  simp[live_of_def] >> simp[GSYM live_of_def] >>
  Cases_on ‘∃l' c. a = Accept l' ∧ r = Accepted (SOME c)’
  (* an accept: c joins the live list *)
  >- (gvs[lstep_def, wacc_def] >>
      first_x_assum (qspecl_then [‘c :: l’, ‘A ++ [c]’] mp_tac) >>
      impl_tac
      >- (gvs[ALL_DISTINCT_APPEND] >> rw[] >> metis_tac[]) >>
      strip_tac >> simp[] >> rpt strip_tac >> res_tac >> gvs[])
  >> Cases_on ‘∃c k. a = Read c k ∧ r = Got (SOME [])’
  (* an EOF: c leaves the live list *)
  >- (gvs[lstep_def, wacc_def] >>
      first_x_assum (qspecl_then [‘remove_one c l’, ‘A’] mp_tac) >>
      impl_tac
      >- (simp[remove_one_distinct] >> metis_tac[remove_one_MEM]) >>
      strip_tac >> simp[] >> rpt strip_tac >> res_tac >> gvs[]
      >- (Cases_on ‘w = c’ >> gvs[remove_one_distinct] >> metis_tac[remove_one_MEM])
      >> simp[])
  (* anything else: no change *)
  >> ‘lstep l (a, SOME r) = l ∧ wacc ((a, r) :: P) = wacc P’
       by (Cases_on ‘a’ >> Cases_on ‘r’ >> gvs[lstep_def, wacc_def] >>
           every_case_tac >> gvs[]) >>
  gvs[] >>
  first_x_assum (qspecl_then [‘l’, ‘A’] mp_tac) >> impl_tac >- metis_tac[] >>
  strip_tac >> simp[] >> rpt strip_tac >> res_tac >> gvs[] >> metis_tac[]
QED

(* The server reads only connections it has accepted *)
Theorem eofr_wacc:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀N. (∀k r. MEM (Read c k, r) (SP lfdn (EI lfdn) s0 N) ⇒
             MEM c (wacc (SP lfdn (EI lfdn) s0 N)))
Proof
  strip_tac >> Induct >- simp[gperf_def] >>
  simp[gperf_SUC] >> rpt strip_tac >> gvs[]
  >- (res_tac >> simp[])
  >> mp_tac (Q.INST [‘ifds’ |-> ‘EI lfdn’] echo_sinv) >> simp[] >>
  disch_then (qspec_then ‘N’ strip_assume_tac) >>
  drule echo_round_actions_ok >>
  ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[]) >>
  drule LENGTH_gres >> disch_then (qspec_then ‘N’ assume_tac) >>
  qspecl_then [‘(SA lfdn (EI lfdn) s0 N, gres (EI lfdn) (EM lfdn) s0 N)’,
               ‘(Read c k, r)’] mp_tac (Q.GENL [‘ps’, ‘p’] MEM_ZIP_MEM_MAP) >>
  simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> simp[action_ok_def]
QED

(* MAIN: along the polling run, the live list is the listener and the
   accepted connections whose EOF the server has not read *)
Theorem live_inv:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀N. ALL_DISTINCT (LIVE lfdn s0 N) ∧
      ∀w. MEM w (LIVE lfdn s0 N) ⇒
          w = n2w lfdn ∨
          (MEM w (wacc (SP lfdn (EI lfdn) s0 N)) ∧ ¬eofr lfdn s0 w N)
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[]) >>
  Induct >- simp[gperf_def, live_of_def] >>
  simp[gperf_SUC, live_of_APPEND] >>
  qabbrev_tac ‘P = ZIP (SA lfdn (EI lfdn) s0 N, gres (EI lfdn) (EM lfdn) s0 N)’ >>
  qabbrev_tac ‘A = wacc (SP lfdn (EI lfdn) s0 N)’ >>
  mp_tac (Q.INST [‘ifds’ |-> ‘EI lfdn’] echo_sinv) >> simp[] >>
  disch_then (fn th => assume_tac (Q.SPEC ‘N’ th) >> assume_tac (Q.SPEC ‘SUC N’ th)) >>
  gvs[] >>
  ‘∀c k r. MEM (Read c k, r) P ⇒ MEM c A’
    by (rpt strip_tac >>
        qpat_x_assum ‘gok_upto _ _ _ N’ (mp_tac o MATCH_MP echo_round_actions_ok) >>
        simp[EVERY_MEM] >> strip_tac >>
        drule LENGTH_gres >> disch_then (qspec_then ‘N’ assume_tac) >>
        qspecl_then [‘(SA lfdn (EI lfdn) s0 N, gres (EI lfdn) (EM lfdn) s0 N)’,
                     ‘(Read c k, r)’] mp_tac (Q.GENL [‘ps’, ‘p’] MEM_ZIP_MEM_MAP) >>
        simp[Abbr ‘P’] >> rpt strip_tac >> first_x_assum drule >>
        simp[action_ok_def, Abbr ‘A’]) >>
  ‘ALL_DISTINCT (A ++ wacc P) ∧ ¬MEM (n2w lfdn) (A ++ wacc P)’
    by (qpat_x_assum ‘sinv _ (wacc (gperf _ _ _ (SUC N))) _’ mp_tac >>
        simp[sinv_def, gperf_SUC, Abbr ‘A’, Abbr ‘P’] >> strip_tac >>
        ‘ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 (SUC N)).conns (n2w lfdn) = NONE’
          by metis_tac[conns_no_listener] >>
        rpt conj_tac >> TRY (gvs[ALL_DISTINCT_APPEND] >> NO_TAC) >>
        strip_tac >>
        qpat_x_assum ‘∀c. _ ⇒ is_conn _ c’ (qspec_then ‘n2w lfdn’ mp_tac) >>
        simp[is_conn_def]) >>
  qspecl_then [‘P’, ‘LIVE lfdn s0 N’, ‘A’] mp_tac
    (Q.GEN ‘L’ live_round |> Q.SPEC ‘n2w lfdn’) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >> simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac
  (* already live: still not EOF-read *)
  >- (first_x_assum drule >> strip_tac >> simp[eofr_SUC] >> metis_tac[])
  (* accepted in this round: not EOF-read before (not yet accepted), nor
     now (reads are of earlier connections) *)
  >> ‘¬MEM w A’ by (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  simp[eofr_SUC, eofr_def] >> disj2_tac >> rpt strip_tac
  >- (qspecl_then [‘s0’, ‘lfdn’, ‘w’] mp_tac (Q.GENL [‘s0’, ‘lfdn’, ‘c’] eofr_wacc) >>
      impl_tac >- simp[] >> disch_then (qspec_then ‘N’ drule) >> gvs[Abbr ‘A’])
  >> res_tac
QED
