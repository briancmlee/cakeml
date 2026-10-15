(*
  The model server's view of the event loop's run, for liveness.

  The event loop runs srelabel (server lfdn) (asyncM4SockModel) in the
  socket world; the model server itself sees the history
     G n = MAP sfs (ghist ifds (srelabel (server lfdn)) s0 n).
  The program-level progress theorems (asyncProgress) need two facts about
  G, proved here:
   - prompt_ghist: the world answers every action in the next snapshot;
   - ready_ghist: snapshot j reports fd ready exactly when some polled
     socket fd c with w2n c = fd is ready after round j; with the growing
     interest list (asyncM4Loop), every connection handed out so far, and
     the listener, are polled (interest_accepted).
*)
Theory asyncM4LiveProg
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress ffiSpikeSocketFFI asyncM3World asyncM4GRounds asyncM4Relabel
  asyncM4RelabelDist asyncM4SockModel asyncM4SockInv asyncM4GTrans asyncM4Loop
  asyncM4Sched
Libs
  preamble

Theorem sfs_results[local]:
  (sfs s).results = MAP sfr s.results
Proof
  simp[snap_map_def]
QED

(* MAIN: the model server's view of the run is prompt *)
Theorem prompt_ghist:
  grun_ok ifds (relabel fa sfs m) s0 ⇒
  prompt m (MAP sfs (ghist ifds (relabel fa sfs m) s0 n))
Proof
  rw[prompt_def]
  >> ‘TAKE i (MAP sfs (ghist ifds (relabel fa sfs m) s0 n)) =
      MAP sfs (ghist ifds (relabel fa sfs m) s0 i)’
       by simp[GSYM MAP_TAKE, ghist_TAKE]
  >> simp[responses_at_MAP, sfs_results, responses_at_def, results_EL_ghist]
  >> drule LENGTH_gres >> disch_then (qspec_then ‘i’ mp_tac)
  >> gvs[gacts_def, new_actions_relabel, EL_MAP, sfs_results, results_EL_ghist]
QED

(* Snapshot j of the run: the ready fds among the polled ones, after round j *)
Theorem ready_EL_ghist:
  j < n ⇒
  (EL j (ghist ifds m s0 n)).ready =
  set (FILTER (is_ready (gstate ifds m s0 (SUC j))) (ifds (ghist ifds m s0 j)))
Proof
  strip_tac >>
  ‘EL j (ghist ifds m s0 n) = EL j (ghist ifds m s0 (SUC j))’
    by (‘SUC j ≤ n’ by simp[] >>
        drule_then (qspecl_then [‘s0’, ‘m’, ‘ifds’] (SUBST1_TAC o SYM))
          (Q.GENL [‘ifds’, ‘m’, ‘s0’] ghist_TAKE |> SPEC_ALL |>
           Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘k’] |>
           Q.SPECL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘SUC j’]) >>
        simp[EL_TAKE]) >>
  simp[Once ghist_def, grounds_SUC, EL_APPEND2, ssnap_def, gstate_SUC, gmid_def,
       sock_poll_def]
QED

(* The interest list contains the initial fds and every connection handed
   out in the run so far *)
Theorem MEM_add_accepted:
  ∀rs fds. MEM c fds ⇒ MEM c (add_accepted fds rs)
Proof
  Induct >> simp[add_accepted_def] >> rpt strip_tac
  >> first_x_assum irule >> every_case_tac >> simp[]
QED

Theorem wacc_add_accepted:
  ∀acts rs fds. MEM c (wacc (ZIP (acts, rs))) ∧ LENGTH acts = LENGTH rs ⇒
                MEM c (add_accepted fds rs)
Proof
  Induct >> simp[wacc_def] >> rpt gen_tac >> Cases_on ‘rs’
  >> simp[wacc_def, add_accepted_def] >> strip_tac
  >- (every_case_tac >> gvs[] >> irule MEM_add_accepted >> simp[])
  >> first_x_assum irule >> simp[]
QED

Theorem interest_ghist_SUC:
  interest fds0 (ghist ifds m s0 (SUC n)) =
  add_accepted (interest fds0 (ghist ifds m s0 n)) (gres ifds m s0 n)
Proof
  simp[Once ghist_def, grounds_SUC, interest_SNOC, ssnap_def, gres_def]
QED

(* MAIN: in round n, the loop polls the listener and every connection
   handed out so far *)
Theorem interest_accepted:
  ∀n c. grun_ok (interest fds0) m s0 ∧
        (MEM c fds0 ∨ MEM c (wacc (gperf (interest fds0) m s0 n))) ⇒
        MEM c (interest fds0 (ghist (interest fds0) m s0 n))
Proof
  Induct
  >- simp[gperf_def, wacc_def, ghist_def, grounds_def]
  >> rpt strip_tac >> simp[interest_ghist_SUC]
  >> gvs[gperf_SUC]
  >- (irule MEM_add_accepted >> simp[])
  >- (irule MEM_add_accepted >> first_x_assum irule >> simp[])
  >> irule wacc_add_accepted >> qexists_tac ‘gacts (interest fds0) m s0 n’
  >> simp[LENGTH_gres]
QED
