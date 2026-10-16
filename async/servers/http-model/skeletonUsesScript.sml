(*
  The generic server skeleton never misuses the socket API, in the model:
  m4-server's server_uses_accepted (echoServerUses), for server_with h
  and any handler h whose run on fd only reads and writes fd.

     server_with_uses_accepted:
       every Accept is on the listener lfd, and every Read or Write of a
       connection fd comes after the response Accepted fd.

  The proof is server_uses_accepted's, with server_with_unfold for
  server_unfold and the handler hypothesis for handler_echoes.
*)
Theory skeletonUses
Ancestors
  pair list rich_list arithmetic option asyncCore asyncLevel1 asyncLevel2
  asyncTranscript echoServer echoServerSafety echoServerUses
  skeleton httpGetServer
Libs
  BasicProvers

(* The handler of fd only touches fd, by reading and writing it *)
Theorem handler_touches_gen[local]:
  EVERY (on_fd fd) (trans m hh) ∧ g ≠ fd ⇒ FILTER (touches g) (trans m hh) = []
Proof
  simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
  gvs[on_fd_def, touches_def, accepts_def] >> rw[] >> gvs[]
QED

Theorem handler_no_accept_gen[local]:
  EVERY (on_fd fd) (trans m hh) ⇒ FILTER is_accept (trans m hh) = []
Proof
  simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
  gvs[on_fd_def, is_accept_def]
QED

(* MAIN: if every handler h fd only reads and writes fd, the server
   skeleton uses the socket API correctly, on every history: it accepts
   only on the listener lfd, and it reads or writes a connection fd only
   after the response Accepted fd. *)
Theorem server_with_uses_accepted:
  (∀fd hh. EVERY (on_fd fd) (trans (h fd) hh)) ⇒
  ∀hh. accepts_on lfd (trans (server_with h lfd) hh) ∧
       ∀fd. acc_first fd (trans (server_with h lfd) hh)
Proof
  strip_tac >> gen_tac >> measureInduct_on ‘LENGTH hh’
  >> ONCE_REWRITE_TAC[server_with_unfold]
  (* wait until the listener is readable *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable lfd) K0) hh’
  >> qspecl_then [‘readable lfd’, ‘K0’, ‘hh’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac
  >- simp[accepts_on_def, acc_first_def]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  (* accept *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Accept lfd)) K1) h2’
  >> qspecl_then [‘emit (Accept lfd)’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- simp[trans_emit, accepts_on_def, acc_first_def, is_accept_def,
          accepts_def]
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’]
  >> reverse (Cases_on ‘res’) >> simp[]
  (* no new connection: the rest of the server *)
  >> TRY (first_x_assum (qspec_then ‘h2'’ mp_tac) >>
          simp[accepts_on_def, acc_first_def, is_accept_def, accepts_def] >>
          NO_TAC)
  (* a new connection fd: its handler, alongside the rest of the server *)
  >> rename1 ‘Accepted fd’
  >> qabbrev_tac ‘L = left_view (h fd) (server_with h lfd) h2'’
  >> qabbrev_tac ‘R = right_view (h fd) (server_with h lfd) h2'’
  >> ‘LENGTH R < LENGTH h1 + (LENGTH h2' + 1)’ by simp[Abbr ‘R’]
  >> first_x_assum (qspec_then ‘R’ mp_tac) >> simp[] >> strip_tac
  >> conj_tac
  >- (‘accepts_on lfd (trans (both (h fd) (server_with h lfd)) h2')’
        suffices_by simp[accepts_on_def, is_accept_def, trans_map] >>
      ONCE_REWRITE_TAC[GSYM accepts_on_FILTER] >>
      ‘FILTER is_accept (trans (both (h fd) (server_with h lfd)) h2') =
       FILTER is_accept (trans (server_with h lfd) R)’
        by (simp[Abbr ‘R’] >> irule trans_both_filter_right >>
            irule handler_no_accept_gen >> metis_tac[]) >>
      pop_assum SUBST1_TAC >> simp[accepts_on_FILTER])
  >> gen_tac >> simp[acc_first_def, accepts_def]
  >> Cases_on ‘fd' = fd’ >> simp[]
  >> ONCE_REWRITE_TAC[GSYM acc_first_FILTER]
  >> ‘FILTER (touches fd') (trans (both (h fd) (server_with h lfd)) h2') =
      FILTER (touches fd') (trans (server_with h lfd) R)’
       by (simp[Abbr ‘R’] >> irule trans_both_filter_right >>
           irule handler_touches_gen >> metis_tac[])
  >> pop_assum SUBST1_TAC >> simp[acc_first_FILTER]
QED

(* The HTTP server is an instance *)
Theorem http_server_uses_accepted:
  ∀hh. accepts_on lfd (trans (http_server files lfd) hh) ∧
       ∀fd. acc_first fd (trans (http_server files lfd) hh)
Proof
  simp[httpGetServerTheory.http_server_def] >> gen_tac >>
  irule server_with_uses_accepted >> simp[] >>
  metis_tac[httpGetServerTheory.http_handler_serves]
QED
