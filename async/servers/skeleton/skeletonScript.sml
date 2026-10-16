(*
  The echo server's accept/fork skeleton, for any per-connection handler.
  Additive: echoServer's definitions are unchanged; the echo server is the
  instance  server_with handler  (server_with_handler).

     server_with h lfd = wait until lfd is readable;
                         accept;
                         on Accepted fd: both (h fd) (server_with h lfd)
                         otherwise:      server_with h lfd

  Main result (server_with_isolates, the generic form of echoServerSafety's
  server_echoes): if each handler h fd only reads and writes its own fd,
  and the connections the world hands out are distinct, then on every
  connection fd the server's reads and writes on fd are exactly those of
  one run of h fd (on some history), or there are none; and the server only
  touches connections it has accepted.  Per-connection properties of h
  therefore transfer to the whole server.
*)
Theory skeleton
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript echoServer
  echoServerSafety
Libs
  BasicProvers

Definition server_with_body_def:
  server_with_body h r lfd =
    bind (readable lfd) (λu.
    bind (emit (Accept lfd)) (λres.
      case res of
        Accepted fd => map (λp. ()) (both (h fd) (r lfd))
      | _ => r lfd))
End

Theorem server_with_body_contractive:
  contractive (server_with_body h)
Proof
  rw[contractive_def, server_with_body_def]
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> Cases >> simp[nonexpansive_call]
  >> ho_match_mp_tac nonexpansive_map >> ho_match_mp_tac nonexpansive_both
  >> simp[nonexpansive_const, nonexpansive_call]
QED

Definition server_with_def:
  server_with h = fix (server_with_body h)
End

(* MAIN: the generic server satisfies its recursive equation *)
Theorem server_with_unfold:
  server_with h lfd =
    bind (readable lfd) (λu.
    bind (emit (Accept lfd)) (λres.
      case res of
        Accepted fd => map (λp. ()) (both (h fd) (server_with h lfd))
      | _ => server_with h lfd))
Proof
  simp[server_with_def, Once (MATCH_MP fix_unfold server_with_body_contractive)]
  >> simp[server_with_body_def]
QED

(* MAIN: the echo server is the instance for the echo handler *)
Theorem server_with_handler:
  server_with handler = server
Proof
  simp[server_with_def, server_def] >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, server_with_body_def, server_body_def]
QED

Theorem wf_server_with:
  (∀fd. wf (h fd)) ⇒ wf (server_with h lfd)
Proof
  strip_tac >> simp[server_with_def] >> irule wf_fix
  >> simp[server_with_body_contractive]
  >> rw[server_with_body_def]
  >> irule wf_bind >> simp[readable_def, wf_wait]
  >> irule wf_bind >> simp[wf_emit] >> Cases >> simp[]
  >> irule wf_map >> irule wf_both >> simp[]
QED

Theorem settled_server_with:
  (∀fd. wf (h fd) ∧ settled (h fd)) ⇒ settled (server_with h lfd)
Proof
  strip_tac >> simp[server_with_def] >> irule settled_fix
  >> simp[server_with_body_contractive]
  >> rw[server_with_body_def]
  >> irule settled_bind >> simp[readable_def, wf_wait, settled_wait]
  >> irule settled_bind >> simp[wf_emit, settled_emit] >> Cases >> simp[]
  >> irule settled_map >> irule settled_both >> simp[]
QED

(* ------------------------------------------------------------------------
   Connections are isolated
   ------------------------------------------------------------------------ *)

Theorem EXISTS_FILTER[local]:
  ∀l. EXISTS P l ⇔ FILTER P l ≠ []
Proof
  Induct >> rw[]
QED

(* MAIN: if each handler h fd only reads and writes its own fd, and the
   connections the world hands out are distinct, then on every connection
   fd the server's reads and writes on fd are those of one run of h fd (on
   some history L), or there are none; and the server only touches
   connections it has accepted. *)
Theorem server_with_isolates:
  (∀fd hh. EVERY (on_fd fd) (trans (h fd) hh)) ⇒
  ∀hh. fresh (trans (server_with h lfd) hh) ⇒
       (∀fd. FILTER (on_fd fd) (trans (server_with h lfd) hh) = [] ∨
             ∃L. FILTER (on_fd fd) (trans (server_with h lfd) hh) =
                 trans (h fd) L) ∧
       (∀fd. EXISTS (on_fd fd) (trans (server_with h lfd) hh) ⇒
             MEM fd (accepted (trans (server_with h lfd) hh)))
Proof
  strip_tac >>
  ‘∀g hh. FILTER is_accept (trans (h g) hh) = []’
    by (rw[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM] >>
        res_tac >> gvs[on_fd_def, is_accept_def]) >>
  ‘∀g fd hh. g ≠ fd ⇒ FILTER (on_fd g) (trans (h fd) hh) = []’
    by (rw[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM] >>
        res_tac >> gvs[on_fd_def]) >>
  gen_tac >> measureInduct_on ‘LENGTH hh’
  >> ONCE_REWRITE_TAC[server_with_unfold]
  (* wait until the listener is readable *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable lfd) K0) hh’
  >> qspecl_then [‘readable lfd’, ‘K0’, ‘hh’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac >> simp[]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  (* accept *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Accept lfd)) K1) h2’
  >> qspecl_then [‘emit (Accept lfd)’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- simp[trans_emit]
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’]
  >> reverse (Cases_on ‘res’) >> simp[]
  (* no new connection: the rest of the server *)
  >> TRY (simp[fresh_def] >> strip_tac
          >> first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[fresh_def] >> NO_TAC)
  (* a new connection fd: its handler, alongside the rest of the server *)
  >> rename1 ‘Accepted fd’
  >> qabbrev_tac ‘L = left_view (h fd) (server_with h lfd) h2'’
  >> qabbrev_tac ‘R = right_view (h fd) (server_with h lfd) h2'’
  >> ‘LENGTH R < LENGTH h1 + (LENGTH h2' + 1)’ by simp[Abbr ‘R’]
  >> ‘accepted (trans (both (h fd) (server_with h lfd)) h2') =
      accepted (trans (server_with h lfd) R)’
       by (ONCE_REWRITE_TAC[GSYM accepted_FILTER] >> AP_TERM_TAC
           >> simp[Abbr ‘R’] >> irule trans_both_filter_right >> simp[])
  >> simp[fresh_def] >> strip_tac
  >> first_x_assum (qspec_then ‘R’ mp_tac) >> simp[fresh_def] >> strip_tac
  (* the rest of the server never touches fd *)
  >> ‘FILTER (on_fd fd) (trans (server_with h lfd) R) = []’
       by (CCONTR_TAC >> gvs[GSYM EXISTS_FILTER] >> res_tac)
  >> ‘FILTER (on_fd fd) (trans (both (h fd) (server_with h lfd)) h2') =
      FILTER (on_fd fd) (trans (h fd) L)’
       by (simp[Abbr ‘L’] >> irule trans_both_filter_left >> fs[Abbr ‘R’])
  >> ‘∀g. g ≠ fd ⇒
          FILTER (on_fd g) (trans (both (h fd) (server_with h lfd)) h2') =
          FILTER (on_fd g) (trans (server_with h lfd) R)’
       by (rpt strip_tac >> simp[Abbr ‘R’] >> irule trans_both_filter_right
           >> simp[])
  >> conj_tac
  >- (gen_tac >> Cases_on ‘fd' = fd’
      >- (disj2_tac >> qexists_tac ‘L’ >> gvs[] >>
          simp[FILTER_EQ_ID] >> metis_tac[])
      >> first_x_assum drule >> simp[])
  >> rpt strip_tac >> Cases_on ‘fd' = fd’ >> simp[]
  >> first_x_assum (qspec_then ‘fd'’ mp_tac) >> simp[] >> strip_tac
  >> gvs[EXISTS_FILTER]
QED
