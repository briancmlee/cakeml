(*
  A copy of KV's asyncServerWithK (spike/http-kv-impl, WIP there), renamed,
  so the chat server does not depend on unchecked work.  Reconcile later.

  server_with over the vocabulary of with_store (asyncWithStore): a
  connection's handler may emit Sock actions (socket calls) and Kv (fd, q)
  queries, each tagged with its connection.

     cserver_with h lfd = wait until lfd is readable;
                           accept;
                           on Accepted fd: both (h fd) (cserver_with h lfd)
                           otherwise:      cserver_with h lfd

  This is asyncServerWith's server_with, verbatim up to the Sock/SockR
  tags, and its two MAIN results carry over with the same proofs:
   - cserver_with_isolates: if each handler only touches its own fd (its
     socket calls on fd and its queries tagged fd), then on every fd the
     server's entries are those of one run of the handler;
   - cserver_with_uses_accepted: outside the store (untag), the server
     uses the socket API correctly (uses_ok, asyncRunOkGen).
*)
Theory asyncChatSW
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncM4ServerUses asyncWithStore
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   Pairs of the inner transcript
   ------------------------------------------------------------------------ *)

(* An inner pair, as an outer one (if it is a Sock pair) *)
Definition sock_pairc_def:
  sock_pairc ((Sock x, r) : ('a, 'q) kact # ('b, 'r) kres option) =
    SOME (x, case r of SOME (SockR y) => SOME y | _ => NONE) ∧
  sock_pairc (Kv q, r) = NONE
End

Theorem untag_sock_pairc:
  ∀tr. untag tr = FLAT (MAP (λp. case sock_pairc p of SOME x => [x] | NONE => []) tr)
Proof
  Induct >> simp[untag_def] >> PairCases >> Cases_on ‘h0’ >>
  simp[sock_pairc_def] >> simp[GSYM untag_def]
QED

(* A property of outer pairs, for inner pairs: Kv pairs never have it *)
Definition liftc_def:
  liftc P p ⇔ case sock_pairc p of SOME x => P x | NONE => F
End

Theorem untag_FILTERc:
  ∀tr. untag (FILTER (liftc P) tr) = FILTER P (untag tr)
Proof
  Induct >> simp[untag_def] >> PairCases >> Cases_on ‘h0’ >>
  rw[liftc_def, sock_pairc_def] >> gvs[GSYM untag_def] >> simp[untag_def]
QED

(* The pair reads or writes fd, or is a query of fd's handler *)
Definition on_fdc_def:
  on_fdc fd (p : (asyncServer$action, num # 'q) kact # ('b, asyncServer$response) kres option) ⇔
    case FST p of Sock a => on_fd fd (a, NONE) | Kv q => FST q = fd
End

Definition is_acceptc_def:
  is_acceptc (p : (asyncServer$action, num # 'q) kact # ('b, asyncServer$response) kres option) ⇔ ∃l. FST p = Sock (Accept l)
End

Definition acceptedc_def:
  acceptedc (tr : ((asyncServer$action, num # 'q) kact # ('b, asyncServer$response) kres option) list) =
    FLAT (MAP (λp. case p of
                     (Sock (Accept l), SOME (SockR (Accepted fd))) => [fd]
                   | _ => []) tr)
End

Definition freshc_def:
  freshc tr ⇔ ALL_DISTINCT (acceptedc tr)
End

Theorem acceptedc_simps[simp]:
  acceptedc [] = [] ∧ acceptedc (l1 ++ l2) = acceptedc l1 ++ acceptedc l2 ∧
  acceptedc [(Sock (Accept l), SOME (SockR (Accepted fd)))] = [fd]
Proof
  simp[acceptedc_def]
QED

Theorem acceptedc_CONS:
  acceptedc (p :: l) = acceptedc [p] ++ acceptedc l
Proof
  simp[acceptedc_def]
QED

Theorem acceptedc_FILTER:
  ∀tr. acceptedc (FILTER is_acceptc tr) = acceptedc tr
Proof
  Induct >> simp[] >> PairCases >> rw[is_acceptc_def] >> gvs[acceptedc_def] >>
  every_case_tac >> gvs[]
QED

Theorem acceptedc_untag:
  ∀tr. acceptedc tr = accepted (untag tr)
Proof
  Induct >> simp[acceptedc_def, untag_def, accepted_def] >> PairCases >> simp[] >>
  fs[GSYM acceptedc_def, GSYM untag_def, GSYM accepted_def] >>
  every_case_tac >> gvs[accepted_def]
QED

Theorem freshc_untag:
  freshc tr ⇔ fresh (untag tr)
Proof
  simp[freshc_def, fresh_def, acceptedc_untag]
QED

(* ------------------------------------------------------------------------
   The server skeleton
   ------------------------------------------------------------------------ *)

Definition cserver_with_body_def:
  cserver_with_body h r lfd =
    bind (readable lfd) (λu.
    bind (emit (Sock (Accept lfd))) (λres.
      case res of
        SockR (Accepted fd) => map (λp. ()) (both (h fd) (r lfd))
      | _ => r lfd))
End

Theorem cserver_with_body_contractive:
  contractive (cserver_with_body h)
Proof
  rw[contractive_def, cserver_with_body_def]
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> gen_tac >> every_case_tac >> simp[nonexpansive_call]
  >> ho_match_mp_tac nonexpansive_map >> ho_match_mp_tac nonexpansive_both
  >> simp[nonexpansive_const, nonexpansive_call]
QED

Definition cserver_with_def:
  cserver_with h = fix (cserver_with_body h)
End

(* MAIN: the server satisfies its recursive equation *)
Theorem cserver_with_unfold:
  cserver_with h lfd =
    bind (readable lfd) (λu.
    bind (emit (Sock (Accept lfd))) (λres.
      case res of
        SockR (Accepted fd) => map (λp. ()) (both (h fd) (cserver_with h lfd))
      | _ => cserver_with h lfd))
Proof
  simp[cserver_with_def, Once (MATCH_MP fix_unfold cserver_with_body_contractive)]
  >> simp[cserver_with_body_def]
QED

Theorem wf_cserver_with:
  (∀fd. wf (h fd)) ⇒ wf (cserver_with h lfd)
Proof
  strip_tac >> simp[cserver_with_def] >> irule wf_fix
  >> simp[cserver_with_body_contractive]
  >> rw[cserver_with_body_def]
  >> irule wf_bind >> simp[readable_def, wf_wait]
  >> irule wf_bind >> simp[wf_emit] >> gen_tac >> every_case_tac >> simp[]
  >> irule wf_map >> irule wf_both >> simp[]
QED

Theorem settled_cserver_with:
  (∀fd. wf (h fd) ∧ settled (h fd)) ⇒ settled (cserver_with h lfd)
Proof
  strip_tac >> simp[cserver_with_def] >> irule settled_fix
  >> simp[cserver_with_body_contractive]
  >> rw[cserver_with_body_def]
  >> irule settled_bind >> simp[readable_def, wf_wait, settled_wait]
  >> irule settled_bind >> simp[wf_emit, settled_emit] >> gen_tac
  >> every_case_tac >> simp[]
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

(* MAIN: if each handler h fd only touches fd, and the connections the
   world hands out are distinct, then on every fd the server's entries on
   fd are those of one run of h fd (on some history L), or there are none;
   and the server only touches connections it has accepted. *)
Theorem cserver_with_isolates:
  (∀fd hh. EVERY (on_fdc fd) (trans (h fd) hh)) ⇒
  ∀hh. freshc (trans (cserver_with h lfd) hh) ⇒
       (∀fd. FILTER (on_fdc fd) (trans (cserver_with h lfd) hh) = [] ∨
             ∃L. FILTER (on_fdc fd) (trans (cserver_with h lfd) hh) =
                 trans (h fd) L) ∧
       (∀fd. EXISTS (on_fdc fd) (trans (cserver_with h lfd) hh) ⇒
             MEM fd (acceptedc (trans (cserver_with h lfd) hh)))
Proof
  strip_tac >>
  ‘∀g hh. FILTER is_acceptc (trans (h g) hh) = []’
    by (rw[FILTER_EQ_NIL, EVERY_MEM] >> CCONTR_TAC >> fs[] >>
        first_assum (qspecl_then [‘g’, ‘hh’] assume_tac) >> fs[EVERY_MEM] >>
        res_tac >> PairCases_on ‘x’ >> gvs[on_fdc_def, is_acceptc_def, on_fd_def]) >>
  ‘∀g fd hh. g ≠ fd ⇒ FILTER (on_fdc g) (trans (h fd) hh) = []’
    by (rw[FILTER_EQ_NIL, EVERY_MEM] >> CCONTR_TAC >> fs[] >>
        first_assum (qspecl_then [‘fd’, ‘hh’] assume_tac) >> fs[EVERY_MEM] >>
        res_tac >> PairCases_on ‘x’ >> Cases_on ‘x0’ >>
        gvs[on_fdc_def, on_fd_def] >> rw[] >> gvs[]) >>
  gen_tac >> measureInduct_on ‘LENGTH hh’
  >> ONCE_REWRITE_TAC[cserver_with_unfold]
  (* wait until the listener is readable *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable lfd) K0) hh’
  >> qspecl_then [‘readable lfd’, ‘K0’, ‘hh’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac >> simp[]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  (* accept *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Sock (Accept lfd))) K1) h2’
  >> qspecl_then [‘emit (Sock (Accept lfd))’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- simp[trans_emit, on_fdc_def]
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’, on_fdc_def]
  >> ‘(∃fd. res = SockR (Accepted fd)) ∨
      (∀fd. res ≠ SockR (Accepted fd)) ∧
      (case res of SockR (Accepted fd) => map (λp. ()) (both (h fd) (cserver_with h lfd))
                 | _ => cserver_with h lfd) = cserver_with h lfd’
       by (Cases_on ‘res’ >> simp[] >> rename1 ‘SockR r0’ >> Cases_on ‘r0’ >> simp[])
  (* no new connection: the rest of the server *)
  >- (gvs[] >> rename1 ‘Accepted fd’
      >> qabbrev_tac ‘L = left_view (h fd) (cserver_with h lfd) h2'’
      >> qabbrev_tac ‘R = right_view (h fd) (cserver_with h lfd) h2'’
      >> ‘LENGTH R < LENGTH h1 + (LENGTH h2' + 1)’ by simp[Abbr ‘R’]
      >> ‘acceptedc (trans (both (h fd) (cserver_with h lfd)) h2') =
          acceptedc (trans (cserver_with h lfd) R)’
           by (ONCE_REWRITE_TAC[GSYM acceptedc_FILTER] >> AP_TERM_TAC
               >> simp[Abbr ‘R’] >> irule trans_both_filter_right >> simp[])
      >> simp[freshc_def, Once acceptedc_CONS] >> strip_tac
      >> first_x_assum (qspec_then ‘R’ mp_tac) >> simp[freshc_def, Once acceptedc_CONS] >> strip_tac
      (* the rest of the server never touches fd *)
      >> ‘FILTER (on_fdc fd) (trans (cserver_with h lfd) R) = []’
           by (CCONTR_TAC >> gvs[GSYM EXISTS_FILTER] >> res_tac)
      >> ‘FILTER (on_fdc fd) (trans (both (h fd) (cserver_with h lfd)) h2') =
          FILTER (on_fdc fd) (trans (h fd) L)’
           by (simp[Abbr ‘L’] >> irule trans_both_filter_left >> fs[Abbr ‘R’])
      >> ‘∀g. g ≠ fd ⇒
              FILTER (on_fdc g) (trans (both (h fd) (cserver_with h lfd)) h2') =
              FILTER (on_fdc g) (trans (cserver_with h lfd) R)’
           by (rpt strip_tac >> simp[Abbr ‘R’] >> irule trans_both_filter_right
               >> simp[])
      >> conj_tac
      >- (gen_tac >> Cases_on ‘fd' = fd’
          >- (disj2_tac >> qexists_tac ‘L’ >> gvs[] >>
              simp[FILTER_EQ_ID] >> metis_tac[])
          >> first_x_assum drule >> simp[])
      >> rpt strip_tac >> Cases_on ‘fd' = fd’ >> simp[]
      >> first_x_assum (qspec_then ‘fd'’ mp_tac) >> simp[] >> strip_tac
      >> gvs[EXISTS_FILTER])
  >> simp[] >> pop_assum kall_tac
  >> ‘acceptedc [(Sock (Accept lfd), SOME res)] = []’
       by (simp[acceptedc_def] >> every_case_tac >> gvs[])
  >> simp[freshc_def, Once acceptedc_CONS] >> strip_tac
  >> first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[freshc_def, Once acceptedc_CONS]
QED

(* ------------------------------------------------------------------------
   The socket API is used correctly
   ------------------------------------------------------------------------ *)

Theorem handler_touches_c[local]:
  EVERY (on_fdc fd) (trans m hh) ∧ g ≠ fd ⇒
  FILTER (liftc (touches g)) (trans m hh) = []
Proof
  simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
  PairCases_on ‘x’ >> Cases_on ‘x0’ >>
  gvs[on_fdc_def, liftc_def, sock_pairc_def, touches_def, accepts_def, on_fd_def] >>
  rw[] >> gvs[]
QED

Theorem handler_no_accept_c[local]:
  EVERY (on_fdc fd) (trans m hh) ⇒ FILTER (liftc is_accept) (trans m hh) = []
Proof
  simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
  PairCases_on ‘x’ >> Cases_on ‘x0’ >>
  gvs[on_fdc_def, liftc_def, sock_pairc_def, is_accept_def, on_fd_def]
QED

Theorem untag_singc[local]:
  untag [(Sock a, SOME (SockR r))] = [(a, SOME r)]
Proof
  simp[untag_def]
QED

Theorem untag_sing_kvc[local]:
  untag [(Sock a, SOME (KvR b))] = [(a, NONE)]
Proof
  simp[untag_def]
QED

Theorem untag_CONSc[local]:
  untag (x :: l) = untag [x] ++ untag l
Proof
  simp[untag_def]
QED

(* MAIN: outside the store, the server accepts only on the listener lfd,
   and reads or writes a connection fd only after the response
   Accepted fd. *)
Theorem cserver_with_uses_accepted:
  (∀fd hh. EVERY (on_fdc fd) (trans (h fd) hh)) ⇒
  ∀hh. accepts_on lfd (untag (trans (cserver_with h lfd) hh)) ∧
       ∀fd. acc_first fd (untag (trans (cserver_with h lfd) hh))
Proof
  strip_tac >> gen_tac >> measureInduct_on ‘LENGTH hh’
  >> ONCE_REWRITE_TAC[cserver_with_unfold]
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable lfd) K0) hh’
  >> qspecl_then [‘readable lfd’, ‘K0’, ‘hh’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac
  >- simp[accepts_on_def, acc_first_def, untag_def]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Sock (Accept lfd))) K1) h2’
  >> qspecl_then [‘emit (Sock (Accept lfd))’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- (simp[trans_emit, untag_def, accepts_on_def, acc_first_def, is_accept_def,
           accepts_def] >> every_case_tac >> simp[])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’]
  >> qabbrev_tac ‘p0 = untag [(Sock (Accept lfd), SOME res)]’
  >> ‘accepts_on lfd p0 ∧ ∀fd. ¬on_fd fd (HD p0) ∧ LENGTH p0 = 1’
       by (simp[Abbr ‘p0’, untag_def, accepts_on_def, is_accept_def] >>
           every_case_tac >> simp[on_fd_def])
  >> ‘(∃fd. res = SockR (Accepted fd)) ∨
      (case res of SockR (Accepted fd) => map (λp. ()) (both (h fd) (cserver_with h lfd))
                 | _ => cserver_with h lfd) = cserver_with h lfd ∧
      ∀fd. ¬accepts fd (HD p0)’
       by (Cases_on ‘res’ >> simp[Abbr ‘p0’, untag_def, accepts_def] >>
           rename1 ‘SockR r0’ >> Cases_on ‘r0’ >> simp[])
  >- (gvs[] >> rename1 ‘Accepted fd’
      >> qabbrev_tac ‘L = left_view (h fd) (cserver_with h lfd) h2'’
      >> qabbrev_tac ‘R = right_view (h fd) (cserver_with h lfd) h2'’
      >> ‘LENGTH R < LENGTH h1 + (LENGTH h2' + 1)’ by simp[Abbr ‘R’]
      >> first_x_assum (qspec_then ‘R’ mp_tac) >> simp[] >> strip_tac
      >> ‘p0 = [(Accept lfd, SOME (Accepted fd))]’ by simp[Abbr ‘p0’, untag_def]
      >> conj_tac
      >- (‘accepts_on lfd (untag (trans (both (h fd) (cserver_with h lfd)) h2'))’
            suffices_by (disch_then mp_tac >> ONCE_REWRITE_TAC[untag_CONSc] >>
                         simp[accepts_on_def, is_accept_def, untag_def]) >>
          ONCE_REWRITE_TAC[GSYM accepts_on_FILTER] >>
          REWRITE_TAC[GSYM untag_FILTERc] >>
          ‘FILTER (liftc is_accept) (trans (both (h fd) (cserver_with h lfd)) h2') =
           FILTER (liftc is_accept) (trans (cserver_with h lfd) R)’
            by (simp[Abbr ‘R’] >> irule trans_both_filter_right >>
                irule handler_no_accept_c >> metis_tac[]) >>
          pop_assum SUBST1_TAC >> simp[untag_FILTERc, accepts_on_FILTER])
      >> gen_tac >> ONCE_REWRITE_TAC[untag_CONSc] >> REWRITE_TAC[untag_singc]
      >> simp[acc_first_def, accepts_def]
      >> Cases_on ‘fd' = fd’ >> simp[]
      >> ONCE_REWRITE_TAC[GSYM acc_first_FILTER]
      >> REWRITE_TAC[GSYM untag_FILTERc]
      >> ‘FILTER (liftc (touches fd')) (trans (both (h fd) (cserver_with h lfd)) h2') =
          FILTER (liftc (touches fd')) (trans (cserver_with h lfd) R)’
           by (simp[Abbr ‘R’] >> irule trans_both_filter_right >>
               irule handler_touches_c >> metis_tac[])
      >> pop_assum SUBST1_TAC >> simp[untag_FILTERc, acc_first_FILTER])
  >> gvs[] >> first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[] >> strip_tac
  >> ONCE_REWRITE_TAC[untag_CONSc]
  >> fs[markerTheory.Abbrev_def]
  >> Cases_on ‘res’
  >> TRY (rename1 ‘SockR r0’ >> Cases_on ‘r0’)
  >> gvs[untag_singc, untag_sing_kvc, accepts_on_def, acc_first_def, accepts_def,
         is_accept_def, on_fd_def]
QED
