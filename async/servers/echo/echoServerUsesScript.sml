(*
  The echo server never misuses the socket API, in the model.

  The real socket FFI fails on misuse: reading from or writing to an fd
  that is not a connection, or accepting on an fd that is not a listener.
  M3's loop theorem assumes there is none (srun_ok, spike/m3-assembly).
  For the echo server this follows from its structure, which this theory
  states and proves over the model's transcript (asyncTranscript), on
  every history:

   - every Accept is on the listener lfd;
   - every Read or Write on a connection fd comes after the response
     Accepted fd, earlier in the transcript.

  No assumption on the world is needed (not even fresh).  Relating the
  transcript to the socket world's state (an accepted fd is a connection,
  and stays one) is the remaining, world-side part; see
  design/15-m4-server.md.
*)
Theory echoServerUses
Ancestors
  pair list rich_list arithmetic option asyncCore asyncLevel1 asyncLevel2
  asyncTranscript echoServer echoServerSafety
Libs
  BasicProvers

(* The pair is the response Accepted fd to an Accept *)
Definition accepts_def:
  accepts fd (p : action # response option) ⇔ ∃l. p = (Accept l, SOME (Accepted fd))
End

(* The pair reads or writes fd, or hands out fd *)
Definition touches_def:
  touches fd p ⇔ on_fd fd p ∨ accepts fd p
End

(* acc_first fd tr: no read or write of fd in tr before fd is accepted *)
Definition acc_first_def:
  (acc_first fd [] ⇔ T) ∧
  (acc_first fd (p :: tr) ⇔
     if accepts fd p then T else ¬on_fd fd p ∧ acc_first fd tr)
End

(* Every Accept in tr is on lfd *)
Definition accepts_on_def:
  accepts_on lfd tr ⇔ EVERY (λp. is_accept p ⇒ FST p = Accept lfd) tr
End

Theorem acc_first_APPEND:
  ∀t1. acc_first fd (t1 ++ t2) ⇔
       acc_first fd t1 ∧ (EXISTS (accepts fd) t1 ∨ acc_first fd t2)
Proof
  Induct >> rw[acc_first_def] >> metis_tac[]
QED

(* acc_first only looks at the pairs that touch fd *)
Theorem acc_first_FILTER:
  ∀tr. acc_first fd (FILTER (touches fd) tr) ⇔ acc_first fd tr
Proof
  Induct >> rw[acc_first_def, touches_def] >> gvs[]
QED

Theorem accepts_on_FILTER:
  ∀tr. accepts_on lfd (FILTER is_accept tr) ⇔ accepts_on lfd tr
Proof
  Induct >> rw[accepts_on_def] >> gvs[accepts_on_def]
QED

(* An equivalent formulation of acc_first, by positions: the transcript
   before every read or write of fd contains the response Accepted fd. *)
Theorem acc_first_MEM:
  ∀tr. acc_first fd tr ⇔
       ∀t1 p t2. tr = t1 ++ p :: t2 ∧ on_fd fd p ⇒ EXISTS (accepts fd) t1
Proof
  Induct >> rw[acc_first_def] >> eq_tac >> rw[]
  >- (Cases_on ‘t1’ >> gvs[accepts_def, on_fd_def])
  >- (Cases_on ‘t1’ >> gvs[] >> metis_tac[])
  >> Cases_on ‘accepts fd h’ >> simp[] >> conj_tac
  >- (strip_tac >> first_x_assum (qspecl_then [‘[]’, ‘h’, ‘tr’] mp_tac) >>
      simp[])
  >> rw[] >> first_x_assum (qspecl_then [‘h :: t1’, ‘p’, ‘t2’] mp_tac) >>
  simp[]
QED

(* The handler of fd only touches fd, by reading and writing it *)
Theorem handler_touches[local]:
  g ≠ fd ⇒ FILTER (touches g) (trans (handler fd) h) = []
Proof
  strip_tac >> qspecl_then [‘fd’, ‘h’] mp_tac (Q.GEN ‘fd’ handler_echoes) >>
  simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >>
  gvs[on_fd_def, touches_def, accepts_def] >> rw[] >> gvs[]
QED

Theorem handler_no_accept[local]:
  FILTER is_accept (trans (handler fd) h) = []
Proof
  qspecl_then [‘fd’, ‘h’] mp_tac (Q.GEN ‘fd’ handler_echoes)
  >> simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac
  >> first_x_assum drule >> gvs[on_fd_def, is_accept_def]
QED

(* MAIN: the echo server uses the socket API correctly, on every history:
   it accepts only on the listener lfd, and it reads or writes a
   connection fd only after the response Accepted fd. *)
Theorem server_uses_accepted:
  ∀h. accepts_on lfd (trans (server lfd) h) ∧
      ∀fd. acc_first fd (trans (server lfd) h)
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’
  >> ONCE_REWRITE_TAC[server_unfold]
  (* wait until the listener is readable *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable lfd) K0) h’
  >> qspecl_then [‘readable lfd’, ‘K0’, ‘h’] mp_tac
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
  >> qabbrev_tac ‘L = left_view (handler fd) (server lfd) h2'’
  >> qabbrev_tac ‘R = right_view (handler fd) (server lfd) h2'’
  >> ‘LENGTH R < LENGTH h1 + (LENGTH h2' + 1)’ by simp[Abbr ‘R’]
  >> first_x_assum (qspec_then ‘R’ mp_tac) >> simp[] >> strip_tac
  >> conj_tac
  >- (‘accepts_on lfd (trans (both (handler fd) (server lfd)) h2')’
        suffices_by simp[accepts_on_def, is_accept_def, trans_map] >>
      ONCE_REWRITE_TAC[GSYM accepts_on_FILTER] >>
      ‘FILTER is_accept (trans (both (handler fd) (server lfd)) h2') =
       FILTER is_accept (trans (server lfd) R)’
        by (simp[Abbr ‘R’] >> irule trans_both_filter_right >>
            simp[handler_no_accept]) >>
      pop_assum SUBST1_TAC >> simp[accepts_on_FILTER])
  >> gen_tac >> simp[acc_first_def, accepts_def]
  >> Cases_on ‘fd' = fd’ >> simp[]
  >> ONCE_REWRITE_TAC[GSYM acc_first_FILTER]
  >> ‘FILTER (touches fd') (trans (both (handler fd) (server lfd)) h2') =
      FILTER (touches fd') (trans (server lfd) R)’
       by (simp[Abbr ‘R’] >> irule trans_both_filter_right >>
           simp[handler_touches])
  >> pop_assum SUBST1_TAC >> simp[acc_first_FILTER]
QED
