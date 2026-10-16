(*
  M4's core property, in the model: the concurrent echo server echoes each
  client's data back to that client, and only to it, in order.

  Formulation (design/08-echo-server.md): take the server's transcript on
  any history h (each action paired with its response, asyncTranscript).
  For every connection fd,
     written fd tr  = the strings the server wrote to fd, in order;
     read fd tr     = the strings it received from fd (Data responses to its
                      reads of fd), in order.
  Theorem: written fd tr = read fd tr.  So every client gets back exactly
  its own data, in order, never another client's; and (because bind
  continues in the same round) every line is echoed in the round it
  arrives, so nothing is held back.

  The one assumption is about the world: the connections it hands out are
  distinct (fresh tr).  There is no close in this model, so fds are not
  reused.
*)
Theory asyncServerSafety
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript asyncServer
Libs
  BasicProvers

(* The action reads or writes fd *)
Definition on_fd_def:
  on_fd fd (p : action # response option) ⇔
    FST p = Read fd ∨ ∃d. FST p = Write fd d
End

Definition written_def:
  written fd tr =
    FLAT (MAP (λp. case FST p of Write fd' d => if fd' = fd then [d] else []
                               | _ => []) tr)
End

Definition read_def:
  read fd tr =
    FLAT (MAP (λp. case p of (Read fd', SOME (Data d)) => if fd' = fd then [d] else []
                           | _ => []) tr)
End

(* The connections the server accepted, in order *)
Definition accepted_def:
  accepted tr =
    FLAT (MAP (λp. case p of (Accept l, SOME (Accepted fd)) => [fd] | _ => []) tr)
End

Definition is_accept_def:
  is_accept (p : action # response option) ⇔ ∃l. FST p = Accept l
End

(* World assumption: the connections handed out are distinct *)
Definition fresh_def:
  fresh tr ⇔ ALL_DISTINCT (accepted tr)
End

Theorem written_APPEND[simp]:
  written fd (t1 ++ t2) = written fd t1 ++ written fd t2
Proof
  simp[written_def]
QED

Theorem read_APPEND[simp]:
  read fd (t1 ++ t2) = read fd t1 ++ read fd t2
Proof
  simp[read_def]
QED

Theorem accepted_APPEND[simp]:
  accepted (t1 ++ t2) = accepted t1 ++ accepted t2
Proof
  simp[accepted_def]
QED

Theorem written_NIL[simp]: written fd [] = []
Proof simp[written_def]
QED

Theorem read_NIL[simp]: read fd [] = []
Proof simp[read_def]
QED

Theorem accepted_NIL[simp]: accepted [] = []
Proof simp[accepted_def]
QED

Theorem written_CONS[simp]:
  written fd ((Read x, r) :: tr) = written fd tr ∧
  written fd ((Accept x, r) :: tr) = written fd tr ∧
  written fd ((Write x d, r) :: tr) = (if x = fd then [d] else []) ++ written fd tr
Proof
  simp[written_def]
QED

Theorem read_CONS[simp]:
  read fd ((Read x, NONE) :: tr) = read fd tr ∧
  read fd ((Read x, SOME r) :: tr) =
    (case r of Data d => if x = fd then [d] else [] | _ => []) ++ read fd tr ∧
  read fd ((Accept x, r') :: tr) = read fd tr ∧
  read fd ((Write x d, r') :: tr) = read fd tr
Proof
  simp[read_def] >> Cases_on ‘r’ >> simp[]
QED

Theorem accepted_CONS[simp]:
  accepted ((Read x, r) :: tr) = accepted tr ∧
  accepted ((Write x d, r) :: tr) = accepted tr ∧
  accepted ((Accept x, SOME r') :: tr) =
    (case r' of Accepted fd => [fd] | _ => []) ++ accepted tr ∧
  accepted ((Accept x, NONE) :: tr) = accepted tr
Proof
  simp[accepted_def] >> Cases_on ‘r'’ >> simp[]
QED

Theorem on_fd_simps[simp]:
  (on_fd fd (Read x, r) ⇔ x = fd) ∧
  (on_fd fd (Write x d, r) ⇔ x = fd) ∧
  ¬on_fd fd (Accept x, r)
Proof
  simp[on_fd_def] >> metis_tac[]
QED

(* written, read and accepted only look at the relevant pairs *)
Theorem written_FILTER:
  ∀tr. written fd (FILTER (on_fd fd) tr) = written fd tr
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on ‘h’
  >> rw[on_fd_def] >> gvs[written_def]
  >> Cases_on ‘h0’ >> gvs[]
QED

Theorem read_FILTER:
  ∀tr. read fd (FILTER (on_fd fd) tr) = read fd tr
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on ‘h’
  >> rw[on_fd_def] >> gvs[read_def]
  >> Cases_on ‘h0’ >> gvs[] >> every_case_tac >> gvs[]
QED

Theorem accepted_FILTER:
  ∀tr. accepted (FILTER is_accept tr) = accepted tr
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on ‘h’
  >> rw[is_accept_def] >> gvs[accepted_def]
  >> Cases_on ‘h0’ >> gvs[] >> every_case_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   Splitting the transcript of a bind
   ------------------------------------------------------------------------ *)

Theorem trans_bind_cases:
  wf m ∧ settled m ⇒
  (∀n. n ≤ LENGTH h ⇒ (m (TAKE n h)).result = NONE) ∧
  trans (bind m f) h = trans m h ∨
  ∃h1 h2 x. h = h1 ++ h2 ∧ first_done m h1 x ∧
            trans (bind m f) h = trans m h1 ++ trans (f x) h2
Proof
  strip_tac
  >> qspecl_then [‘m’, ‘h’] strip_assume_tac history_split
  >- (disj1_tac >> simp[] >> irule trans_bind_running >> simp[])
  >> disj2_tac >> qexistsl_tac [‘h1’, ‘h2’, ‘x’] >> simp[]
  >> irule trans_bind_continues >> simp[]
QED

Theorem first_done_wait_nonempty:
  first_done (wait p) h1 x ⇒ h1 ≠ []
Proof
  rpt strip_tac >> gvs[first_done_def, wait_def, first_some_def]
QED

Theorem first_done_emit:
  first_done (emit a) h1 x ⇒ ∃s. h1 = [s] ∧ oHD s.results = SOME x
Proof
  rw[first_done_def] >> Cases_on ‘h1’ >> gvs[emit_def]
  >> Cases_on ‘t’ >> gvs[]
  >> first_x_assum (qspec_then ‘1’ mp_tac) >> simp[emit_def]
QED

(* ------------------------------------------------------------------------
   One connection
   ------------------------------------------------------------------------ *)

(* MAIN: a connection's handler only reads and writes its own fd, and writes
   back exactly what it has read, in order *)
Theorem handler_echoes:
  ∀h. EVERY (on_fd fd) (trans (handler fd) h) ∧
      written fd (trans (handler fd) h) = read fd (trans (handler fd) h)
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’
  >> ONCE_REWRITE_TAC[handler_unfold] >> REWRITE_TAC[handler_body_def]
  (* wait until fd is readable *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable fd) K0) h’
  >> qspecl_then [‘readable fd’, ‘K0’, ‘h’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac >> simp[]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  (* read fd *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Read fd)) K1) h2’
  >> qspecl_then [‘emit (Read fd)’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- (* no response yet *)
     (simp[trans_emit] >> Cases_on ‘h2’ >> simp[]
      >> first_x_assum (qspec_then ‘1’ mp_tac) >> simp[emit_def]
      >> Cases_on ‘oHD h.results’ >> simp[])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’]
  >> Cases_on ‘res’ >> simp[]
  (* data d: write it back, then continue *)
  >> TRY (rename1 ‘Write fd d’
          >> qspecl_then [‘emit (Write fd d)’, ‘λw. handler fd’, ‘h2'’] mp_tac
               (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
          >> simp[wf_emit, settled_emit] >> strip_tac
          >- simp[trans_emit]
          >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
          >> first_x_assum (qspec_then ‘h2''’ mp_tac) >> simp[] >> NO_TAC)
  (* would block, or a stray response: continue *)
  >> first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   The whole server
   ------------------------------------------------------------------------ *)

Theorem EXISTS_FILTER[local]:
  ∀l. EXISTS P l ⇔ FILTER P l ≠ []
Proof
  Induct >> rw[]
QED

Theorem handler_no_accept[local]:
  FILTER is_accept (trans (handler fd) h) = []
Proof
  qspecl_then [‘fd’, ‘h’] mp_tac (Q.GEN ‘fd’ handler_echoes)
  >> simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac
  >> first_x_assum drule >> gvs[on_fd_def, is_accept_def]
QED

Theorem handler_only_fd[local]:
  g ≠ fd ⇒ FILTER (on_fd g) (trans (handler fd) h) = []
Proof
  qspecl_then [‘fd’, ‘h’] mp_tac (Q.GEN ‘fd’ handler_echoes)
  >> simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac
  >> first_x_assum drule >> gvs[on_fd_def]
QED

(* MAIN: the server's invariant.  If the connections the world hands out are
   distinct, then on every connection fd the server writes back exactly the
   data it has read from fd, in order; and it only ever reads or writes
   connections it has accepted. *)
Theorem server_echoes:
  ∀h. fresh (trans (server lfd) h) ⇒
      (∀fd. written fd (trans (server lfd) h) = read fd (trans (server lfd) h)) ∧
      (∀fd. EXISTS (on_fd fd) (trans (server lfd) h) ⇒
            MEM fd (accepted (trans (server lfd) h)))
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’
  >> ONCE_REWRITE_TAC[server_unfold]
  (* wait until the listener is readable *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable lfd) K0) h’
  >> qspecl_then [‘readable lfd’, ‘K0’, ‘h’] mp_tac
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
  >> qabbrev_tac ‘L = left_view (handler fd) (server lfd) h2'’
  >> qabbrev_tac ‘R = right_view (handler fd) (server lfd) h2'’
  >> ‘LENGTH R < LENGTH h1 + (LENGTH h2' + 1)’ by simp[Abbr ‘R’]
  >> ‘accepted (trans (both (handler fd) (server lfd)) h2') =
      accepted (trans (server lfd) R)’
       by (ONCE_REWRITE_TAC[GSYM accepted_FILTER] >> AP_TERM_TAC
           >> simp[Abbr ‘R’] >> irule trans_both_filter_right
           >> simp[handler_no_accept])
  >> simp[fresh_def] >> strip_tac
  >> first_x_assum (qspec_then ‘R’ mp_tac) >> simp[fresh_def] >> strip_tac
  (* the rest of the server never touches fd *)
  >> ‘FILTER (on_fd fd) (trans (server lfd) R) = []’
       by (CCONTR_TAC >> gvs[GSYM EXISTS_FILTER] >> res_tac)
  >> ‘FILTER (on_fd fd) (trans (both (handler fd) (server lfd)) h2') =
      FILTER (on_fd fd) (trans (handler fd) L)’
       by (simp[Abbr ‘L’] >> irule trans_both_filter_left >> fs[Abbr ‘R’])
  >> ‘∀g. g ≠ fd ⇒
          FILTER (on_fd g) (trans (both (handler fd) (server lfd)) h2') =
          FILTER (on_fd g) (trans (server lfd) R)’
       by (rpt strip_tac >> simp[Abbr ‘R’] >> irule trans_both_filter_right
           >> simp[handler_only_fd])
  >> conj_tac
  >- (gen_tac >> Cases_on ‘fd' = fd’
      >- (ONCE_REWRITE_TAC[GSYM written_FILTER, GSYM read_FILTER] >> gvs[]
          >> simp[written_FILTER, read_FILTER, handler_echoes])
      >> ONCE_REWRITE_TAC[GSYM written_FILTER, GSYM read_FILTER]
      >> first_x_assum drule >> simp[] >> strip_tac
      >> simp[written_FILTER, read_FILTER])
  >> rpt strip_tac >> Cases_on ‘fd' = fd’ >> simp[]
  >> first_x_assum (qspec_then ‘fd'’ mp_tac) >> simp[] >> strip_tac
  >> gvs[EXISTS_FILTER]
QED

(* MAIN: M4's safety property, in the model.  If the connections the world
   hands out are distinct, then for every connection fd, the data the server
   has written to fd is exactly the data it has read from fd, in order: each
   client gets back its own data, never another client's, never reordered,
   and nothing it sent is held back. *)
Theorem echo_server_safety:
  fresh (trans (server lfd) h) ⇒
  ∀fd. written fd (trans (server lfd) h) = read fd (trans (server lfd) h)
Proof
  metis_tac[server_echoes]
QED

(* ------------------------------------------------------------------------
   Sanity check: two clients, interleaved
   ------------------------------------------------------------------------ *)

Definition snap_def:
  snap rdy res = <| ready := rdy; now := 0; results := res |>
End

(* Client 5 connects and sends "hi"; while it is being served, client 6
   connects and sends "yo".  Each gets back exactly its own data. *)
Definition two_clients_def:
  two_clients =
    [snap {Readable 0} [];                       (* a connection is pending *)
     snap {} [Accepted 5];                       (* it is fd 5 *)
     snap {Readable 0; Readable 5} [];           (* 5 has data; another connection *)
     snap {} [Data "hi"; Accepted 6];            (* 5 sent "hi"; the new one is fd 6 *)
     snap {Readable 5; Readable 6} [Written];    (* 6 has data too *)
     snap {} [Data "yo"]]                        (* 6 sent "yo" *)
End

Theorem example_two_clients_log:
  (server 0 two_clients).actions =
    [Accept 0; Read 5; Accept 0; Write 5 "hi"; Read 6; Write 6 "yo"]
Proof
  EVAL_TAC
QED

(* The transcript: each action with its response (the last write's
   acknowledgement has not arrived yet) *)
Theorem example_two_clients_transcript:
  trans (server 0) two_clients =
    [(Accept 0, SOME (Accepted 5)); (Read 5, SOME (Data "hi"));
     (Accept 0, SOME (Accepted 6)); (Write 5 "hi", SOME Written);
     (Read 6, SOME (Data "yo")); (Write 6 "yo", NONE)]
Proof
  EVAL_TAC
QED

Theorem example_two_clients_echo:
  written 5 (trans (server 0) two_clients) = ["hi"] ∧
  read 5 (trans (server 0) two_clients) = ["hi"] ∧
  written 6 (trans (server 0) two_clients) = ["yo"] ∧
  read 6 (trans (server 0) two_clients) = ["yo"]
Proof
  EVAL_TAC
QED
