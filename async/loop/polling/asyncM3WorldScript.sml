(*
  M3 assembly, pure HOL side: the async library's actions are socket
  operations, performed against the socket model (ffiSpikeSocketFFI).

  - A library computation emits actions of type sact (accept on a
    listener, read at most n bytes from a connection, write bytes to a
    connection) and receives responses of type sresp (the operation's
    result).
  - Each round, the event loop performs the round's actions in order, one
    Socket call each, then calls Socket.poll on a fixed list of interest
    fds, which also lets one step of the world's schedule arrive.  The
    snapshot is <| ready := the ready fds; now := 0; results := the
    responses |>.
  - srounds defines the history this socket world generates for a model
    computation m, and sround_events the I/O events of each round (the
    socket calls' events, then the poll's event).
  - The trace lemma: the actions recorded in the socket events of the
    first n+1 rounds are exactly m's action log on that history.

  The socket operations fail (the FFI call fails) on misuse, e.g. a read
  on an fd that is not a connection.  srun_ok says that this never
  happens in the run; it is a hypothesis of the loop theorem.
*)
Theory asyncM3World
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel ffiSpikeSocketFFI ffi
  llist Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   Actions and responses
   ------------------------------------------------------------------------ *)

Datatype:
  sact = Accept word64 | Read word64 num | Write word64 (word8 list)
End

Datatype:
  sresp = Accepted (word64 option) | Got ((word8 list) option) | Wrote
End

(* Performing one action in the socket world: its response and the next
   state, or NONE on misuse (the FFI call would fail). *)
Definition sock_do_def:
  sock_do s (Accept l) =
    OPTION_MAP (λ(r, s'). (Accepted r, s')) (sock_accept l s) ∧
  sock_do s (Read c n) =
    (if 0 < n ∧ n < 256 ** 8 then
       OPTION_MAP (λ(r, s'). (Got r, s')) (sock_read c n s)
     else NONE) ∧
  sock_do s (Write c bs) =
    OPTION_MAP (λs'. (Wrote, s')) (sock_write c bs s)
End

(* The bytes «sock_read» writes into a buffer with n data bytes (the same
   as ffiSpikeSocketProof's read_bytes) *)
Definition sread_out_def:
  sread_out n r =
    case r of
    | NONE => 1w :: REPLICATE (n + 8) 0w
    | SOME d =>
        if d = [] then 2w :: REPLICATE (n + 8) (0w:word8)
        else 0w :: n2w8 (LENGTH d) ++ d ++ REPLICATE (n − LENGTH d) 0w
End

(* The I/O event of the Socket call that performs action a with response r *)
Definition act_event_def:
  act_event (Accept l) (Accepted r) =
    IO_event (ExtCall «sock_accept») (fd_bytes l)
      (ZIP (REPLICATE 9 0w,
            case r of NONE => 0w :: REPLICATE 8 0w | SOME c => 1w :: fd_bytes c)) ∧
  act_event (Read c n) (Got r) =
    IO_event (ExtCall «sock_read») (fd_bytes c)
      (ZIP (REPLICATE (n + 9) 0w, sread_out n r)) ∧
  act_event (Write c bs) Wrote =
    IO_event (ExtCall «sock_write») (fd_bytes c ++ bs) [] ∧
  act_event _ _ = IO_event (ExtCall «») [] []
End

(* The I/O event of Socket.poll on fds in state s (the same as
   ffiSpikeSocketDiv's poll_event) *)
Definition spoll_event_def:
  spoll_event fds s =
    IO_event (ExtCall «sock_poll») (fds_bytes fds)
      (ZIP (REPLICATE (LENGTH fds) 0w,
            MAP (λfd. if is_ready (tick s) fd then 1w else 0w) fds))
End

(* Performing a round's actions in order: the responses, the events and
   the next state, or NONE if some action is a misuse. *)
Definition sock_acts_def:
  sock_acts s [] = SOME ([], [], s) ∧
  sock_acts s (a :: acts) =
    case sock_do s a of
    | NONE => NONE
    | SOME (r, s1) =>
        case sock_acts s1 acts of
        | NONE => NONE
        | SOME (rs, evs, s2) => SOME (r :: rs, act_event a r :: evs, s2)
End

(* The same, total (misuse: no responses, no change); only used to define
   the history, under srun_ok *)
Definition sock_acts_tot_def:
  sock_acts_tot s acts =
    case sock_acts s acts of SOME x => x | NONE => ([], [], s)
End

(* ------------------------------------------------------------------------
   The history the socket world generates
   ------------------------------------------------------------------------ *)

(* The snapshot of one round: the ready fds among the interest fds (after
   the poll), and the responses *)
Definition ssnap_def:
  ssnap rdy rs = <| ready := set rdy; now := 0; results := rs |>
End

(* srounds fds m s0 n = (h, s): after n rounds of the loop running m with
   interest fds in the socket world started in s0, the history m has been
   polled with and the world's state. *)
Definition srounds_def:
  srounds fds m s0 0 = ([], s0) ∧
  srounds fds m s0 (SUC n) =
    let (h, s) = srounds fds m s0 n;
        (rs, evs, s1) = sock_acts_tot s (new_actions (log_of m) h);
        (rdy, s2) = sock_poll fds s1
    in (h ++ [ssnap rdy rs], s2)
End

Definition shist_def:
  shist fds m s0 n = FST (srounds fds m s0 n)
End

(* The I/O events of round n: the socket calls of m's new actions, then
   the poll *)
Definition sround_events_def:
  sround_events fds m s0 n =
    let (h, s) = srounds fds m s0 n;
        (rs, evs, s1) = sock_acts_tot s (new_actions (log_of m) h)
    in evs ++ [spoll_event fds s1]
End

(* No action of the run is a misuse *)
Definition srun_ok_def:
  srun_ok fds m s0 ⇔
    ∀n. sock_acts (SND (srounds fds m s0 n))
                  (new_actions (log_of m) (FST (srounds fds m s0 n))) ≠ NONE
End

Theorem srounds_SUC:
  srounds fds m s0 (SUC n) =
    (FST (srounds fds m s0 n) ++
       [ssnap (FST (sock_poll fds
                 (SND (SND (sock_acts_tot (SND (srounds fds m s0 n))
                    (new_actions (log_of m) (FST (srounds fds m s0 n))))))))
              (FST (sock_acts_tot (SND (srounds fds m s0 n))
                    (new_actions (log_of m) (FST (srounds fds m s0 n)))))],
     SND (sock_poll fds
            (SND (SND (sock_acts_tot (SND (srounds fds m s0 n))
               (new_actions (log_of m) (FST (srounds fds m s0 n))))))))
Proof
  simp[srounds_def] >> Cases_on ‘srounds fds m s0 n’ >> simp[] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem sround_events_alt:
  sround_events fds m s0 n =
    FST (SND (sock_acts_tot (SND (srounds fds m s0 n))
               (new_actions (log_of m) (FST (srounds fds m s0 n))))) ++
    [spoll_event fds
       (SND (SND (sock_acts_tot (SND (srounds fds m s0 n))
                    (new_actions (log_of m) (FST (srounds fds m s0 n))))))]
Proof
  simp[sround_events_def] >> Cases_on ‘srounds fds m s0 n’ >> simp[] >>
  rpt (pairarg_tac >> gvs[])
QED

(* ------------------------------------------------------------------------
   The actions recorded in a socket trace
   ------------------------------------------------------------------------ *)

(* The action a socket event performed (none for poll and other events) *)
Definition sevent_actions_def:
  sevent_actions (IO_event (ExtCall n) conf bytes) =
    (if n = «sock_accept» then [Accept (bytes_fd conf)]
     else if n = «sock_read» then [Read (bytes_fd conf) (LENGTH bytes - 9)]
     else if n = «sock_write» then [Write (bytes_fd (TAKE 8 conf)) (DROP 8 conf)]
     else []) ∧
  sevent_actions _ = []
End

Definition strace_actions_def:
  strace_actions evs = FLAT (MAP sevent_actions evs)
End

Theorem LENGTH_sread_out:
  (∀d. r = SOME d ⇒ LENGTH d ≤ n) ⇒ LENGTH (sread_out n r) = n + 9
Proof
  rw[sread_out_def] >> every_case_tac >> gvs[LENGTH_n2w8]
QED

Theorem sevent_actions_act_event:
  sock_do s a = SOME (r, s') ⇒ sevent_actions (act_event a r) = [a]
Proof
  Cases_on ‘a’ >>
  rw[sock_do_def, OPTION_MAP_EQ_SOME, pairTheory.EXISTS_PROD] >>
  gvs[act_event_def, sevent_actions_def]
  >- (rename1 ‘sock_read c n s = SOME (rr, _)’ >>
      ‘∀d. rr = SOME d ⇒ LENGTH d ≤ n’
        by (rw[] >> imp_res_tac sock_read_LENGTH) >>
      simp[LENGTH_ZIP_MIN, LENGTH_sread_out])
  >- (‘8 = LENGTH (fd_bytes c)’ by simp[] >>
      pop_assum SUBST1_TAC >>
      simp[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND])
QED

Theorem strace_actions_sock_acts:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ⇒ strace_actions evs = acts
Proof
  Induct >> rw[sock_acts_def, strace_actions_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac sevent_actions_act_event >> gvs[strace_actions_def] >>
  metis_tac[]
QED

Theorem strace_actions_spoll_event[simp]:
  strace_actions [spoll_event fds s] = []
Proof
  simp[strace_actions_def, spoll_event_def, sevent_actions_def]
QED

Theorem strace_actions_APPEND:
  strace_actions (xs ++ ys) = strace_actions xs ++ strace_actions ys
Proof
  simp[strace_actions_def]
QED

(* One round: its events perform exactly the model's new actions *)
Theorem strace_actions_round:
  srun_ok fds m s0 ⇒
  strace_actions (sround_events fds m s0 n) =
  new_actions (log_of m) (shist fds m s0 n)
Proof
  rw[srun_ok_def, sround_events_alt, shist_def, strace_actions_APPEND] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >>
  qmatch_goalsub_abbrev_tac ‘sock_acts s acts’ >>
  Cases_on ‘sock_acts s acts’ >> simp[] >> PairCases_on ‘x’ >>
  simp[sock_acts_tot_def] >> metis_tac[strace_actions_sock_acts]
QED

(* MAIN: the socket trace and the model agree.  If no action of the run
   is a misuse, the actions performed by the socket calls in the first n+1
   rounds of the loop's trace are exactly the model computation's action
   log on the history the socket world generates. *)
Theorem strace_actions_rounds:
  srun_ok fds m s0 ∧ wf m ⇒
  strace_actions (FLAT (GENLIST (sround_events fds m s0) (SUC n))) =
  (m (shist fds m s0 n)).actions
Proof
  strip_tac >> Induct_on ‘n’
  >- (simp[strace_actions_round] >>
      simp[shist_def, srounds_def, new_actions_NIL, log_of_def]) >>
  ONCE_REWRITE_TAC[GENLIST] >>
  simp[SNOC_APPEND, FLAT_APPEND, strace_actions_APPEND, strace_actions_round] >>
  simp[shist_def, srounds_SUC] >>
  gvs[shist_def] >>
  qmatch_goalsub_abbrev_tac ‘new_actions _ (h ++ [sn])’ >>
  ‘log_of m h ≼ log_of m (h ++ [sn])’ by simp[log_of_def, wf_SNOC_actions] >>
  drule new_actions_prefix >> simp[log_of_def]
QED
