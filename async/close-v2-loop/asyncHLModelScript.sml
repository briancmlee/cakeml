(*
  The handle layer, in the model: how the event loop runs a library
  computation in the version-2 world (close, fd reuse) while the
  computation sees a version-1 world.

  The computation (e.g. the echo server, unchanged) emits version-1
  socket actions (asyncM3World's sact) on HANDLES.  The loop keeps a table
  of the open handles and their current fds:
   - Accept l: a new connection on fd f gets a fresh handle, the j-th
     handle hdl lfd j (handles are never reused; the listener's number is
     skipped);
   - Read h n: reads the fd of h; when the read returns EOF the loop
     closes the fd (AUTO-CLOSE) and drops h from the table.  A read on a
     handle not in the table (closed) returns EOF, as a version-1
     connection does after its EOF;
   - Write h bs: writes to the fd of h (nothing, if h is closed);
   - the poll: the listener is polled as itself, open handles through their
     fds; closed handles are reported ready (EOF), as in version 1.

  hdo performs one action (its response, the next state, its I/O events),
  hrounds the history and states of the whole run, hround_events each
  round's events; hrun_ok says no action of the run is a misuse.
*)
Theory asyncHLModel
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel ffiSpikeSocketFFI ffi
  asyncM3World socketV2FFI socketV2Proof llist alist
Libs
  preamble

(* ------------------------------------------------------------------------
   Handles
   ------------------------------------------------------------------------ *)

(* The open handles and their fds; the number of handles issued so far *)
Datatype:
  hstate = <| tbl : (word64 # word64) list; nxt : num |>
End

Definition hinit_def:
  hinit = <| tbl := []; nxt := 0 |>
End

(* The j-th handle, skipping the listener's number *)
Definition hdln_def:
  hdln (lfdn:num) (j:num) = if j < lfdn then j else j + 1
End

Definition hdl_def:
  hdl (lfd:word64) j : word64 = n2w (hdln (w2n lfd) j)
End

(* ------------------------------------------------------------------------
   One action
   ------------------------------------------------------------------------ *)

(* Performing action a: its response, the next world and handle state, and
   its I/O events; NONE on misuse (an FFI call would fail, or the handles
   would overflow) *)
Definition hdo_def:
  hdo lfd (s, hs) (Accept l) =
    (case sock_accept2 l s of
     | NONE => NONE
     | SOME (NONE, s') =>
         SOME (Accepted NONE, (s', hs), [act_event (Accept l) (Accepted NONE)])
     | SOME (SOME f, s') =>
         if hdln (w2n lfd) hs.nxt < dimword (:64) then
           SOME (Accepted (SOME (hdl lfd hs.nxt)),
                 (s', hs with <| tbl := (hdl lfd hs.nxt, f) :: hs.tbl;
                                 nxt := hs.nxt + 1 |>),
                 [act_event (Accept l) (Accepted (SOME f))])
         else NONE) ∧
  hdo lfd (s, hs) (Read h n) =
    (if 0 < n ∧ n < 256 ** 8 then
       case ALOOKUP hs.tbl h of
       | NONE => SOME (Got (SOME []), (s, hs), [])
       | SOME f =>
           case sock_read2 f n s of
           | NONE => NONE
           | SOME (SOME [], s') =>
               (case sock_close2 f s' of
                | NONE => NONE
                | SOME s'' =>
                    SOME (Got (SOME []), (s'', hs with tbl := ADELKEY h hs.tbl),
                          [act_event (Read f n) (Got (SOME [])); close_event f]))
           | SOME (r, s') => SOME (Got r, (s', hs), [act_event (Read f n) (Got r)])
     else NONE) ∧
  hdo lfd (s, hs) (Write h bs) =
    case ALOOKUP hs.tbl h of
    | NONE => SOME (Wrote, (s, hs), [])
    | SOME f =>
        OPTION_MAP (λs'. (Wrote, (s', hs), [act_event (Write f bs) Wrote]))
          (sock_write2 f bs s)
End

(* Performing a round's actions in order *)
Definition hacts_def:
  hacts lfd st [] = SOME ([], [], st) ∧
  hacts lfd st (a :: acts) =
    case hdo lfd st a of
    | NONE => NONE
    | SOME (r, st1, evs1) =>
        case hacts lfd st1 acts of
        | NONE => NONE
        | SOME (rs, evs, st2) => SOME (r :: rs, evs1 ++ evs, st2)
End

Definition hacts_tot_def:
  hacts_tot lfd st acts =
    case hacts lfd st acts of SOME x => x | NONE => ([], [], st)
End

(* ------------------------------------------------------------------------
   The poll
   ------------------------------------------------------------------------ *)

(* The fds polled for the interest handles hfds *)
Definition hpoll_fds_def:
  hpoll_fds lfd hs hfds =
    FLAT (MAP (λh. case ALOOKUP hs.tbl h of
                   | SOME f => [f]
                   | NONE => if h = lfd then [h] else []) hfds)
End

(* The ready handles, given the ready fds rdy *)
Definition hready_def:
  hready lfd hs rdy hfds =
    FILTER (λh. case ALOOKUP hs.tbl h of
                | SOME f => MEM f rdy
                | NONE => if h = lfd then MEM h rdy else T) hfds
End

Definition hpoll_def:
  hpoll lfd hs hfds s =
    let (rdy, s') = sock_poll2 (hpoll_fds lfd hs hfds) s in
      (hready lfd hs rdy hfds, s')
End

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

(* hrounds lfd ifds m s0 n = (h, (s, hs)): after n rounds of the handle
   loop running m, polling the handles ifds h, in the version-2 world
   started in s0: the history m has been polled with, the world and the
   handle state *)
Definition hrounds_def:
  hrounds lfd ifds m s0 0 = ([], (s0, hinit)) ∧
  hrounds lfd ifds m s0 (SUC n) =
    let (h, st) = hrounds lfd ifds m s0 n;
        (rs, evs, (s1, hs1)) = hacts_tot lfd st (new_actions (log_of m) h);
        (rdy, s2) = hpoll lfd hs1 (ifds h) s1
    in (h ++ [ssnap rdy rs], (s2, hs1))
End

Definition hhist_def:
  hhist lfd ifds m s0 n = FST (hrounds lfd ifds m s0 n)
End

Definition hst_def:
  hst lfd ifds m s0 n = SND (hrounds lfd ifds m s0 n)
End

Definition hacts_of_def:
  hacts_of lfd ifds m s0 n = new_actions (log_of m) (hhist lfd ifds m s0 n)
End

(* The I/O events of round n: those of m's new actions, then the poll *)
Definition hround_events_def:
  hround_events lfd ifds m s0 n =
    let (h, st) = hrounds lfd ifds m s0 n;
        (rs, evs, (s1, hs1)) = hacts_tot lfd st (new_actions (log_of m) h)
    in evs ++ [spoll2_event (hpoll_fds lfd hs1 (ifds h)) s1]
End

(* No action of the run is a misuse *)
Definition hrun_ok_def:
  hrun_ok lfd ifds m s0 ⇔
    ∀n. hacts lfd (hst lfd ifds m s0 n) (hacts_of lfd ifds m s0 n) ≠ NONE
End

Theorem hrounds_SUC:
  hrounds lfd ifds m s0 (SUC n) =
    let (rs, evs, (s1, hs1)) =
          hacts_tot lfd (hst lfd ifds m s0 n) (hacts_of lfd ifds m s0 n)
    in (hhist lfd ifds m s0 n ++
          [ssnap (FST (hpoll lfd hs1 (ifds (hhist lfd ifds m s0 n)) s1)) rs],
        (SND (hpoll lfd hs1 (ifds (hhist lfd ifds m s0 n)) s1), hs1))
Proof
  simp[hrounds_def, hhist_def, hst_def, hacts_of_def] >>
  Cases_on ‘hrounds lfd ifds m s0 n’ >> simp[] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem hround_events_alt:
  hround_events lfd ifds m s0 n =
    let (rs, evs, (s1, hs1)) =
          hacts_tot lfd (hst lfd ifds m s0 n) (hacts_of lfd ifds m s0 n)
    in evs ++ [spoll2_event (hpoll_fds lfd hs1 (ifds (hhist lfd ifds m s0 n))) s1]
Proof
  simp[hround_events_def, hhist_def, hst_def, hacts_of_def] >>
  Cases_on ‘hrounds lfd ifds m s0 n’ >> simp[] >>
  rpt (pairarg_tac >> gvs[])
QED
