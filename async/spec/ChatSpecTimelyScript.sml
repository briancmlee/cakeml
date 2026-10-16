(*
  ChatSpecTimely: a CANDIDATE strengthening of ChatSpec, for review.
  ChatSpec itself is unchanged; this file only adds definitions.

  TRUSTED SURFACE (if adopted).  It answers three adequacy findings on
  ChatSpec (design/42-chat-timely-gc.md):

  C-DELAY.  chat_live only says "eventually": a server may delay every
  line by any number of rounds.  The trace has no clock, but the server's
  own polls are visible (each «sock_poll» event), and in the socket world
  each poll is one step of the schedule.  chat_prompt B: whatever a client
  is owed at some point is written to it before B more polls have
  happened.  (A server that never polls meets it only by delivering
  eventually; but a server that waits for readiness has to poll.)

  C-JOIN.  What a client is owed starts at the server's accept, so a
  server could leave a connection pending for a long time, and the client
  misses everything said meanwhile.  chat_accept_prompt A: at the n-th
  poll, a connection that arrived within the first n steps of the
  schedule is accepted within A more polls per connection still waiting
  (see T2 below).  A line read in the same round, before the accept, is
  still not owed to it: a one-round granularity no server can avoid.

  C-EOF.  A client whose end-of-stream the server has read stays owed
  every later line forever, so a correct server that stops serving
  departed clients fails chat_live.  owed_open d evs: what d is owed, but
  counting only lines completed before the server read d's EOF.
  chat_live_open is chat_live with owed_open in the delivery clause.
  Writing more (up to owed) is still allowed by chat_safe.

  T1 (review of this file).  chat_prompt bounds read-to-write, but reading
  itself was still "eventually".  chat_read_prompt R: the complete lines a
  client sent within n steps are read within R polls per arrived
  connection and per byte (a read may return one byte; the client must
  first be accepted).

  T2 (review of this file).  The accept bound now counts the CURRENT
  backlog at the n-th poll (connections arrived, less those accepted so
  far), not every connection since the start.

  chat_spec_timely B A R: chat_safe, chat_live_open, chat_prompt B,
  chat_accept_prompt A and chat_read_prompt R.  ChatSpecTimelyBiteScript.sml proves what each
  clause rules out and that ChatSpec's chat_live implies chat_live_open.
*)
Theory ChatSpecTimely
Ancestors
  semantics ffi llist ml_prog ffiSpikeSocketFFI ffiSpikeSocketFair
  EchoSpec ChatSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   The server's clock: its polls
   ------------------------------------------------------------------------ *)

Definition is_poll_def:
  is_poll (IO_event (ExtCall n) conf bytes) = (n = «sock_poll») ∧
  is_poll _ = F
End

Definition polls_def:
  polls evs = LENGTH (FILTER is_poll evs)
End

(* ------------------------------------------------------------------------
   C-EOF: what a departed client is owed
   ------------------------------------------------------------------------ *)

(* e is a «sock_read» on d that returned end-of-stream (status byte 2) *)
Definition event_eof_def:
  event_eof d (IO_event (ExtCall n) conf bytes) =
    (n = «sock_read» ∧ LENGTH conf = 8 ∧ bytes_fd conf = d ∧
     bytes ≠ [] ∧ SND (HD bytes) = 2w) ∧
  event_eof d _ = F
End

(* What d is owed, counting only the lines completed before the server
   read d's end-of-stream *)
Definition owed_open_def:
  owed_open d evs = owed d (FST (SPLITP (event_eof d) evs))
End

Definition chat_live_open_def:
  chat_live_open sk io ⇔
    (∀d n. connects_upto d n sk ⇒
           ∃evs. LPREFIX (fromList evs) io ∧ EXISTS (event_accepts d) evs) ∧
    (∀c n. ∃evs. LPREFIX (fromList evs) io ∧
                 whole_lines (sent_upto c n sk) ≼ bytes_read_from c evs) ∧
    (∀d evs. LPREFIX (fromList evs) io ⇒
             ∃evs'. LPREFIX (fromList evs') io ∧
                    owed_open d evs ≼ bytes_written_to d evs')
End

(* ------------------------------------------------------------------------
   C-DELAY: bounded latency, in polls
   ------------------------------------------------------------------------ *)

(* What d is owed at any point is written to d before B more polls *)
Definition chat_prompt_def:
  chat_prompt B io ⇔
    ∀evs d. LPREFIX (fromList evs) io ⇒
            ∃evs'. LPREFIX (fromList evs') io ∧ polls evs' ≤ polls evs + B ∧
                   owed_open d evs ≼ bytes_written_to d evs'
End

(* ------------------------------------------------------------------------
   C-JOIN: prompt accepts, against the current backlog
   ------------------------------------------------------------------------ *)

(* The connections that arrived within the first n steps *)
Definition nconnects_def:
  nconnects n sk =
    LENGTH (FILTER (λa. case a of Connect l c => T | _ => F)
                    (arrivals_upto n sk.sched))
End

(* e is a «sock_accept» that returned a connection (status byte 1) *)
Definition is_accept_ev_def:
  is_accept_ev (IO_event (ExtCall n) conf bytes) =
    (n = «sock_accept» ∧ bytes ≠ [] ∧ SND (HD bytes) = 1w) ∧
  is_accept_ev _ = F
End

Definition naccepts_def:
  naccepts evs = LENGTH (FILTER is_accept_ev evs)
End

(* At the n-th poll (the prefix evs0 of the trace that ends with it), a
   connection d that arrived within the first n steps is accepted within
   A more polls per connection still waiting: the connections that have
   arrived, less those accepted so far. *)
Definition chat_accept_prompt_def:
  chat_accept_prompt A sk io ⇔
    ∀d n evs0. connects_upto d n sk ∧ LPREFIX (fromList evs0) io ∧
               polls evs0 = n ∧ (evs0 ≠ [] ⇒ is_poll (LAST evs0)) ⇒
               ∃evs. LPREFIX (fromList evs) io ∧
                     polls evs ≤ n + A * (nconnects n sk − naccepts evs0) ∧
                     EXISTS (event_accepts d) evs
End

(* ------------------------------------------------------------------------
   T1: prompt reads
   ------------------------------------------------------------------------ *)

(* The complete lines c sent within the first n steps are read within
   R polls per connection that has arrived and per byte sent (a read may
   return as little as one byte, and c must first be accepted). *)
Definition chat_read_prompt_def:
  chat_read_prompt R sk io ⇔
    ∀c n. ∃evs. LPREFIX (fromList evs) io ∧
                polls evs ≤ n + R * (1 + nconnects n sk + LENGTH (sent_upto c n sk)) ∧
                whole_lines (sent_upto c n sk) ≼ bytes_read_from c evs
End

(* ------------------------------------------------------------------------
   The candidate statement
   ------------------------------------------------------------------------ *)

Definition chat_spec_timely_def:
  chat_spec_timely B A R lfd (prog : dec list) ⇔
    ∀sk. server_world lfd sk ⇒
         ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog
                (Diverge io) ∧
              chat_safe io ∧ chat_live_open sk io ∧
              chat_prompt B io ∧ chat_accept_prompt A sk io ∧
              chat_read_prompt R sk io
End
