(*
  ChatSpec: what a verified chat (broadcast) server does, on raw socket I/O.

  TRUSTED SURFACE.  It reuses EchoSpec's world (the sockets-only FFI, the
  worlds server_world, the per-connection projections bytes_read_from /
  bytes_written_to, and sent_upto) and adds only what is below.

  The service.  Clients connect to one listening socket and send lines
  (byte strings ending in a newline, 10w).  The server relays every line,
  verbatim, to every connected client, the sender included.

  The global order is the order in which the server finished READING the
  lines: an event of the trace that reads from connection c "completes"
  the lines of c whose newline it read.  So all clients see one order,
  and that order respects real time as the server saw it: a line the
  server had completely read before another line was even started comes
  first, for everybody.

  A client d is owed exactly the lines completed after the server
  accepted d's connection (no backlog, nothing missed), in that order.

  Safety (chat_safe): at every point of the run, everything written to
  every client is a prefix of what it is owed.  This rules out dropping,
  duplicating, reordering (including between clients), relaying a line
  before its newline has been read, inventing data, and writing to a
  connection that has not been accepted.

  Liveness (chat_live): every pending connection is eventually accepted,
  every complete line a client sends is eventually read, and whatever a
  client is owed at some point is eventually written to it.

  ChatSpecBiteScript.sml proves that broken servers violate the
  statement and that it is satisfiable.
*)
Theory ChatSpec
Ancestors
  semantics ffi llist ml_prog ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   Lines
   ------------------------------------------------------------------------ *)

(* The complete lines at the front of bs: bs up to and including its last
   newline (all of bs if it ends with one, [] if it has none). *)
Definition whole_lines_def:
  whole_lines (bs : word8 list) =
    REVERSE (dropWhile (λb. b ≠ 10w) (REVERSE bs))
End

(* ------------------------------------------------------------------------
   The order in which the server completes lines
   ------------------------------------------------------------------------ *)

(* The connection an event is about: its first 8 config bytes (for a read,
   the connection read from). *)
Definition event_fd_def:
  event_fd (IO_event n conf bytes) = bytes_fd (TAKE 8 conf)
End

(* The lines that event e, coming after the events evs, completes: the new
   complete lines of e's connection.  Empty unless e reads a newline. *)
Definition completes_def:
  completes evs e =
    DROP (LENGTH (whole_lines (bytes_read_from (event_fd e) evs)))
         (whole_lines (bytes_read_from (event_fd e) (evs ++ [e])))
End

(* All lines completed in evs, in the order the server completed them *)
Definition relayed_def:
  relayed evs =
    FLAT (GENLIST (λk. completes (TAKE k evs) (EL k evs)) (LENGTH evs))
End

(* ------------------------------------------------------------------------
   Who is owed what
   ------------------------------------------------------------------------ *)

(* e is a «sock_accept» that returned the new connection d (status byte 1,
   then d's 8 bytes) *)
Definition event_accepts_def:
  event_accepts d (IO_event (ExtCall n) conf bytes) =
    (n = «sock_accept» ∧ MAP SND bytes = 1w :: fd_bytes d) ∧
  event_accepts d _ = F
End

(* What client d is owed after the events evs: the lines completed after
   d's connection was accepted, in order ([] if it has not been). *)
Definition owed_def:
  owed d evs =
    case SPLITP (event_accepts d) evs of
    | (before, []) => []
    | (before, acc) => DROP (LENGTH (relayed before)) (relayed evs)
End

(* d connected within the first n steps of the schedule *)
Definition connects_upto_def:
  connects_upto d n sk ⇔ ∃l. MEM (Connect l d) (arrivals_upto n sk.sched)
End

(* ------------------------------------------------------------------------
   The specification
   ------------------------------------------------------------------------ *)

(* Safety: at every point, every client has been sent a prefix of what it
   is owed. *)
Definition chat_safe_def:
  chat_safe io ⇔
    ∀evs d. LPREFIX (fromList evs) io ⇒ bytes_written_to d evs ≼ owed d evs
End

(* Liveness: connections are accepted, complete lines are read, and what
   is owed is delivered. *)
Definition chat_live_def:
  chat_live sk io ⇔
    (∀d n. connects_upto d n sk ⇒
           ∃evs. LPREFIX (fromList evs) io ∧ EXISTS (event_accepts d) evs) ∧
    (∀c n. ∃evs. LPREFIX (fromList evs) io ∧
                 whole_lines (sent_upto c n sk) ≼ bytes_read_from c evs) ∧
    (∀d evs. LPREFIX (fromList evs) io ⇒
             ∃evs'. LPREFIX (fromList evs') io ∧
                    owed d evs ≼ bytes_written_to d evs')
End

(* THE STATEMENT (to be proved for the chat server's program, lfd = 3w):
   in every fair world with one listener lfd, the program runs forever, and
   its I/O trace is safe and live. *)
Definition chat_spec_def:
  chat_spec lfd (prog : dec list) ⇔
    ∀sk. server_world lfd sk ⇒
         ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog
                (Diverge io) ∧
              chat_safe io ∧ chat_live sk io
End
