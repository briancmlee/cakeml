(*
  EchoSpec bites: the statement rules out plausible bugs, and its
  assumptions are satisfiable.  Everything here is proved.

  - Concrete I/O events, built exactly as the socket model's FFI functions
    produce them (rd: a «sock_read» that returned data; wr: a «sock_write»).
  - Broken servers: a trace that swaps two clients' data, drops a byte,
    duplicates a byte, or never echoes violates the spec.
  - Non-vacuity: a fair world exists (the socket worker's hello_world, with
    one connection sending "hi\n"), and an ideal echo trace for it is both
    safe and live.
*)
Theory EchoSpecBite
Ancestors
  EchoSpec socketWorld socketFair llist Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   Concrete events
   ------------------------------------------------------------------------ *)

(* A «sock_read» on c with a buffer of n data bytes that returned bs *)
Definition rd_def:
  rd c bs n =
    IO_event (ExtCall «sock_read») (fd_bytes c)
      (ZIP (REPLICATE (n + 9) 0w,
            0w :: n2w8 (LENGTH bs) ++ bs ++ REPLICATE (n - LENGTH bs) 0w))
End

(* A «sock_write» of bs on c *)
Definition wr_def:
  wr c bs = IO_event (ExtCall «sock_write») (fd_bytes c ++ bs) []
End

(* Two clients and some bytes ("a", "b", "c") *)
Overload c1 = “4w : word64”
Overload c2 = “5w : word64”
Overload A = “[97w] : word8 list”
Overload B = “[98w] : word8 list”

(* A trace that has evs as a finite prefix *)
Overload starts_with = “λevs io. LPREFIX (fromList evs) io”

(* ------------------------------------------------------------------------
   Broken servers violate safety
   ------------------------------------------------------------------------ *)

Theorem broken_swaps_clients:
  starts_with [rd c1 A 100; rd c2 B 100; wr c1 B; wr c2 A] io ⇒
  ¬echo_safe io
Proof
  rw[echo_safe_def] >>
  qexistsl [‘[rd c1 A 100; rd c2 B 100; wr c1 B; wr c2 A]’, ‘c1’] >>
  simp[] >> EVAL_TAC
QED

Theorem broken_drops_a_byte:
  starts_with [rd c1 (A ++ B ++ A) 100; wr c1 (A ++ A)] io ⇒
  ¬echo_safe io
Proof
  rw[echo_safe_def] >>
  qexistsl [‘[rd c1 (A ++ B ++ A) 100; wr c1 (A ++ A)]’, ‘c1’] >>
  simp[] >> EVAL_TAC
QED

Theorem broken_duplicates_a_byte:
  starts_with [rd c1 (A ++ B) 100; wr c1 (A ++ A ++ B)] io ⇒
  ¬echo_safe io
Proof
  rw[echo_safe_def] >>
  qexistsl [‘[rd c1 (A ++ B) 100; wr c1 (A ++ A ++ B)]’, ‘c1’] >>
  simp[] >> EVAL_TAC
QED

Theorem broken_writes_before_reading:
  starts_with [wr c1 A] io ⇒ ¬echo_safe io
Proof
  rw[echo_safe_def] >> qexistsl [‘[wr c1 A]’, ‘c1’] >> simp[] >> EVAL_TAC
QED

(* ------------------------------------------------------------------------
   A server that never echoes violates liveness
   ------------------------------------------------------------------------ *)

Theorem hello_world_sends:
  sent_upto 4w 1 hello_world = [104w; 105w; 10w]
Proof
  EVAL_TAC
QED

Theorem broken_never_echoes:
  (∀evs. starts_with evs io ⇒ bytes_written_to 4w evs = []) ⇒
  ¬echo_live hello_world io
Proof
  rw[echo_live_def] >> qexistsl [‘4w’, ‘1’] >> rw[hello_world_sends] >>
  Cases_on ‘LPREFIX (fromList evs) io’ >> simp[] >> res_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   Non-vacuity
   ------------------------------------------------------------------------ *)

(* A fair world for the echo server exists *)
Theorem server_world_exists:
  server_world 3w hello_world
Proof
  simp[server_world_def, hello_world_sched_wf] >> EVAL_TAC
QED

Theorem LPREFIX_fromList_fromList[local]:
  LPREFIX (fromList xs) (fromList ys) ⇔ xs ≼ ys
Proof
  simp[LPREFIX_fromList, from_toList]
QED

Theorem sent_upto_hello_world[local]:
  sent_upto c n hello_world =
    if n = 0 ∨ c ≠ 4w then [] else [104w; 105w; 10w]
Proof
  Cases_on ‘n’ >> simp[sent_upto_def, arrivals_upto_def] >>
  simp[hello_world_def] >>
  Cases_on ‘n'’ >> simp[arrivals_upto_def] >> rw[]
QED

Theorem prefix_two[local]:
  evs ≼ [x; y] ⇔ evs = [] ∨ evs = [x] ∨ evs = [x; y]
Proof
  Cases_on ‘evs’ >> simp[] >> Cases_on ‘t’ >> simp[] >>
  Cases_on ‘t'’ >> simp[]
QED

(* The ideal echo of hello_world: read "hi\n" from 4, write it back *)
Overload ideal = “fromList [rd 4w [104w; 105w; 10w] 100; wr 4w [104w; 105w; 10w]]”

(* The safety and liveness predicates are jointly satisfiable *)
Theorem ideal_trace_safe_and_live:
  echo_safe ideal ∧ echo_live hello_world ideal
Proof
  conj_tac
  >- (rw[echo_safe_def, LPREFIX_fromList_fromList, prefix_two] >>
      EVAL_TAC >> rw[] >> EVAL_TAC)
  >- (rw[echo_live_def, sent_upto_hello_world] >>
      qexists_tac ‘[rd 4w [104w; 105w; 10w] 100; wr 4w [104w; 105w; 10w]]’ >>
      simp[LPREFIX_fromList_fromList] >> rw[] >> fs[] >> EVAL_TAC)
QED
