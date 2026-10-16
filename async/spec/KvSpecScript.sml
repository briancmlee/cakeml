(*
  KvSpec: an HTTP KEY-VALUE server, whose clients share one store.
  APPROVED by the user (2026-10-16): real time starts at the first byte
  read; the behaviour is as drafted.  TRUSTED SURFACE, with HttpSpec
  (requests, framing, the response printer) and EchoSpec (the world, the
  per-connection projections), which are unchanged.

  What the server answers:
    GET k            200 with the value stored under k, or 404
    POST k, body v   stores v under k; 200 with an empty body
  The keys are the paths.  The store starts empty.

  The point is CONCURRENCY: all connections share the store.  The
  statement is LINEARIZABILITY at the level of the trace.  At every point
  of the run there is one order of all the complete requests read so far
  (on all connections) such that
   - each connection's requests are in the order it sent them;
   - it respects real time: if the server had written the whole response
     to a request x before it read any byte of a request y on another
     connection, x comes before y;
   - on every connection, what the server has written is a prefix of the
     responses that running the requests one by one, in that order, on a
     single store gives to that connection's requests.
  Liveness is as in HttpSpec: every request a client sends is
  eventually answered (by a whole response, whose content is safety's
  business).

  Zhang et al. (ITP 2021) verify a C key-value server against interaction
  trees, but state no such request-level linear specification and no
  liveness.  This file states both.  Design note 30 discusses why it is
  linearizability (and not sequential consistency), and its edge cases.
*)
Theory KvSpec
Ancestors
  EchoSpec HttpGetSpec HttpSpec rich_list
Libs
  preamble

(* ------------------------------------------------------------------------
   The store, and the server's intended behaviour on it, one at a time
   ------------------------------------------------------------------------ *)

Type store = “:string -> string option”

Definition kv_step_def:
  kv_step (st:store) (Req m k ver hs b) =
    if m = "POST" then (Ok "", (k =+ SOME b) st)
    else ((case st k of SOME v => Ok v | NONE => NotFound), st)
End

(* The responses to some requests, run one by one on a single store *)
Definition kv_run_def:
  kv_run st [] = [] ∧
  kv_run st (r :: rs) = let (a, st') = kv_step st r in a :: kv_run st' rs
End

Definition reply_bytes_def:
  reply_bytes as = bytes (FLAT (MAP print_response as))
End

(* ------------------------------------------------------------------------
   Orders of the requests of all connections
   ------------------------------------------------------------------------ *)

(* rss c: the complete requests read from connection c so far.  (c, i)
   names the i-th of them.  An order lists each exactly once, each
   connection's in their own order. *)
Definition is_order_def:
  is_order (rss : word64 -> brequest list) (order : (word64 # num) list) ⇔
    ∀c. MAP SND (FILTER (λx. FST x = c) order) = COUNT_LIST (LENGTH (rss c))
End

Definition earlier_def:
  earlier order x y ⇔ ∃l1 l2 l3. order = l1 ++ [x] ++ l2 ++ [y] ++ l3
End

(* The responses that running the requests in that order on the empty
   store gives to connection c's requests, in c's order *)
Definition replies_def:
  replies rss order c =
    MAP SND (FILTER (λ((d, i), a). d = c)
                    (ZIP (order, kv_run (λk. NONE)
                                   (MAP (λ(d, i). EL i (rss d)) order))))
End

(* Real time: at some point evs1 of the trace evs, the server had written
   the whole response to (c, i) and had read no byte of (d, j) *)
Definition precedes_def:
  precedes rss order evs (c, i) (d, j) ⇔
    ∃evs1. evs1 ≼ evs ∧
           reply_bytes (TAKE (SUC i) (replies rss order c)) ≼
             bytes_written_to c evs1 ∧
           bytes_read_from d evs1 ≼ brequests (TAKE j (rss d))
End

(* ------------------------------------------------------------------------
   The specification
   ------------------------------------------------------------------------ *)

(* Safety: at every point evs of the run, if what the server has read from
   each connection c is some complete requests rss c followed by a partial
   one, then some order of all of them respects real time, and on every
   connection the server has written a prefix of that order's replies. *)
Definition kv_safe_def:
  kv_safe io ⇔
    ∀evs rss rests.
      LPREFIX (fromList evs) io ∧
      (∀c. EVERY valid_brequest (rss c) ∧ no_full_brequest (rests c) ∧
           bytes_read_from c evs = brequests (rss c) ++ rests c) ⇒
      ∃order.
        is_order rss order ∧
        (∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
               precedes rss order evs x y ⇒ earlier order x y) ∧
        ∀c. bytes_written_to c evs ≼ reply_bytes (replies rss order c)
End

(* Liveness: if a client has sent the requests rs (within the first n steps
   of the schedule), the server eventually writes as many whole responses
   to it. *)
Definition kv_live_def:
  kv_live sk io ⇔
    ∀c n rs.
      EVERY valid_brequest rs ∧ brequests rs ≼ sent_upto c n sk ⇒
      ∃evs ans. LPREFIX (fromList evs) io ∧ LENGTH ans = LENGTH rs ∧
               reply_bytes ans ≼ bytes_written_to c evs
End

(* THE STATEMENT: in every fair world with one listener lfd, the program
   runs forever, and its I/O trace is linearizable and live. *)
Definition kv_spec_def:
  kv_spec lfd (prog : dec list) ⇔
    ∀sk. server_world lfd sk ⇒
         ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog
                (Diverge io) ∧
              kv_safe io ∧ kv_live sk io
End
