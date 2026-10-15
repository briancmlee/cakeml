(*
  EchoSpec2 bites: the statement rules out plausible bugs, and its
  assumptions are satisfiable with fds actually reused.  Everything here is
  proved.

  - Concrete events as the version-2 FFI functions produce them: EchoSpec's
    rd (data read) and wr (write), plus acc (an accept that returned an
    fd), rdeof (a read that returned EOF) and cls (a close).
  - Broken servers, per episode: swapping two clients' data, dropping or
    duplicating a byte, writing before reading, never echoing.
  - NEW, fd reuse: a server that writes data read on a previous connection
    to the new connection on the same fd violates echo_safe2.  EchoSpec's
    per-fd echo_safe does NOT catch this bug (v1_misses_leak), which is why
    EchoSpec2 projects per episode.
  - NEW, closing: a server that never closes (version 1's behaviour) is
    safe and live but violates echo_closes2 (broken_never_closes).
  - Non-vacuity: POSIX's lowest-free policy is an allocation policy
    (lowest_free_alloc_ok); a fair version-2 world with it in which the
    kernel really reuses an fd (hello_world2_reuses); and an ideal echo
    trace for it, with two episodes on the same fd, that is safe, live and
    closes (ideal2_trace_spec).
*)
Theory EchoSpec2Bite
Ancestors
  EchoSpec EchoSpecBite EchoSpec2 ffiSpikeSocketFFI socketV2FFI socketV2Fair
  llist Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   Concrete events
   ------------------------------------------------------------------------ *)

(* An accept on listener l that returned the connection fd f *)
Definition acc_def:
  acc l f =
    IO_event (ExtCall «sock_accept») (fd_bytes l)
      (ZIP (REPLICATE 9 0w, 1w :: fd_bytes f))
End

(* A read on c, with a buffer of n data bytes, that returned EOF *)
Definition rdeof_def:
  rdeof c n =
    IO_event (ExtCall «sock_read») (fd_bytes c)
      (ZIP (REPLICATE (n + 9) 0w, 2w :: REPLICATE (n + 8) 0w))
End

(* A close of c *)
Definition cls_def:
  cls c = IO_event (ExtCall «sock_close») (fd_bytes c) []
End

Overload L = “3w : word64”

(* ------------------------------------------------------------------------
   Broken servers violate safety, per episode
   ------------------------------------------------------------------------ *)

Theorem broken_swaps_clients2:
  starts_with [acc L c1; acc L c2; rd c1 A 100; rd c2 B 100; wr c1 B; wr c2 A] io ⇒
  ¬echo_safe2 io
Proof
  rw[echo_safe2_def] >>
  qexistsl [‘[acc L c1; acc L c2; rd c1 A 100; rd c2 B 100; wr c1 B; wr c2 A]’, ‘0’] >>
  simp[] >> EVAL_TAC
QED

Theorem broken_drops_a_byte2:
  starts_with [acc L c1; rd c1 (A ++ B ++ A) 100; wr c1 (A ++ A)] io ⇒
  ¬echo_safe2 io
Proof
  rw[echo_safe2_def] >>
  qexistsl [‘[acc L c1; rd c1 (A ++ B ++ A) 100; wr c1 (A ++ A)]’, ‘0’] >>
  simp[] >> EVAL_TAC
QED

Theorem broken_duplicates_a_byte2:
  starts_with [acc L c1; rd c1 (A ++ B) 100; wr c1 (A ++ A ++ B)] io ⇒
  ¬echo_safe2 io
Proof
  rw[echo_safe2_def] >>
  qexistsl [‘[acc L c1; rd c1 (A ++ B) 100; wr c1 (A ++ A ++ B)]’, ‘0’] >>
  simp[] >> EVAL_TAC
QED

Theorem broken_writes_before_reading2:
  starts_with [acc L c1; wr c1 A] io ⇒ ¬echo_safe2 io
Proof
  rw[echo_safe2_def] >> qexistsl [‘[acc L c1; wr c1 A]’, ‘0’] >>
  simp[] >> EVAL_TAC
QED

(* ------------------------------------------------------------------------
   fd reuse: a new connection never receives the previous one's data
   ------------------------------------------------------------------------ *)

(* Read "a" on fd c1, close c1, accept a new connection that reuses c1, and
   write "a" to it: the previous client's data reaches the new client *)
Overload leak = “[acc L c1; rd c1 A 100; cls c1; acc L c1; wr c1 A]”

(* NEW: such a server violates EchoSpec2's safety *)
Theorem broken_leaks_across_reuse:
  starts_with leak io ⇒ ¬echo_safe2 io
Proof
  rw[echo_safe2_def] >> qexistsl [‘leak’, ‘1’] >> simp[] >> EVAL_TAC
QED

Theorem LPREFIX_fromList_fromList[local]:
  LPREFIX (fromList xs) (fromList ys) ⇔ xs ≼ ys
Proof
  simp[LPREFIX_fromList, from_toList]
QED

Theorem prefix_take[local]:
  evs ≼ l ⇔ ∃n. n ≤ LENGTH l ∧ evs = TAKE n l
Proof
  eq_tac >> rw[]
  >- (qexists_tac ‘LENGTH evs’ >> gvs[IS_PREFIX_APPEND] >> simp[TAKE_APPEND1])
  >> simp[IS_PREFIX_APPEND] >> qexists_tac ‘DROP n l’ >> simp[]
QED

(* ... but EchoSpec's per-fd safety does not catch it: on fd c1, "a" was
   read and "a" was written *)
Theorem v1_misses_leak:
  echo_safe (fromList leak) ∧ ¬echo_safe2 (fromList leak)
Proof
  conj_tac
  >- (rw[echo_safe_def, LPREFIX_fromList_fromList, prefix_take] >>
      ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5’ by gvs[] >>
      gvs[] >> EVAL_TAC >> rw[] >> EVAL_TAC)
  >> irule broken_leaks_across_reuse >> simp[]
QED

(* ------------------------------------------------------------------------
   A fair world with reuse
   ------------------------------------------------------------------------ *)

(* A process using fds 0, 1, 2, listening on 3.  In the first round a client
   connects and sends "hi\n" then EOF; in the second round another client
   connects and sends "yo\n" then EOF; nothing arrives after that. *)
Overload HI = “[104w; 105w; 10w] : word8 list”
Overload YO = “[121w; 111w; 10w] : word8 list”

Definition hello_world2_def:
  hello_world2 =
    <| listening := [(3w, [])]; clients := []; open_fds := [];
       reserved := [0w; 1w; 2w]; alloc := (λj. lowest_free);
       future := [| [Connect2 3w; Data2 0 HI; Eof2 0];
                    [Connect2 3w; Data2 1 YO; Eof2 1] |] |>
End

Theorem ticks2_quiet[local]:
  ∀n s. s.future = [||] ⇒ ticks2 n s = s
Proof
  Induct >> rw[ticks2_def, tick2_def]
QED

(* NON-VACUITY: the assumption holds *)
Theorem hello_world2_sched_wf:
  sched_wf2 hello_world2
Proof
  rw[sched_wf2_def] >> Cases_on ‘n’ >- EVAL_TAC
  >> Cases_on ‘n'’ >- EVAL_TAC
  >> simp[ticks2_def]
  >> ‘(tick2 (tick2 hello_world2)).future = [||]’ by EVAL_TAC
  >> simp[ticks2_quiet, next_step2_def, step_ok2_def]
QED

(* Pigeonhole: fewer than N values cannot contain N distinct ones *)
Theorem pigeon[local]:
  ∀N (used : α list) f.
    (∀n m. n < N ∧ m < N ∧ f n = f m ⇒ n = m) ∧ LENGTH used < N ⇒
    ∃n. n < N ∧ ¬MEM (f n) used
Proof
  rw[] >> CCONTR_TAC >> gvs[] >>
  ‘set (GENLIST f N) ⊆ set used’ by (rw[SUBSET_DEF, MEM_GENLIST] >> metis_tac[]) >>
  ‘ALL_DISTINCT (GENLIST f N)’ by (simp[ALL_DISTINCT_GENLIST] >> metis_tac[]) >>
  ‘CARD (set (GENLIST f N)) = N’ by simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  ‘CARD (set (GENLIST f N)) ≤ CARD (set used)’ by (irule CARD_SUBSET >> simp[]) >>
  ‘CARD (set used) ≤ LENGTH used’ by simp[CARD_LIST_TO_SET] >>
  gvs[]
QED

(* With fewer than 2^64 fds in use, some fd is free *)
Theorem free_fd_exists[local]:
  LENGTH (used : word64 list) < dimword (:64) ⇒ ∃n. ¬MEM (n2w n : word64) used
Proof
  strip_tac >>
  qspecl_then [‘dimword (:64)’, ‘used’, ‘λn. n2w n’] mp_tac
    (INST_TYPE [alpha |-> “:word64”] pigeon) >>
  impl_tac >- (simp_tac std_ss [] >> rw[] >> gvs[n2w_11]) >>
  metis_tac[]
QED

(* NON-VACUITY: POSIX's policy, the lowest free fd, gives free fds *)
Theorem lowest_free_alloc_ok:
  alloc_ok (λj. lowest_free)
Proof
  rw[alloc_ok_def, lowest_free_def] >>
  ‘∃n. ¬MEM (n2w n : word64) used’ by (irule free_fd_exists >> simp[]) >>
  numLib.LEAST_ELIM_TAC >> metis_tac[]
QED

Theorem server_world2_exists:
  server_world2 3w hello_world2
Proof
  simp[server_world2_def, hello_world2_sched_wf] >> conj_tac >- EVAL_TAC >>
  simp[hello_world2_def, lowest_free_alloc_ok]
QED

Theorem lowest_free_eq[local]:
  ¬MEM (n2w n : word64) used ∧ (∀m. m < n ⇒ MEM (n2w m) used) ⇒
  lowest_free used = n2w n
Proof
  strip_tac >> REWRITE_TAC[lowest_free_def] >> AP_TERM_TAC >>
  numLib.LEAST_ELIM_TAC >> rw[]
  >- metis_tac[]
  >> CCONTR_TAC >> ‘n' < n ∨ n < n'’ by simp[] >> metis_tac[]
QED

(* NON-VACUITY: in this world the kernel really reuses an fd.  The server
   polls, accepts the first client (fd 4), closes it, polls again and
   accepts the second client: fd 4 again. *)
Theorem hello_world2_reuses:
  ∃s1 s2 s3 s4 s5.
    s1 = SND (sock_poll2 [3w] hello_world2) ∧
    sock_accept2 3w s1 = SOME (SOME 4w, s2) ∧
    sock_close2 4w s2 = SOME s3 ∧
    s4 = SND (sock_poll2 [3w] s3) ∧
    sock_accept2 3w s4 = SOME (SOME 4w, s5)
Proof
  ‘lowest_free [0w; 1w; 2w; 3w] = 4w’
    by (irule lowest_free_eq >> simp[] >> rw[] >>
        ‘m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3’ by simp[] >> simp[])
  (* evaluate the world, keeping lowest_free folded *)
  >> computeLib.RESTR_EVAL_TAC [“lowest_free”] >> simp[]
  >> computeLib.RESTR_EVAL_TAC [“lowest_free”] >> simp[]
QED

(* ------------------------------------------------------------------------
   Never echoing violates liveness
   ------------------------------------------------------------------------ *)

Theorem arrivals2_upto_nil[local]:
  arrivals2_upto n [||] = []
Proof
  Cases_on ‘n’ >> simp[arrivals2_upto_def]
QED

Theorem sent2_upto_hello_world2[local]:
  sent2_upto j n hello_world2 =
    if j = 0 ∧ 1 ≤ n then HI else if j = 1 ∧ 2 ≤ n then YO else []
Proof
  Cases_on ‘n’ >> simp[sent2_upto_def, arrivals2_upto_def, hello_world2_def]
  >> Cases_on ‘n'’ >> simp[arrivals2_upto_def, arrivals2_upto_nil] >> rw[]
QED

Theorem broken_never_echoes2:
  (∀evs. starts_with evs io ⇒ ep_written 0 evs = []) ⇒
  ¬echo_live2 hello_world2 io
Proof
  rw[echo_live2_def] >> qexistsl [‘0’, ‘1’] >> rw[sent2_upto_hello_world2] >>
  Cases_on ‘LPREFIX (fromList evs) io’ >> simp[] >> res_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   An ideal trace, with two episodes on the same fd
   ------------------------------------------------------------------------ *)

(* Accept client 0 on fd 4, echo "hi\n", read EOF, close fd 4; accept
   client 1, again on fd 4, echo "yo\n", read EOF, close *)
Overload ideal2_evs =
  “[acc L 4w; rd 4w HI 100; wr 4w HI; rdeof 4w 100; cls 4w;
    acc L 4w; rd 4w YO 100; wr 4w YO; rdeof 4w 100; cls 4w]”

(* The safety and liveness predicates are jointly satisfiable, with reuse *)
Theorem ideal2_trace_safe_and_live:
  echo_safe2 (fromList ideal2_evs) ∧ echo_live2 hello_world2 (fromList ideal2_evs)
Proof
  conj_tac
  >- (rw[echo_safe2_def, LPREFIX_fromList_fromList, prefix_take] >>
      ‘n ≤ 10’ by gvs[] >>
      ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
       n = 8 ∨ n = 9 ∨ n = 10’ by simp[] >>
      ‘j = 0 ∨ j = 1 ∨ 2 ≤ j’ by simp[] >> gvs[] >> EVAL_TAC >> simp[])
  >> rw[echo_live2_def] >> qexists_tac ‘ideal2_evs’ >>
  simp[LPREFIX_fromList_fromList, sent2_upto_hello_world2] >> rw[] >> EVAL_TAC
QED

(* ... and it closes both episodes *)
Theorem ideal2_trace_closes:
  echo_closes2 (fromList ideal2_evs)
Proof
  rw[echo_closes2_def, LPREFIX_fromList_fromList] >>
  qexists_tac ‘ideal2_evs’ >> simp[] >>
  ‘j < LENGTH (accepted_fds evs)’ by gvs[ep_eof_read_def] >>
  ‘accepted_fds evs ≼ accepted_fds ideal2_evs’
    by (qpat_x_assum ‘evs ≼ _’ (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
        ASM_REWRITE_TAC [accepted_fds_def, MAP_APPEND, FLAT_APPEND] >>
        REWRITE_TAC [IS_PREFIX_APPEND] >> metis_tac[]) >>
  ‘LENGTH (accepted_fds ideal2_evs) = 2’ by EVAL_TAC >>
  imp_res_tac IS_PREFIX_LENGTH >>
  ‘j = 0 ∨ j = 1’ by simp[] >> gvs[] >> EVAL_TAC
QED

(* NON-VACUITY: the three clauses are jointly satisfiable, with reuse *)
Theorem ideal2_trace_spec:
  echo_safe2 (fromList ideal2_evs) ∧ echo_live2 hello_world2 (fromList ideal2_evs) ∧
  echo_closes2 (fromList ideal2_evs)
Proof
  simp[ideal2_trace_safe_and_live, ideal2_trace_closes]
QED

(* ------------------------------------------------------------------------
   A server that never closes
   ------------------------------------------------------------------------ *)

(* Version 1's behaviour: echo each client, read its EOF, never close; the
   second client gets a fresh fd (5), as fd 4 is still in use *)
Overload noclose_evs =
  “[acc L 4w; rd 4w HI 100; wr 4w HI; rdeof 4w 100;
    acc L 5w; rd 5w YO 100; wr 5w YO; rdeof 5w 100]”

(* NEW: it is safe and live, but violates echo_closes2 *)
Theorem broken_never_closes:
  echo_safe2 (fromList noclose_evs) ∧ echo_live2 hello_world2 (fromList noclose_evs) ∧
  ¬echo_closes2 (fromList noclose_evs)
Proof
  rpt conj_tac
  >- (rw[echo_safe2_def, LPREFIX_fromList_fromList, prefix_take] >>
      ‘n ≤ 8’ by gvs[] >>
      ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
       n = 8’ by simp[] >>
      ‘j = 0 ∨ j = 1 ∨ 2 ≤ j’ by simp[] >> gvs[] >> EVAL_TAC >> simp[])
  >- (rw[echo_live2_def] >> qexists_tac ‘noclose_evs’ >>
      simp[LPREFIX_fromList_fromList, sent2_upto_hello_world2] >> rw[] >> EVAL_TAC)
  >> rw[echo_closes2_def, LPREFIX_fromList_fromList] >>
  qexistsl [‘noclose_evs’, ‘0’] >> simp[] >> conj_tac >- EVAL_TAC >>
  rw[] >> Cases_on ‘evs' ≼ noclose_evs’ >> simp[] >> gvs[prefix_take] >>
  ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
   n = 8’ by simp[] >> gvs[] >> EVAL_TAC
QED
