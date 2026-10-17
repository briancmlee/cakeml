(*
  The prefetching L1 (honestL1PFModel) in CakeML: the pure parts, translated.

  L1's state is the model's own (l1p, with honestL1Model's l1st inside),
  registered with the translator, so the bookkeeping the model does
  between calls (buffers, tables, the poll set, the ready set, decoding
  the C's results) is the model's definitions themselves, translated.  The
  code that makes the L0 calls (honestL0Prog's L0 module) mirrors the
  model's world functions one by one (honestL1PFCode), and its CF specs
  are against them (honestL1PFSpec).

  Appended to honestL0Proof's translation state (the servers' chain, then
  the L0 wrappers).
*)
Theory honestL1PFProg
Ancestors
  ml_translator honestL0 honestL0World honestL1Model honestL1PFModel honestL0Proof
  ffiSpikeSocketFFI Marshalling
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "honestL0Proof";

(* ------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------ *)

val _ = register_type “:errcode”;
val _ = register_type “:l0_res”;
val _ = register_type “:revents”;
val _ = register_type “:l1st”;
val _ = register_type “:l1p”;
val _ = register_type “:fetched”;

(* ------------------------------------------------------------------------
   Bytes and strings at the L0 boundary
   ------------------------------------------------------------------------ *)

(* The configuration string of a call, and the bytes of a result *)
Definition bytes_to_str_def:
  bytes_to_str (bs : word8 list) = implode (MAP (λw. CHR (w2n w)) bs)
End

Definition str_to_bytes_def:
  str_to_bytes s = MAP (λc. n2w (ORD c)) (explode s) : word8 list
End

Theorem str_to_bytes_bytes_to_str:
  str_to_bytes (bytes_to_str bs) = bs
Proof
  simp[str_to_bytes_def, bytes_to_str_def, MAP_MAP_o, combinTheory.o_DEF,
       ORD_CHR_RWT, w2n_lt_256 |> SIMP_RULE (srw_ss()) [],
       wordsTheory.w2n_lt |> INST_TYPE [alpha |-> “:8”] |> SIMP_RULE (srw_ss()) []] >>
  Induct_on ‘bs’ >> simp[] >> rpt strip_tac >>
  ‘w2n h < 256’ by (assume_tac (INST_TYPE [alpha |-> “:8”] wordsTheory.w2n_lt) >> fs[]) >>
  simp[ORD_CHR_RWT]
QED

(* Membership, translatable (the translator reads MEM as a set) *)
Definition lmem_def:
  lmem x [] = F ∧
  lmem x (y :: ys) = (x = y ∨ lmem x ys)
End

Theorem lmem_MEM:
  ∀l. lmem x l ⇔ MEM x l
Proof
  Induct >> simp[lmem_def]
QED

val r = translate lmem_def;

(* Translate with TAKE / DROP as the basis's mllist take / drop and MEM as
   lmem *)
fun tr th = translate (th |> REWRITE_RULE [GSYM mllistTheory.take_def,
                                          GSYM mllistTheory.drop_def,
                                          GSYM lmem_MEM]);

(* ------------------------------------------------------------------------
   Decoding results (honestL0's dec_res, l0_res_of)
   ------------------------------------------------------------------------ *)

val r = tr err_code_def;
val r = tr code_err_def;
val r = tr w82n_def;
val r = tr n2w8_def;
val r = tr fd_bytes_def;
val r = tr dec_res_def;

Theorem w82n_side_8[local]:
  LENGTH l = 8 ⇒ w82n_side l
Proof
  rw[listTheory.LENGTH_EQ_NUM_compute] >> simp[fetch "-" "w82n_side_def"]
QED

(* The decoder is total: it reads the 8 value bytes only of a full header *)
Theorem dec_res_side[local]:
  dec_res_side v
Proof
  rw[fetch "-" "dec_res_side_def", mllistTheory.take_def] >>
  TRY (Cases_on ‘v’ >> fs[] >> NO_TAC) >>
  irule w82n_side_8 >> Cases_on ‘v’ >> fs[listTheory.LENGTH_TAKE]
QED

val _ = update_precondition dec_res_side;
val r = tr l0_res_of_def;

(* byte_revents, with word_bit as arithmetic *)
Theorem byte_revents_arith:
  byte_revents b =
    <| rin := ODD (w2n b); rout := ODD (w2n b DIV 2); rerr := ODD (w2n b DIV 4);
       rhup := ODD (w2n b DIV 8); rnval := ODD (w2n b DIV 16) |>
Proof
  simp[byte_revents_def, revents_component_equality] >>
  Cases_on ‘b’ >> fs[wordsTheory.word_bit_n2w, bitTheory.BIT_def, bitTheory.BITS_THM,
                     bitTheory.ODD_MOD2_LEM]
QED

val r = tr byte_revents_arith;

(* D20: the entries of a poll's result, and their revents fields *)
val r = tr pollfd_entries_def;

Theorem pollfd_entries_ind_holds[local]:
  pollfd_entries_ind
Proof
  rw[fetch "-" "pollfd_entries_ind_def"] >>
  completeInduct_on ‘LENGTH v1’ >> rw[] >>
  last_x_assum irule >> rw[mllistTheory.drop_def] >>
  first_x_assum (qspec_then ‘LENGTH (DROP 8 v1)’ mp_tac) >> simp[]
QED

val _ = update_precondition pollfd_entries_ind_holds;

Theorem abi_revents_arith:
  abi_revents bs =
    <| rin := ODD (w2n (HD bs)); rout := ODD (w2n (HD bs) DIV 4);
       rerr := ODD (w2n (HD bs) DIV 8); rhup := ODD (w2n (HD bs) DIV 16);
       rnval := ODD (w2n (HD bs) DIV 32) |>
Proof
  simp[abi_revents_def, revents_component_equality] >>
  Cases_on ‘HD bs’ >> fs[wordsTheory.word_bit_n2w, bitTheory.BIT_def, bitTheory.BITS_THM,
                         bitTheory.ODD_MOD2_LEM]
QED

val r = tr abi_revents_arith;

Theorem pollfd_entries_len[local]:
  ∀bs e. MEM e (pollfd_entries bs) ⇒ LENGTH e = 8
Proof
  recInduct pollfd_entries_ind >> rw[] >>
  pop_assum mp_tac >> simp[Once pollfd_entries_def] >> rw[] >> gvs[]
QED

val r = tr poll_revents_def;

val _ = print_thm (fetch "-" "poll_revents_side_def");
val _ = print "\n";
val _ = print_thm (fetch "-" "abi_revents_side_def");
val _ = print "\n";

Theorem poll_revents_side[local]:
  poll_revents_side fes out
Proof
  rw[fetch "-" "poll_revents_side_def", fetch "-" "abi_revents_side_def"] >>
  gvs[mllistTheory.drop_def] >> imp_res_tac pollfd_entries_len >> gvs[DROP_EQ_NIL]
QED

val _ = update_precondition poll_revents_side;
val r = tr readable_fds_def;
val r = tr writable_fds_def;
(* D20: the poll's buffer, with the words as arithmetic *)
Theorem pfd_bytes_arith:
  pfd_bytes (f, e) =
    [n2w (w2n f); n2w (w2n f DIV 256); n2w (w2n f DIV 65536); n2w (w2n f DIV 16777216);
     n2w ((if e MOD 2 = 1 then 1 else 0) + (if 2 ≤ e then 4 else 0)); 0w; 0w; 0w]
Proof
  simp[pfd_bytes_def, wordsTheory.w2w_def, wordsTheory.w2n_lsr, bitTheory.ODD_MOD2_LEM]
QED

val r = tr pfd_bytes_arith;
Theorem poll_buf_lit:
  poll_buf fes = [0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w;0w] ++ FLAT (MAP pfd_bytes fes)
Proof
  simp[poll_buf_def] >> EVAL_TAC
QED

val r = tr poll_buf_lit;

(* ------------------------------------------------------------------------
   L1's bookkeeping
   ------------------------------------------------------------------------ *)

val r = tr alistTheory.ADELKEY_def;
val r = tr l1hdln_def;
val r = tr l1hdl_def;
val r = tr outbox_of_def;
val r = tr set_outbox_def;
val r = tr l1_transient_def;
val r = tr forget_def;
val r = tr after_send_def;
val r = tr inb_of_def;
val r = tr set_inb_def;
val r = tr pf_chunk_def;
val r = tr pf_backoff_def;
(* The servers' pause policy, pol_self hw (moonshot step 5), as the loop
   computes it: by the high-water mark *)
Definition wants_input_hw_def:
  wants_input_hw lfd hw ps f ⇔
    if f = lfd then ps.acq = [] ∧ ps.pause = 0
    else inb_of ps f = [] ∧ ¬MEM f ps.eof ∧ LENGTH (outbox_of ps.b f) ≤ hw
End

Theorem wants_input_hw:
  wants_input_hw lfd hw ps f ⇔ wants_input lfd (pol_self hw) ps f
Proof
  rw[wants_input_hw_def, wants_input_def, pol_self_def, NOT_LESS]
QED

Definition pf_poll_set_hw_def:
  pf_poll_set_hw lfd hw ps (hs : word64 list) =
    let ins = FLAT (MAP (λh. case ALOOKUP ps.b.tbl h of
                             | SOME f =>
                                 let i = (if wants_input_hw lfd hw ps f then 1n else 0);
                                     ou = (if outbox_of ps.b f = [] then 0 else 2n) in
                                   if i + ou = 0 then [] else [(f, i + ou)]
                             | NONE => if h = lfd ∧ wants_input_hw lfd hw ps lfd
                                       then [(lfd, 1n)] else []) hs) in
      ins ++ MAP (λ(f, bs). (f, 2n))
               (FILTER (λ(f, bs). bs ≠ [] ∧ ¬MEM f (MAP FST ins)) ps.b.outbox)
End

Theorem pf_poll_set_hw:
  pf_poll_set_hw lfd hw ps hs = pf_poll_set lfd (pol_self hw) ps hs
Proof
  simp[pf_poll_set_hw_def, pf_poll_set_def, wants_input_hw]
QED

val r = tr wants_input_hw_def;
val r = tr pf_poll_set_hw_def;
val r = tr in_fds_def;
val r = tr pf_ready_def;

(* ------------------------------------------------------------------------
   The model's world functions, split at their L0 calls

   Each world function of honestL1PFModel is a pure decision (which call,
   if any) and a pure update from the call's result; the CakeML code makes
   the call in between (honestL1PFCode).  The lemmas pdo_split etc. show
   the split is the model.
   ------------------------------------------------------------------------ *)

(* Accept: the oldest queued fd under the next handle *)
Definition pacc_def:
  pacc lfd ps =
    case ps.acq of
    | [] => NONE
    | f :: q =>
        SOME (l1hdl lfd ps.b.nxt,
              ps with <| b := ps.b with <| tbl := (l1hdl lfd ps.b.nxt, f) :: ps.b.tbl;
                                           nxt := ps.b.nxt + 1 |>;
                         acq := q |>)
End

(* Read: an answer, or an auto-close of f first *)
Datatype:
  rstep = RkGot (word8 list option) l1p | RkClose word64 l1p
End

Definition pread_step_def:
  pread_step ps h n =
    case ALOOKUP ps.b.tbl h of
    | NONE => RkGot (SOME []) ps
    | SOME f =>
        if inb_of ps f ≠ [] then
          RkGot (SOME (TAKE n (inb_of ps f))) (set_inb f (DROP n (inb_of ps f)) ps)
        else if MEM f ps.eof then
          let ps0 = ps with <| b := ps.b with tbl := ADELKEY h ps.b.tbl;
                               eof := FILTER ($≠ f) ps.eof |> in
            if outbox_of ps.b f = [] ∨ MEM f ps.b.gone then RkClose f ps0
            else RkGot (SOME []) (ps0 with b := ps0.b with closing := f :: ps0.b.closing)
        else RkGot NONE ps
End

Definition pclose_upd_def:
  pclose_upd f ps0 = ps0 with b := forget f ps0.b
End

(* Write: done, or one send of bs on f *)
Datatype:
  wstep = WkDone l1p | WkSend word64
End

Definition pwrite_step_def:
  pwrite_step ps h bs =
    case ALOOKUP ps.b.tbl h of
    | NONE => WkDone ps
    | SOME f =>
        if MEM f ps.b.gone then WkDone ps
        else if outbox_of ps.b f ≠ [] then
          WkDone (ps with b := set_outbox f (outbox_of ps.b f ++ bs) ps.b)
        else WkSend f
End

Definition psend_upd_def:
  psend_upd f bs out ps =
    ps with b := after_send f (l0_res_of out) (set_outbox f bs ps.b)
End

(* The fetch's updates *)
Definition fetch_acc_upd_def:
  fetch_acc_upd ps out =
    case l0_res_of out of
    | Ok k => ps with acq := ps.acq ++ [n2w k]
    | Fail e _ => if e = E_MFILE then ps with pause := pf_backoff else ps
End

Definition fetch_recv_upd_def:
  fetch_recv_upd f ps out =
    case l0_res_of out of
    | Ok k => if 0 < k then set_inb f (TAKE k (DROP 13 out)) ps
              else ps with eof := f :: ps.eof
    | Fail e _ => if l1_transient e then ps else ps with eof := f :: ps.eof
End

(* The fetch log entry of an accept, of a recv on f (as pf_fetch's) *)
Definition fetch_acc_log_def:
  fetch_acc_log out =
    case l0_res_of out of
    | Ok k => [FConn (n2w k)]
    | Fail e _ => []
End

Definition fetch_recv_log_def:
  fetch_recv_log f out =
    case l0_res_of out of
    | Ok k => if 0 < k then [FData f (TAKE k (DROP 13 out))] else [FEof f]
    | Fail e _ => if l1_transient e then [] else [FReset f]
End

(* D19's hung-up step, with the outboxes of the state before the flush *)
Definition stall_step_ob_def:
  stall_step_ob hfs b0 log ps = stall_step hfs (outbox_of b0) log ps
End

(* An fd the flush skips, and the reap closes *)
Definition quiet_fd_def:
  quiet_fd st f ⇔ outbox_of st f = [] ∨ MEM f st.gone
End

Definition l1p_b_def:
  l1p_b ps = ps.b
End

Definition set_b_def:
  set_b ps b = ps with b := b
End

(* Room for n more handles, with one to spare (a pending accepted
   connection): a round with at most n accepts cannot overflow the handle
   counter.  Without room the loop stops (spins without I/O):
   after 2^64 accepted connections, unreachable in practice; a deliberate
   choice over wrapping the counter (which would reuse handles) *)
Definition hdl_room_def:
  hdl_room (lfd:word64) ps n ⇔ l1hdln (w2n lfd) (ps.b.nxt + n + 1) < dimword (:64)
End

Theorem hdl_room_num:
  hdl_room (lfd:word64) ps n ⇔ l1hdln (w2n lfd) (ps.b.nxt + n + 1) < 18446744073709551616
Proof
  simp[hdl_room_def]
QED

(* The round's end: the reaped state, and one round of the listener's pause *)
Definition end_round_def:
  end_round ps b = ps with <| b := b; pause := ps.pause − 1 |>
End

Definition closing_of_def:
  closing_of ps = ps.b.closing
End

Definition filter_in_def:
  filter_in ins fs = FILTER (λf:word64. MEM f ins) fs
End

Definition map_w64_def:
  map_w64 (l : num list) = MAP (λn. n2w n) l : word64 list
End

Definition map_num_def:
  map_num (l : word64 list) = MAP (λw. w2n w) l
End

val _ = register_type “:rstep”;
val _ = register_type “:wstep”;

val r = tr bytes_to_str_def;

Theorem bytes_to_str_side[local]:
  bytes_to_str_side bs
Proof
  simp[fetch "-" "bytes_to_str_side_def", EVERY_MEM] >> rpt strip_tac >>
  assume_tac (INST_TYPE [alpha |-> “:8”] wordsTheory.w2n_lt) >> fs[]
QED

val _ = update_precondition bytes_to_str_side;
val r = tr str_to_bytes_def;
val r = tr pacc_def;
val r = tr pread_step_def;
val r = tr pclose_upd_def;
val r = tr pwrite_step_def;
val r = tr psend_upd_def;
val r = tr fetch_acc_upd_def;
val r = tr fetch_recv_upd_def;
val r = tr fetch_acc_log_def;
val r = tr fetch_recv_log_def;
val r = tr pf_sendwait_def;
val r = tr pf_held_def;
val r = tr drop_out_def;
val r = tr listTheory.nub_def;
val r = tr listTheory.FOLDL;
val r = tr stall_step_def;
val r = tr stall_step_ob_def;
val r = tr quiet_fd_def;
val r = tr l1p_b_def;
val r = tr set_b_def;
(* As the model's, with the subtraction guarded (the translator's num
   subtraction needs 1 ≤ pause) *)
Theorem end_round_guarded:
  end_round ps b =
    ps with <| b := b; pause := if ps.pause = 0 then 0 else ps.pause − 1 |>
Proof
  rw[end_round_def]
QED

val r = tr end_round_guarded;
val r = tr hdl_room_num;
val r = tr closing_of_def;
val r = tr filter_in_def;
val r = tr map_w64_def;
val r = tr map_num_def;

(* ------------------------------------------------------------------------
   The code: the calls, and the model's world functions around them
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun c_accept l = str_to_bytes (L0.accept (bytes_to_str (fd_bytes l)) 13);
  fun c_recv f n = str_to_bytes (L0.recv (bytes_to_str (fd_bytes f)) (13 + n));
  fun c_send f bs = str_to_bytes (L0.send (bytes_to_str (fd_bytes f @ bs)) 13);
  fun c_close f = str_to_bytes (L0.close (bytes_to_str (fd_bytes f)) 13);
  fun c_poll fes =
    str_to_bytes (L0.poll (bytes_to_str [Word8.fromInt 0]) (bytes_to_str (poll_buf fes)));

  fun pdo lfd ps a =
    case a of
      Accept l =>
        (case pacc lfd ps of
           None => (ps, Accepted None)
         | Some p => (case p of (h, ps1) => (ps1, Accepted (Some (Word64.toInt h)))))
    | Read h n =>
        (case pread_step ps (Word64.fromInt h) n of
           Rkgot r ps1 =>
             (ps1, Got (case r of None => None | Some bs => Some (bytes_to_str bs)))
         | Rkclose f ps0 =>
             let val out = c_close f in (pclose_upd f ps0, Got (Some "")) end)
    | Write h s =>
        let val bs = str_to_bytes s in
          case pwrite_step ps (Word64.fromInt h) bs of
            Wkdone ps1 => (ps1, Wrote)
          | Wksend f =>
              let val out = c_send f bs in (psend_upd f bs out ps, Wrote) end
        end;

  fun pacts lfd ps acts =
    case acts of
      [] => (ps, [])
    | a :: rest =>
        (case pdo lfd ps a of
           (ps1, r) => (case pacts lfd ps1 rest of (ps2, rs) => (ps2, r :: rs)));

  fun l1_polls chunks =
    case chunks of
      [] => []
    | fes :: rest =>
        let val out = c_poll fes
            val rv = l1_polls rest
        in poll_revents fes out @ rv end;

  fun l1_flush fs st =
    case fs of
      [] => st
    | f :: rest =>
        if quiet_fd st f then l1_flush rest st
        else
          let val out = c_send f (outbox_of st f) in
            l1_flush rest (after_send f (l0_res_of out) st)
          end;

  fun pf_fetch lfd hw fs ps =
    case fs of
      [] => (ps, [])
    | f :: rest =>
        if not (wants_input_hw lfd hw ps f) then pf_fetch lfd hw rest ps
        else if f = lfd then
          let val out = c_accept lfd in
            case pf_fetch lfd hw rest (fetch_acc_upd ps out) of
              (ps2, log) => (ps2, fetch_acc_log out @ log)
          end
        else
          let val out = c_recv f pf_chunk in
            case pf_fetch lfd hw rest (fetch_recv_upd f ps out) of
              (ps2, log) => (ps2, fetch_recv_log f out @ log)
          end;

  fun l1_reap fs st =
    case fs of
      [] => st
    | f :: rest =>
        if quiet_fd st f then
          let val out = c_close f in l1_reap rest (forget f st) end
        else l1_reap rest st;

  fun pf_tail lfd hw hs ps =
    let
      val fes = pf_poll_set_hw lfd hw ps hs
      val rv = l1_polls [fes]
      val b2 = l1_flush (writable_fds rv) (l1p_b ps)
      val fl = pf_fetch lfd hw (filter_in (in_fds fes) (readable_fds rv)) (set_b ps b2)
    in
      case fl of (ps3a, log) =>
      let
        val ps3 = stall_step_ob (pf_held ps3a) (l1p_b ps) log ps3a
        val b4 = l1_reap (closing_of ps3) (l1p_b ps3)
        val ps4 = end_round ps3 b4
      in (pf_ready lfd ps4 hs, ps4) end
    end;

  fun step_pf st =
    case st of (lfd, hw, fds, ps, c) =>
    case c of (acts, s) =>
    if not (hdl_room lfd ps (List.length acts)) then st else
    case pacts lfd ps acts of (ps1, rs) =>
    case pf_tail lfd hw (map_w64 fds) ps1 of (rdy, ps2) =>
      (lfd, hw, add_accepted fds rs, ps2, Async.poll c (map_num rdy, 0, rs));

  fun run_pf st = run_pf (step_pf st);
End
