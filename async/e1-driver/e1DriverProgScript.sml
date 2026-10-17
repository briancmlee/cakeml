(*
  E1's L1 (honestL1EPModel) in CakeML, and the generic E1 driver loop.

  As in honestL1PFProg, the bookkeeping between calls is the model's own
  definitions, translated; the code makes the L0 calls in between, and
  its CF specs (e1DriverSpec) are against the model's world functions.
  The PF code (pacc, pread_step, pwrite_step, l1_polls, l1_flush,
  l1_reap, stall_step) is reused; the fetch is re-done for a general
  pause policy pol (the PF code has pol_self hw built in).

  The loop runs a fold program (e1Fold): it keeps the program's state
  and calls the program's (translated) acts, ifds, step and fin, passed
  as values.
*)
Theory e1DriverProg
Ancestors
  ml_translator endpointHLModel honestL0 honestL0World honestL1Model honestL1PFModel
  honestL1EPModel honestL1PFProg e1TypesProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "e1TypesProg";

(* TAKE / DROP as mllist's take / drop, MEM as honestL1PFProg's lmem *)
fun tr th = translate (th |> REWRITE_RULE [GSYM mllistTheory.take_def,
                                           GSYM mllistTheory.drop_def,
                                           GSYM lmem_MEM]);

(* ------------------------------------------------------------------------
   The pause policy, general
   ------------------------------------------------------------------------ *)

val r = tr wants_input_def;
val r = tr pf_poll_set_def;

(* ------------------------------------------------------------------------
   E1's world functions, split at their L0 calls
   ------------------------------------------------------------------------ *)

Definition e_p_def:
  e_p (es : l1e) = es.p
End

Definition set_p_def:
  set_p (es : l1e) ps = es with p := ps
End

Definition ec_lookup_def:
  ec_lookup (es : l1e) h = ALOOKUP es.ctbl h
End

Definition ec_refused_def:
  ec_refused es f ⇔ cstat_of es f = CRefused
End

(* A refused connect handle, read: its socket closed, the handle forgotten *)
Definition ec_close_upd_def:
  ec_close_upd h f es = ec_del h f (es with p := es.p with b := forget f es.p.b)
End

(* A connect's status from sys_connect's answer *)
Definition conn_stat_def:
  conn_stat out =
    case l0_res_of out of
    | Ok _ => CUp
    | Fail e _ => if e = E_INPROGRESS then CPending else CRefused
End

(* EConnect's update from sys_connect's answer (edo's EConnect, a < 2^16);
   the case without a handle left (NONE in the model) keeps the state *)
Definition conn_upd_def:
  conn_upd lfd out (es : l1e) =
    if res_val out = 0 then (es, EConnected NONE)
    else if l1hdln (w2n lfd) es.p.b.nxt < 18446744073709551616 then
      (es with <| p := es.p with b := es.p.b with nxt := es.p.b.nxt + 1;
                  ctbl := (l1hdl lfd es.p.b.nxt, n2w (res_val out)) :: es.ctbl;
                  cst := (n2w (res_val out), CPending) :: ADELKEY (n2w (res_val out)) es.cst;
                  settling := l1hdl lfd es.p.b.nxt :: es.settling;
                  early := if conn_stat out = CPending then es.early
                           else (n2w (res_val out), conn_stat out) :: es.early |>,
       EConnected (SOME (l1hdl lfd es.p.b.nxt)))
    else (es, EConnected NONE)
End

(* EWrite's answer on a PF handle (from the state before the write) *)
Definition ewrite_resp_def:
  ewrite_resp (es : l1e) h (bs : word8 list) =
    EWrote (if ALOOKUP es.p.b.tbl h = NONE then 0 else LENGTH bs)
End

(* sys_connerr's answer on a pending fd f (settle_fds's update) *)
Definition settle_upd_def:
  settle_upd f out (es : l1e) =
    case l0_res_of out of
    | Ok _ => es with cst := (f, CUp) :: ADELKEY f es.cst
    | Fail e _ => if res_val out = 1
                  then es with cst := (f, CRefused) :: ADELKEY f es.cst
                  else es
End

(* The tail's poll set: the PF set, and each pending connect for OUT *)
Definition etail_fes_def:
  etail_fes lfd pol es hs =
    pf_poll_set lfd pol es.p hs ++ MAP (λf. (f, 2n)) (pend_fds es)
End

(* The pending connects the poll found ready *)
Definition ready_pend_def:
  ready_pend es rv =
    FILTER (λf. MEM f (pend_fds es) ∧ (MEM f (writable_fds rv) ∨ MEM f (readable_fds rv)))
           (pend_fds es)
End

(* The tail after the reap: the PF state's round end, the early outcomes *)
Definition es_end_def:
  es_end (es : l1e) ps3 b4 = apply_early (es with p := end_round ps3 b4)
End

(* The tail's end: promotion, the snapshot's ready handles, settling *)
Definition etail_fin_def:
  etail_fin lfd hs es5 =
    let es6 = promote es5;
        settled = (λh. MEM h es6.settling ∧
                       (case ALOOKUP es6.ctbl h of
                        | SOME f => cstat_of es6 f ≠ CPending
                        | NONE => ALOOKUP es6.p.b.tbl h ≠ NONE));
        rdy = FILTER (λh. case ALOOKUP es6.ctbl h of
                          | SOME f => cstat_of es6 f = CRefused ∨ settled h
                          | NONE => MEM h (pf_ready lfd es6.p [h]) ∨ settled h) hs
    in (rdy, es6 with settling := FILTER (λh. ¬(MEM h hs ∧ settled h)) es6.settling)
End

val r = tr e_p_def;
val r = tr set_p_def;
val r = tr ec_lookup_def;
val r = tr cstat_of_def;
val r = tr ec_refused_def;
val r = tr ec_del_def;
val r = tr ec_close_upd_def;
val r = tr res_val_def;
val r = tr port_bytes_def;
val r = tr conn_stat_def;
val r = tr conn_upd_def;
val r = tr ewrite_resp_def;
val r = tr elevel_def;
val r = tr settle_upd_def;
val r = tr pend_fds_def;
val r = tr etail_fes_def;
val r = tr ready_pend_def;
val r = tr apply_early_def;
val r = tr es_end_def;
val r = tr promote_def;
val r = tr etail_fin_def;

(* ------------------------------------------------------------------------
   The code: the calls, and E1's world functions around them
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun c_connect a = str_to_bytes (L0.connect (bytes_to_str (port_bytes a)) 13);
  fun c_connerr f = str_to_bytes (L0.connerr (bytes_to_str (fd_bytes f)) 13);

  fun edo lfd es a =
    case a of
      Eaccept l =>
        (case pacc lfd (e_p es) of
           None => (es, Eaccepted None)
         | Some p => (case p of (h, ps1) => (set_p es ps1, Eaccepted (Some h))))
    | Econnect a =>
        if 65536 <= a then (es, Econnected None)
        else let val out = c_connect a in conn_upd lfd out es end
    | Eread h n =>
        (case ec_lookup es h of
           Some f =>
             if ec_refused es f then
               let val out = c_close f in (ec_close_upd h f es, Erefused) end
             else (es, Egot None)
         | None =>
             (case pread_step (e_p es) h n of
                Rkgot r ps1 => (set_p es ps1, Egot r)
              | Rkclose f ps0 =>
                  let val out = c_close f in (set_p es (pclose_upd f ps0), Egot (Some [])) end))
    | Ewrite h bs =>
        (case ec_lookup es h of
           Some f => (es, Ewrote 0)
         | None =>
             (case pwrite_step (e_p es) h bs of
                Wkdone ps1 => (set_p es ps1, ewrite_resp es h bs)
              | Wksend f =>
                  let val out = c_send f bs in
                    (set_p es (psend_upd f bs out (e_p es)), ewrite_resp es h bs)
                  end))
    | Elevel h => (es, Elvl (elevel es h));

  fun eacts lfd es acts =
    case acts of
      [] => (es, [])
    | a :: rest =>
        (case edo lfd es a of
           (es1, r) => (case eacts lfd es1 rest of (es2, rs) => (es2, r :: rs)));

  fun pf_fetch_p lfd pol fs ps =
    case fs of
      [] => (ps, [])
    | f :: rest =>
        if not (wants_input lfd pol ps f) then pf_fetch_p lfd pol rest ps
        else if f = lfd then
          let val out = c_accept lfd in
            case pf_fetch_p lfd pol rest (fetch_acc_upd ps out) of
              (ps2, log) => (ps2, fetch_acc_log out @ log)
          end
        else
          let val out = c_recv f pf_chunk in
            case pf_fetch_p lfd pol rest (fetch_recv_upd f ps out) of
              (ps2, log) => (ps2, fetch_recv_log f out @ log)
          end;

  fun settle_fds_c fs es =
    case fs of
      [] => es
    | f :: rest => let val out = c_connerr f in settle_fds_c rest (settle_upd f out es) end;

  fun etail lfd pol hs es =
    let
      val ps = e_p es
      val fes = etail_fes lfd pol es hs
      val rv = l1_polls [fes]
      val b2 = l1_flush (writable_fds rv) (l1p_b ps)
      val fl = pf_fetch_p lfd pol (filter_in (in_fds fes) (readable_fds rv)) (set_b ps b2)
    in
      case fl of (ps3a, log) =>
      let
        val ps3 = stall_step_ob (pf_held ps3a) (l1p_b ps) log ps3a
        val b4 = l1_reap (closing_of ps3) (l1p_b ps3)
        val es5 = settle_fds_c (ready_pend es rv) (es_end es ps3 b4)
      in etail_fin lfd hs es5 end
    end;

  fun run_e lfd pol ifds acts step fin st es =
    if fin st then ()
    else
      case eacts lfd es (acts st) of (es1, rs) =>
      case etail lfd pol (ifds st) es1 of (rdy, es2) =>
        run_e lfd pol ifds acts step fin (step st rdy rs) es2;
End
