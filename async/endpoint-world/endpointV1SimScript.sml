(*
  Version 1 as version 2, for fd-disciplined programs (design/35 §4,
  option A; toward v1_instance_disc).

  From a version-1 server world sk, the version-2 world v2of1 lfd sk:
   - the schedule, renamed (rn1_sched): Connect l c becomes Connect2 l and c
     is the next client; Data c bs and Eof c go to c's client number (its
     position in connect order);
   - the allocation gives client j the fd of the j-th connect (conn_fd), or
     the lowest free fd if that one is in use (so alloc_ok holds).
  A program that only touches the listener and connections it has accepted
  cannot tell the two worlds apart.
*)
Theory endpointV1Sim
Ancestors
  llist alist words rich_list indexedLists ffiSpikeSocketFFI ffiSpikeSocketFair
  socketV2FFI socketV2Fair EchoSpec EchoSpec2 EchoSpec2Bite
Libs
  preamble

(* ------------------------------------------------------------------------
   The renamed schedule
   ------------------------------------------------------------------------ *)

(* cs: the connections so far, in connect order *)
Definition rn1_arr_def:
  rn1_arr (cs : word64 list) (Connect l c) = (cs ++ [c], Connect2 l) ∧
  rn1_arr cs (Data c bs) = (cs, Data2 (findi c cs) bs) ∧
  rn1_arr cs (Eof c) = (cs, Eof2 (findi c cs))
End

Definition rn1_step_def:
  rn1_step cs [] = (cs, []) ∧
  rn1_step cs (a :: as) =
    let (cs1, b) = rn1_arr cs a;
        (cs2, bs) = rn1_step cs1 as
    in (cs2, b :: bs)
End

Definition rn1_sched_def:
  rn1_sched cs ll =
    LUNFOLD (λ(cs, ll). case LHD ll of
                        | NONE => NONE
                        | SOME st => SOME ((FST (rn1_step cs st), THE (LTL ll)),
                                           SND (rn1_step cs st))) (cs, ll)
End

Theorem rn1_sched_LHD:
  LHD (rn1_sched cs ll) = OPTION_MAP (λst. SND (rn1_step cs st)) (LHD ll)
Proof
  simp[rn1_sched_def, Once LUNFOLD] >> CASE_TAC >> simp[]
QED

Theorem rn1_sched_LTL:
  LHD ll = SOME st ⇒
  LTL (rn1_sched cs ll) = SOME (rn1_sched (FST (rn1_step cs st)) (THE (LTL ll)))
Proof
  simp[rn1_sched_def, Once LUNFOLD]
QED

(* The connections of a step's arrivals, in order *)
Definition step_conns_def:
  step_conns st = FLAT (MAP (λa. case a of Connect l c => [c] | _ => []) st)
End

Theorem rn1_step_conns:
  ∀st cs. FST (rn1_step cs st) = cs ++ step_conns st
Proof
  Induct >> simp[rn1_step_def, step_conns_def] >> Cases >>
  simp[rn1_arr_def] >> rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  fs[step_conns_def] >> metis_tac[FST, APPEND_ASSOC]
QED

(* The connections of the first n steps of a schedule *)
Definition sched_conns_def:
  sched_conns 0 ll = [] ∧
  sched_conns (SUC n) ll =
    case LHD ll of
    | NONE => []
    | SOME st => step_conns st ++ sched_conns n (THE (LTL ll))
End

(* The fd of the j-th connect of the schedule (0w if there is none) *)
Definition conn_fd_def:
  conn_fd ll j =
    if ∃n. j < LENGTH (sched_conns n ll)
    then EL j (sched_conns (LEAST n. j < LENGTH (sched_conns n ll)) ll)
    else 0w
End

(* The allocation: client j gets the fd of the j-th connect, unless it is
   in use *)
Definition alloc1_def:
  alloc1 ll j used = let c = conn_fd ll j in if MEM c used then lowest_free used else c
End

Theorem alloc1_ok:
  alloc_ok (alloc1 ll)
Proof
  rw[alloc_ok_def, alloc1_def] >>
  mp_tac lowest_free_alloc_ok >> rw[alloc_ok_def]
QED

(* The version-2 world of a version-1 world *)
Definition v2of1_def:
  v2of1 lfd (sk : sockets) =
    <| listening := [(lfd, [])]; clients := []; open_fds := []; reserved := [];
       alloc := alloc1 sk.sched; future := rn1_sched [] sk.sched |>
End
