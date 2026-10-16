(*
  The handle-layer event loop in CakeML (the model: loopHandlesModel).

      fun hdo lfd (tbl, nxt) a =          (* one action, on handles *)
        Accept l  => accept; a new fd f gets handle hdln lfd nxt
        Read h n  => read the fd of h; on EOF, SocketClose.close it and
                     drop h; a closed h reads as EOF
        Write h s => write to the fd of h (nothing if h is closed)
      fun hperform lfd hs acts = (hdo on each action, in order)
      fun step_h (lfd, fds, hs, c) =
        perform c's actions; poll the fds of the interest handles fds;
        poll c with the ready handles; add the accepted handles to fds
      fun run_h st = run_h (step_h st)

  The table operations are pure functions on numbers, translated.  The
  code is appended to the version-1 echo program's translation state with
  SocketClose (lifetimeProg): the server, the Async library and the
  Socket module are version 1's, unchanged.
*)
Theory loopHandlesProg
Ancestors
  ml_translator loopHandlesModel lifetimeProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "lifetimeProg";

(* ------------------------------------------------------------------------
   The table, on numbers
   ------------------------------------------------------------------------ *)

Definition tlookup_def:
  tlookup (h:num) [] = NONE ∧
  tlookup h ((k, f:num) :: t) = if k = h then SOME f else tlookup h t
End

Definition tdelete_def:
  tdelete (h:num) [] = [] ∧
  tdelete h ((k, f:num) :: t) =
    if k = h then tdelete h t else (k, f) :: tdelete h t
End

(* The fds polled for the interest handles *)
Definition hpfds_def:
  hpfds (lfd:num) tbl [] = [] ∧
  hpfds lfd tbl (h :: hs) =
    (case tlookup h tbl of
     | SOME f => [f]
     | NONE => if h = lfd then [h] else []) ++ hpfds lfd tbl hs
End

(* Membership, translatable *)
Definition nmem_def:
  nmem (x:num) [] = F ∧
  nmem x (y :: ys) = (x = y ∨ nmem x ys)
End

Theorem nmem_MEM:
  ∀ys. nmem x ys ⇔ MEM x ys
Proof
  Induct >> simp[nmem_def]
QED

(* The ready handles, given the ready fds *)
Definition hrdy_def:
  hrdy (lfd:num) tbl rdy [] = [] ∧
  hrdy lfd tbl rdy (h :: hs) =
    (if (case tlookup h tbl of
         | SOME f => nmem f rdy
         | NONE => if h = lfd then nmem h rdy else T)
     then [h] else []) ++ hrdy lfd tbl rdy hs
End

val r = translate tlookup_def;
val r = translate tdelete_def;
val r = translate hdln_def;
val r = translate hpfds_def;
val r = translate nmem_def;
val r = translate hrdy_def;

(* ------------------------------------------------------------------------
   The loop
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun hdo lfd hs a =
    case hs of (tbl, nxt) =>
    case a of
      Accept l =>
        (case Socket.accept l of
           None => (hs, Accepted None)
         | Some f =>
             let val h = hdln lfd nxt in (((h, f) :: tbl, nxt + 1), Accepted (Some h)) end)
    | Read h n =>
        (case tlookup h tbl of
           None => (hs, Got (Some ""))
         | Some f =>
             (case Socket.read f n of
                None => (hs, Got None)
              | Some s =>
                  if s = "" then
                    let val u = SocketClose.close f in ((tdelete h tbl, nxt), Got (Some "")) end
                  else (hs, Got (Some s))))
    | Write h s =>
        (case tlookup h tbl of
           None => (hs, Wrote)
         | Some f => let val u = Socket.write f s in (hs, Wrote) end);

  fun hperform lfd hs acts =
    case acts of
      [] => (hs, [])
    | a :: rest =>
        (case hdo lfd hs a of
           (hs1, r) =>
             (case hperform lfd hs1 rest of
                (hs2, rs) => (hs2, r :: rs)));

  fun step_h st =
    case st of (lfd, fds, hs, c) =>
    case c of (acts, s) =>
    case hperform lfd hs acts of (hs1, rs) =>
    case hs1 of (tbl1, nxt1) =>
      let
        val rdy = Socket.poll (hpfds lfd tbl1 fds)
        val rh = hrdy lfd tbl1 rdy fds
      in (lfd, add_accepted fds rs, hs1, Async.poll c (rh, 0, rs)) end;
End

Quote add_cakeml:
  fun run_h st = run_h (step_h st);
End
