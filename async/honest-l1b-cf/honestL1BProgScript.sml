(*
  The blocking L1 (honestL1BModel) in CakeML, on the prefetching L1's code
  (honestL1PFProg), which it reuses unchanged.  One new branch: a round
  with no actions in an idle L1 state (pf_idle) polls BLOCKING (block flag
  1, c_pollb), then runs the PF round's tail after its poll (pf_aftr, the
  model's pf_after).  Every other round is step_pf's.

  The code has no busy test: it is for servers that are never busy (bz =
  K F, as the echo), so an idle round is one with no actions.
*)
Theory honestL1BProg
Ancestors
  ml_translator honestL0 honestL0World honestL1Model honestL1PFModel honestL1BModel
  honestL1PFProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "honestL1PFProg";

fun tr th = translate (th |> REWRITE_RULE [GSYM mllistTheory.take_def,
                                          GSYM mllistTheory.drop_def,
                                          GSYM lmem_MEM]);

(* The model's idle test, without its unused policy *)
Definition pf_idle_c_def:
  pf_idle_c lfd ps hs ⇔
    ps.pause = 0 ∧ pf_ready lfd ps hs = [] ∧ ps.b.closing = [] ∧
    EVERY (λ(f, bs). bs = []) ps.b.outbox ∧
    EVERY (λf. MEM f (MAP FST ps.stalls)) (pf_held ps) ∧
    EVERY (λ(f, n). n = 0 ∧ MEM f (pf_held ps)) ps.stalls
End

Theorem pf_idle_c:
  pf_idle_c lfd ps hs ⇔ pf_idle lfd hw ps hs
Proof
  simp[pf_idle_c_def, pf_idle_def]
QED

val r = tr pf_idle_c_def;

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun c_pollb fes =
    str_to_bytes (L0.poll (bytes_to_str [Word8.fromInt 1]) (bytes_to_str (poll_buf fes)));

  fun pf_aftr lfd hw hs ps fes rv =
    let
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

  fun pf_tailb lfd hw hs ps =
    let
      val fes = pf_poll_set_hw lfd hw ps hs
      val rv = poll_revents fes (c_pollb fes)
    in pf_aftr lfd hw hs ps fes rv end;

  fun step_pfb st =
    case st of (lfd, hw, fds, ps, c) =>
    case c of (acts, s) =>
    if not (hdl_room lfd ps (naccepts acts)) then st else
    case pacts lfd ps acts of (ps1, rs) =>
    let
      val hs = map_w64 fds
      val idle = (case acts of [] => pf_idle_c lfd ps1 hs | a :: rest => False)
    in
      case (if idle then pf_tailb lfd hw hs ps1 else pf_tail lfd hw hs ps1) of (rdy, ps2) =>
        (lfd, hw, add_accepted fds rs, ps2, Async.poll c (map_num rdy, 0, rs))
    end;

  fun run_pfb st = run_pfb (step_pfb st);
End
