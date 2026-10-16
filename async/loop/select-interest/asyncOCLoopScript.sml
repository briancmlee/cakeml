(*
  Option C §2.3: the event loop that selects on the declared interest, in
  CakeML, in the Level 2 socket program (after asyncOCProtoProg).

      fun step_q (fds, c) =                 (* c = (acts, s), Level 2 *)
        let val rs = perform acts
            val u  = case acts of
                       [] => q_wait_ready (sort_num (interest c))
                     | _ => ()
            val rdy = Socket.poll fds
        in (add_accepted fds rs, poll2 c (rdy, 0, rs)) end
      fun run_q st = run_q (step_q st)

  This is #46's step_b / step_l (asyncM4BlkLoop, asyncM4LiveLoop) with the
  select set read from the computation: the fds it declares, sorted
  (asyncOCSel's qsel).  So select waits for exactly what the computation
  waits for (sel_covers_qsel), by construction; there is no live-list
  bookkeeping, and no spin (#56).  The poll, the world and the trace are
  #46's: the rounds are lbgrounds (qsel c) (asyncM4BlkSelWorld).

  The FFI calls' specs are asyncM4BlkLoop's (perform, Socket.poll, over
  SSEL); select's config encoder and wait_ready are re-added here under
  their own names (q_...), as the loop is one program with the Level 2
  server.

  MAIN: run_q_spec, run_q_stuck_spec, run_q_two_outcomes.
*)
Theory asyncOCLoop
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncTranscript
  asyncCfActModel asyncCfActProg asyncCfReactWorld asyncM3World asyncM3Prog
  asyncM3Loop asyncM4GRounds asyncM4Loop asyncM4SockServer asyncM4BlkWorld
  asyncM4BlkTrace asyncM4BlkLoop asyncM4BlkSelWorld
  ffiSpikeSocketFFI ffiSpikeSocketProg ffiSpikeSocketProof
  ffiSpikeSocketDiv ffiSpikeSocketFair ffiSpikeSocketSelect cfDiv
  asyncOCModel asyncOCProg asyncOCSpec asyncOCProtoProg asyncOCFinite
  asyncOCSel ml_translator mlstring Marshalling std_prelude llist misc
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib
  ml_translatorLib

val _ = translation_extends "asyncOCProtoProg"

(* ------------------------------------------------------------------------
   select's config, and sorting
   ------------------------------------------------------------------------ *)

Definition q_sel_byte_def:
  q_sel_byte (w:word8) = CHR (w2n w)
End

Definition q_n2w8_def:
  q_n2w8 (i:num) : word8 list =
    [n2w (i DIV 256 ** 7); n2w (i DIV 256 ** 6); n2w (i DIV 256 ** 5);
     n2w (i DIV 256 ** 4); n2w (i DIV 256 ** 3); n2w (i DIV 256 ** 2);
     n2w (i DIV 256); n2w i]
End

Definition q_fd_chars_def:
  q_fd_chars n = MAP q_sel_byte (q_n2w8 n)
End

Definition q_conf_def:
  q_conf ns = implode (FLAT (MAP q_fd_chars ns))
End

val r = translate q_sel_byte_def;

Theorem q_sel_byte_side[local]:
  q_sel_byte_side w
Proof
  simp [fetch "-" "q_sel_byte_side_def", w2n_lt_256]
QED

val _ = update_precondition q_sel_byte_side;

val r = translate (q_n2w8_def |> SIMP_RULE arith_ss []);
val r = translate q_fd_chars_def;
val r = translate q_conf_def;
val r = translate ins_num_def;
val r = translate sort_num_def;

Theorem q_conf_sel_conf:
  q_conf = sel_conf
Proof
  ‘q_fd_chars = sel_fd_chars’
    by simp [FUN_EQ_THM, q_fd_chars_def, sel_fd_chars_def, q_n2w8_def, n2w8_def,
             q_sel_byte_def, sel_byte_def] >>
  simp [FUN_EQ_THM, q_conf_def, sel_conf_def]
QED

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun q_wait_ready fds =
    let
      val a = Word8Array.array 0 (Word8.fromInt 0)
      val u = #(sock_select) (q_conf fds) a
    in () end;

  fun step_q st =
    case st of (fds, c) =>
    case c of (acts, s) =>
      let
        val rs = perform acts
        val u = (case acts of [] => q_wait_ready (sort_num (interest c))
                            | a :: rest => ())
        val rdy = Socket.poll fds
      in (add_accepted fds rs, poll2 c (rdy, 0, rs)) end;
End

Quote add_cakeml:
  fun run_q st = run_q (step_q st);
End

val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   select
   ------------------------------------------------------------------------ *)

Theorem q_wait_ready_spec:
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ sock_wait fds s = SOME k ⇒
  app (p:'ffi ffi_proj) q_wait_ready_v [fdsv] (SSEL s evs)
    (POSTv v. &UNIT_TYPE () v * SSEL (ticks k s) (evs ++ [select_event fds]))
Proof
  strip_tac
  \\ xcf_with_def (fetch "-" "q_wait_ready_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av _’
  \\ xlet ‘POSTv uv. W8ARRAY av [] * SSEL (ticks k s) (evs ++ [select_event fds])’
  >- (simp [SSEL_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, q_conf_sel_conf, sel_conf_fds_bytes]
      \\ qexistsl [‘fds_bytes fds’, ‘emp’, ‘sockets_encode s’,
                   ‘mk_ffi_next ssel_ffi_part’, ‘ssel_names’, ‘evs’]
      \\ xsimpl
      \\ simp [ssel_ffi_part_def, mk_ffi_next_def, ffi_sock_select_def,
               select_event_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ xcon \\ xsimpl
QED

Theorem q_wait_ready_stuck_spec:
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ sock_wait fds s = NONE ⇒
  app (p:'ffi ffi_proj) q_wait_ready_v [fdsv] (SSEL s evs)
    (POSTf n. λc b. &(n = «sock_select» ∧ c = fds_bytes fds ∧ b = []) *
                  SSEL s evs * SEP_EXISTS av. W8ARRAY av [])
Proof
  strip_tac
  \\ xcf_with_def (fetch "-" "q_wait_ready_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av _’
  \\ xlet ‘POSTf n. λc b. &(n = «sock_select» ∧ c = fds_bytes fds ∧ b = []) *
                        SSEL s evs * W8ARRAY av []’
  >- (simp [SSEL_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, q_conf_sel_conf, sel_conf_fds_bytes]
      \\ qexistsl [‘fds_bytes fds’, ‘emp’, ‘sockets_encode s’,
                   ‘mk_ffi_next ssel_ffi_part’, ‘ssel_names’, ‘evs’]
      \\ xsimpl
      \\ simp [ssel_ffi_part_def, mk_ffi_next_def, ffi_sock_select_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ xsimpl \\ qexists_tac ‘av’ \\ simp [SEP_IMP_REFL]
QED

(* The declared fds, sorted: what the code passes to select *)
Theorem LIST_TYPE_SEV[local]:
  ∀l v. LIST_TYPE SEV l v ⇔ LIST_TYPE NUM (MAP w2n l) v
Proof
  Induct >> simp[LIST_TYPE_def, SEV_def]
QED
