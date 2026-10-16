(*
  protoLiveV: the query handler (proto_handler_v) meets the library's
  per-handler obligation for stateful servers, handler_live_va
  (skeletonVLiveAns), for every protocol and vocabulary: what is owed for
  data D, given the answers ks to its queries, is
  resps ansq fin (proto_all P D) ks, written within (|D| + 2)(2K + 3)
  rounds.  qmachine_live_p_v with henv's four facts unfolded (as
  proto_env_live / proto_handler_live for proto_handler).
*)
Theory protoLiveV
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncTranscript echoServer echoServerSafety
  skeletonV skeletonVLive skeletonVLiveAns
  protoInterface protoServer protoV protoMachineV protoDrainV
Libs
  BasicProvers

(* MAIN: the query handler is live, and has by then received an answer to
   every query of D's complete requests (so, with resps_LENGTH_full, it has
   written a response to each of them) *)
Theorem proto_handler_live_va_full:
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ⇒
  ∀fd g j0 D.
    prompt (proto_handler_v V P ansq fin (fd, "")) g ∧
    henv_t fd (λq. sproj V (trans (proto_handler_v V P ansq fin (fd, "")) q)) g j0 D ∧
    j0 + (LENGTH D + 2) * (2 * LENGTH (proto_all P D) + 3) ≤ LENGTH g ⇒
    ∃j. j ≤ LENGTH g ∧
        resps ansq fin (proto_all P D)
          (kanswers V (trans (proto_handler_v V P ansq fin (fd, "")) (TAKE j g))) ≼
          written fd (sproj V (trans (proto_handler_v V P ansq fin (fd, "")) (TAKE j g))) ∧
        nq ansq (proto_all P D) ≤
          LENGTH (kanswers V (trans (proto_handler_v V P ansq fin (fd, "")) (TAKE j g)))
Proof
  rw[henv_t_def, hread_t_def] >>
  ‘proto_handler_v V P ansq fin (fd, "") = qcomp V P ansq fin fd (QA "")’
    by simp[qcomp_def] >>
  fs[] >>
  ‘∃j'. j' ≤ LENGTH g ∧ DONE V P ansq fin fd g D j'’
    suffices_by (strip_tac >> qexists_tac ‘j'’ >> simp[]) >>
  irule qmachine_live_p_v >> simp[] >>
  qexistsl [‘j0’, ‘j0’, ‘LENGTH D’] >> simp[] >> rpt conj_tac >> rpt strip_tac
  (* (comparable: by simp) waiting while not readable: D read next round, and nothing new read *)
  >- (‘D ≼ Rq V P ansq fin fd g (SUC j)’ by simp[] >>
      ‘Rq V P ansq fin fd g (SUC j) = Rq V P ansq fin fd g j’
        by (‘j < LENGTH g’ by simp[] >>
            qpat_assum ‘proto_ok _’ (fn t1 => qpat_assum ‘vocab_ok _’ (fn t2 =>
            qpat_assum ‘vocab_qok _’ (fn t3 => qpat_assum ‘prompt _ _’ (fn t4 =>
            qpat_assum ‘j < LENGTH g’ (fn t5 =>
              mp_tac (MATCH_MP Rq_Wq_SUC (CONJ (LIST_CONJ [t1, t2, t3, t4]) t5))))))) >>
            simp[]) >>
      fs[])
  (* reading: an outstanding read *)
  >- (first_x_assum irule >> simp[] >>
      irule qmachine_reading >> simp[] >> metis_tac[])
  (* stopped, not invalid: end-of-file was read *)
  >> first_x_assum irule >> simp[] >>
  irule qmachine_eof >> simp[] >> qexists_tac ‘b’ >> simp[]
QED

(* MAIN: the query handler is live, in the library's sense for stateful
   servers *)
Theorem proto_handler_live_va:
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ⇒
  handler_live_va V (λfd. proto_handler_v V P ansq fin (fd, ""))
                  (λD ks. resps ansq fin (proto_all P D) ks)
                  (λD. (LENGTH D + 2) * (2 * LENGTH (proto_all P D) + 3))
Proof
  rw[handler_live_va_def] >>
  drule_all proto_handler_live_va_full >> strip_tac >> metis_tac[]
QED
