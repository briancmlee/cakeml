(*
  asyncProtoLiveV: the query handler (proto_handler_v) meets the library's
  per-handler obligation for stateful servers, handler_live_va
  (asyncServerVLiveA), for every protocol and vocabulary: what is owed for
  data D, given the answers ks to its queries, is
  resps ansq fin (proto_all P D) ks, written within (|D| + 2)(2K + 3)
  rounds.  qmachine_live_p_v with henv's four facts unfolded (as
  proto_env_live / proto_handler_live for proto_handler).
*)
Theory asyncProtoLiveV
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncServerV asyncServerVLive asyncServerVLiveA
  asyncProto asyncProtoServer asyncProtoV asyncProtoMachineV asyncProtoDrainV
Libs
  BasicProvers

(* MAIN: the query handler is live, in the library's sense for stateful
   servers *)
Theorem proto_handler_live_va:
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ⇒
  handler_live_va V (λfd. proto_handler_v V P ansq fin (fd, ""))
                  (λD ks. resps ansq fin (proto_all P D) ks)
                  (λD. (LENGTH D + 2) * (2 * LENGTH (proto_all P D) + 3))
Proof
  rw[handler_live_va_def, henv_t_def, hread_t_def] >>
  ‘proto_handler_v V P ansq fin (fd, "") = qcomp V P ansq fin fd (QA "")’
    by simp[qcomp_def] >>
  fs[] >>
  ‘∃j'. j' ≤ LENGTH g ∧
        resps ansq fin (proto_all P D) (Kq V P ansq fin fd g j') ≼
        Wq V P ansq fin fd g j'’
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
