(*
  The accept/fork skeleton at Level 2: server_with2 h2, for any Level 2
  handler h2, erasing to the Level 1 skeleton server_with (asyncServerWith)
  when each h2 fd erases to h fd.

  The server declares what it waits for (the listener becoming readable)
  and runs each accepted connection's handler alongside itself (both2).
  Lifted from asyncHttpServer2H (archive/http-quiet-53), where it was
  stated for the header-tolerant HTTP handler only.
*)
Theory asyncServerWith2
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncLoop2 asyncSched asyncSched2
  asyncServer asyncServer2 asyncServerWith
Libs
  BasicProvers

Definition server_with_body2_def:
  server_with_body2 h2 R lfd =
    bind2 (wait_on (Readable lfd) (λs. SOME ())) (λu.
    bind2 (emit2 (Accept lfd)) (λres.
      case res of
        Accepted fd => map2 (λp. ()) (both2 (h2 fd) (R lfd))
      | _ => R lfd))
End

Theorem server_with_body2_contractive:
  contractive2 (server_with_body2 h2)
Proof
  rw[contractive2_def, server_with_body2_def]
  >> ho_match_mp_tac guarded2_bind2
  >> simp[wait_on_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive2_bind2 >> simp[nonexpansive2_const]
  >> Cases >> simp[nonexpansive2_call]
  >> ho_match_mp_tac nonexpansive2_map2 >> ho_match_mp_tac nonexpansive2_both2
  >> simp[nonexpansive2_const, nonexpansive2_call]
QED

Definition server_with2_def:
  server_with2 h2 = fix2 (server_with_body2 h2)
End

Theorem erase_server_with_body2:
  (∀fd. erase (h2 fd) = h fd) ⇒
  erase (server_with_body2 h2 R lfd) = server_with_body h (λq. erase (R q)) lfd
Proof
  strip_tac
  >> simp[server_with_body2_def, server_with_body_def, erase_bind2, erase_wait_on,
          erase_emit2, readable_def]
  >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC
  >> Cases_on ‘res’ >> simp[erase_map2, erase_both2]
QED

(* The Level 2 skeleton erases to the Level 1 skeleton *)
Theorem erase_server_with2:
  (∀fd. erase (h2 fd) = h fd) ⇒ erase (server_with2 h2 lfd) = server_with h lfd
Proof
  strip_tac >> simp[server_with2_def, server_with_def]
  >> qspecl_then [‘server_with_body h’, ‘server_with_body2 h2’] mp_tac
       (Q.GENL [‘body1’, ‘body2’] erase_fix2)
  >> simp[server_with_body_contractive, server_with_body2_contractive,
          erase_server_with_body2]
QED

Theorem wf2_server_with2:
  (∀fd. wf2 (h2 fd)) ⇒ wf2 (server_with2 h2 lfd)
Proof
  strip_tac >> simp[server_with2_def] >> irule wf2_fix2
  >> simp[server_with_body2_contractive]
  >> rw[server_with_body2_def]
  >> irule wf2_bind2 >> simp[wf2_wait_on]
  >> irule wf2_bind2 >> simp[wf2_emit2] >> Cases >> simp[]
  >> irule wf2_map2 >> irule wf2_both2 >> simp[]
QED

