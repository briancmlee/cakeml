(*
  The echo server at Level 2: it declares what it waits for (the listener
  and each connection becoming readable), erases to the Level 1 server, and
  is quiet.  So M2's no-busy-waiting theorem applies: a scheduler running it
  may block in select until the listener or some connection is readable
  (or a response is due), with exactly the same behaviour as one that
  polls every round.  The safety property (asyncServerSafety) is about the
  erased server, so it holds for this one too.
*)
Theory asyncServer2
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncLoop2 asyncSched asyncSched2
  asyncServer
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   both2 and map2 are non-expansive
   ------------------------------------------------------------------------ *)

Theorem both2_agree:
  agree_below n (pack c1) (pack c1') ∧ agree_below n (pack c2) (pack c2') ⇒
  agree_below n (pack (both2 c1 c2)) (pack (both2 c1' c2'))
Proof
  simp[agree_below_pack] >> strip_tac >> qx_gen_tac ‘h’ >> strip_tac
  >> ‘agree_below n c1.run c1'.run ∧ agree_below n c2.run c2'.run’
       by simp[agree_below_def]
  >> ‘agree_below n (both c1.run c2.run) (both c1'.run c2'.run)’
       by (irule both_agree >> simp[])
  >> conj_tac >- fs[both2_def, agree_below_def]
  >> ‘par_views (log_of c1.run) (log_of c2.run) h =
      par_views (log_of c1'.run) (log_of c2'.run) h’
       by (irule par_views_cong >> rw[log_of_def])
  >> simp[both2_def, left_view_def, right_view_def, waiting_on_def]
  >> ‘LENGTH (FST (par_views (log_of c1'.run) (log_of c2'.run) h)) = LENGTH h ∧
      LENGTH (SND (par_views (log_of c1'.run) (log_of c2'.run) h)) = LENGTH h’
       by simp[LENGTH_par_views]
  >> simp[]
QED

Theorem nonexpansive2_both2:
  nonexpansive2 (λR. M1 R) ∧ nonexpansive2 (λR. M2 R) ⇒
  nonexpansive2 (λR. both2 (M1 R) (M2 R))
Proof
  rw[nonexpansive2_def, nonexpansive_def] >> irule both2_agree >> simp[]
QED

Theorem nonexpansive2_map2:
  nonexpansive2 (λR. M R) ⇒ nonexpansive2 (λR. map2 f (M R))
Proof
  rw[nonexpansive2_def, nonexpansive_def, agree_below_pack, map2_def, map_def]
  >> first_x_assum drule >> simp[agree_below_pack]
QED

Theorem wf2_map2:
  wf2 c ⇒ wf2 (map2 f c)
Proof
  rw[wf2_def] >- simp[map2_def, wf_map]
  >> irule quiet_map2 >> simp[]
QED

Theorem wf2_both2:
  wf2 c1 ∧ wf2 c2 ⇒ wf2 (both2 c1 c2)
Proof
  rw[wf2_def] >- simp[both2_def, wf_both]
  >> irule quiet_both2 >> simp[]
QED

(* ------------------------------------------------------------------------
   The handler and the server at Level 2
   ------------------------------------------------------------------------ *)

Definition handler_body2_def:
  handler_body2 R fd =
    bind2 (wait_on (Readable fd) (λs. SOME ())) (λu.
    bind2 (emit2 (Read fd)) (λres.
      case res of
        Data d => bind2 (emit2 (Write fd d)) (λw. R fd)
      | Eof => return2 ()
      | _ => R fd))
End

Theorem handler_body2_contractive:
  contractive2 handler_body2
Proof
  rw[contractive2_def, handler_body2_def]
  >> ho_match_mp_tac guarded2_bind2
  >> simp[wait_on_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive2_bind2 >> simp[nonexpansive2_const]
  >> Cases >> simp[nonexpansive2_call, nonexpansive2_const]
  >> ho_match_mp_tac nonexpansive2_bind2 >> simp[nonexpansive2_const, nonexpansive2_call]
QED

Definition handler2_def:
  handler2 = fix2 handler_body2
End

Theorem erase_handler_body2:
  erase (handler_body2 R fd) = handler_body (λq. erase (R q)) fd
Proof
  simp[handler_body2_def, handler_body_def, erase_bind2, erase_wait_on, erase_emit2,
       readable_def]
  >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC
  >> Cases_on ‘res’ >> simp[erase_bind2, erase_emit2, erase_return2]
QED

(* The Level 2 handler erases to the Level 1 handler *)
Theorem erase_handler2:
  erase (handler2 fd) = handler fd
Proof
  simp[handler2_def, handler_def]
  >> irule erase_fix2
  >> simp[handler_body_contractive, handler_body2_contractive, erase_handler_body2]
QED

Theorem wf2_handler2:
  wf2 (handler2 fd)
Proof
  simp[handler2_def] >> irule wf2_fix2 >> simp[handler_body2_contractive]
  >> rw[handler_body2_def]
  >> irule wf2_bind2 >> simp[wf2_wait_on]
  >> irule wf2_bind2 >> simp[wf2_emit2] >> Cases
  >> simp[wf2_return2] >> irule wf2_bind2 >> simp[wf2_emit2]
QED

Definition server_body2_def:
  server_body2 R lfd =
    bind2 (wait_on (Readable lfd) (λs. SOME ())) (λu.
    bind2 (emit2 (Accept lfd)) (λres.
      case res of
        Accepted fd => map2 (λp. ()) (both2 (handler2 fd) (R lfd))
      | _ => R lfd))
End

Theorem server_body2_contractive:
  contractive2 server_body2
Proof
  rw[contractive2_def, server_body2_def]
  >> ho_match_mp_tac guarded2_bind2
  >> simp[wait_on_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive2_bind2 >> simp[nonexpansive2_const]
  >> Cases >> simp[nonexpansive2_call]
  >> ho_match_mp_tac nonexpansive2_map2 >> ho_match_mp_tac nonexpansive2_both2
  >> simp[nonexpansive2_const, nonexpansive2_call]
QED

Definition server2_def:
  server2 = fix2 server_body2
End

Theorem erase_server_body2:
  erase (server_body2 R lfd) = server_body (λq. erase (R q)) lfd
Proof
  simp[server_body2_def, server_body_def, erase_bind2, erase_wait_on, erase_emit2,
       readable_def]
  >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC
  >> Cases_on ‘res’ >> simp[erase_map2, erase_both2, erase_handler2]
QED

(* MAIN: the Level 2 server erases to the Level 1 server, so the safety
   theorem (echo_server_safety) holds for it *)
Theorem erase_server2:
  erase (server2 lfd) = server lfd
Proof
  simp[server2_def, server_def]
  >> irule erase_fix2
  >> simp[server_body_contractive, server_body2_contractive, erase_server_body2]
QED

(* MAIN: the Level 2 server is well-formed and quiet *)
Theorem wf2_server2:
  wf2 (server2 lfd)
Proof
  simp[server2_def] >> irule wf2_fix2 >> simp[server_body2_contractive]
  >> rw[server_body2_def]
  >> irule wf2_bind2 >> simp[wf2_wait_on]
  >> irule wf2_bind2 >> simp[wf2_emit2] >> Cases >> simp[]
  >> irule wf2_map2 >> irule wf2_both2 >> simp[wf2_handler2]
QED

(* MAIN: no busy-waiting for the echo server: a scheduler running it that
   blocks through every idle round (no request in flight, no responses, and
   neither the listener nor any connection readable) emits exactly the same
   actions, and gets exactly the same result, as one that polls every round *)
Theorem server_no_busy_waiting:
  ∀H. let K = blocked (sched_idle [server2 lfd]) [] H in
      sched_log [server lfd] K = sched_log [server lfd] H ∧
      ∀xs. LIST_REL (λt x. (t.comp t.view).result = SOME x) (run [server lfd] K) xs ⇔
           LIST_REL (λt x. (t.comp t.view).result = SOME x) (run [server lfd] H) xs
Proof
  qspec_then ‘[server2 lfd]’ mp_tac (Q.GEN ‘cs’ no_busy_waiting)
  >> simp[wf2_server2, erase_server2]
QED
