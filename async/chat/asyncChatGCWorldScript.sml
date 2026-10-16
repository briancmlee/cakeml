(*
  The GC server in the socket world: its run is the chat server's run, and
  its hub holds exactly the log after the least client cursor.

   - grounds_cong (generic): two machines that agree on the first one's
     histories have the same run;
   - gc_grounds_eq: the GC server's run (snapshots, world states, events)
     is the chat server's, so every theorem about the chat server's trace
     (safety, liveness, timeliness) holds of the GC server's trace;
   - gc_run_space: at every point of the GC server's run, the hub's log is
     exactly the bytes after the least cursor (gc_space).
*)
Theory asyncChatGCWorld
Ancestors
  pair list rich_list arithmetic option string words alist llist
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncM3World asyncM4GRounds asyncM4GTrans asyncM4SockModel asyncM4Relabel
  asyncRunOkGen asyncWithStore asyncWithTap asyncWithTapSim asyncChatSW
  asyncChatModel asyncChatSafe asyncChatLiveV asyncChatLiveCoverRun
  asyncChatGC asyncChatGCRun
Libs
  preamble

(* ------------------------------------------------------------------------
   Runs of machines that agree on the run
   ------------------------------------------------------------------------ *)

Theorem new_actions_ghist_cong:
  (∀k. m2 (ghist ifds m1 s0 k) = m1 (ghist ifds m1 s0 k)) ⇒
  new_actions (log_of m2) (ghist ifds m1 s0 n) = new_actions (log_of m1) (ghist ifds m1 s0 n)
Proof
  strip_tac >> Cases_on ‘n’
  >- (simp[new_actions_def, log_of_def] >>
      first_x_assum (qspec_then ‘0’ mp_tac) >> simp[ghist_def, grounds_def]) >>
  rename1 ‘SUC n’ >>
  ‘ghist ifds m1 s0 (SUC n) ≠ []’
    by (strip_tac >> metis_tac[LENGTH_ghist, LENGTH, numTheory.NOT_SUC]) >>
  ‘FRONT (ghist ifds m1 s0 (SUC n)) = ghist ifds m1 s0 n’
    by (simp[Once ghist_def, grounds_SUC, FRONT_APPEND]) >>
  simp[new_actions_def, log_of_def]
QED

Theorem grounds_cong:
  (∀k. m2 (ghist ifds m1 s0 k) = m1 (ghist ifds m1 s0 k)) ⇒
  ∀n. grounds ifds m2 s0 n = grounds ifds m1 s0 n
Proof
  strip_tac >> Induct >- simp[grounds_def] >>
  simp[grounds_def] >>
  ‘FST (grounds ifds m1 s0 n) = ghist ifds m1 s0 n’ by simp[ghist_def] >>
  Cases_on ‘grounds ifds m1 s0 n’ >> gvs[] >>
  drule_then (qspec_then ‘n’ mp_tac) new_actions_ghist_cong >> simp[]
QED

(* ------------------------------------------------------------------------
   The GC server's run
   ------------------------------------------------------------------------ *)

Theorem gc_server_on_run:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  gc_server lfdn (MAP sfs (ghist ifds (srelabel (chat_server lfdn)) s0 k)) =
  chat_server lfdn (MAP sfs (ghist ifds (srelabel (chat_server lfdn)) s0 k))
Proof
  strip_tac >>
  ‘fresh (TSg (chat_server lfdn) ifds s0 k) ∧ fds_ok (TSg (chat_server lfdn) ifds s0 k)’
    by (conj_tac
        >- (irule gen_fresh >> simp[] >> qexists_tac ‘lfdn’ >> simp[chat_uses_ok_v])
        >> irule fds_ok_TSg_chat >> simp[]) >>
  irule gc_server_eq >>
  qabbrev_tac ‘hh = MAP sfs (ghist ifds (srelabel (chat_server lfdn)) s0 k)’ >>
  ‘trans (chat_server lfdn) hh =
   untag (trans (chat_inner lfdn) (tap_hist chat_tap chat_delta empty_store (chat_inner lfdn) hh))’
    by simp[chat_server_def, trans_with_tap, wf_chat_inner] >>
  gvs[freshc_untag]
QED

(* MAIN: the GC server's run is the chat server's run *)
Theorem gc_grounds_eq:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀n. grounds ifds (srelabel (gc_server lfdn)) s0 n =
      grounds ifds (srelabel (chat_server lfdn)) s0 n
Proof
  strip_tac >> irule grounds_cong >> gen_tac >>
  simp[relabel_def, gc_server_on_run]
QED

Theorem gc_events_eq:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  grounds_events ifds (srelabel (gc_server lfdn)) s0 =
  grounds_events ifds (srelabel (chat_server lfdn)) s0
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  drule_all gc_grounds_eq >> disch_then (qspecl_then [‘ifds’, ‘x’] assume_tac) >>
  simp[grounds_events_def] >>
  ‘new_actions (log_of (srelabel (gc_server lfdn))) (ghist ifds (srelabel (chat_server lfdn)) s0 x) =
   new_actions (log_of (srelabel (chat_server lfdn))) (ghist ifds (srelabel (chat_server lfdn)) s0 x)’
    by (irule new_actions_ghist_cong >> simp[relabel_def, gc_server_on_run]) >>
  ‘FST (grounds ifds (srelabel (chat_server lfdn)) s0 x) =
   ghist ifds (srelabel (chat_server lfdn)) s0 x’ by simp[ghist_def] >>
  Cases_on ‘grounds ifds (srelabel (chat_server lfdn)) s0 x’ >> gvs[]
QED

(* The GC server's trace is the chat server's trace *)
Theorem gc_trace_eq:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  LFLATTEN (LGENLIST (λi. fromList (grounds_events ifds (srelabel (gc_server lfdn)) s0 i)) NONE) =
  LFLATTEN (LGENLIST (λi. fromList (grounds_events ifds (srelabel (chat_server lfdn)) s0 i)) NONE)
Proof
  strip_tac >> drule_all gc_events_eq >> disch_then (qspec_then ‘ifds’ assume_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   Space, along the run
   ------------------------------------------------------------------------ *)

(* MAIN (space): at every point of the GC server's run (any prefix of the
   inner transcript at any round), the GC hub's log holds exactly the bytes
   after the least cursor of the connected clients *)
Theorem gc_run_space:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  GTR = trans (chat_inner lfdn)
         (tap_hist gc_tap gc_delta empty_gstore (chat_inner lfdn)
            (MAP sfs (ghist ifds (srelabel (gc_server lfdn)) s0 n))) ∧
  q ≤ LENGTH GTR ⇒
  gc_inv (tap_fold gc_tap gc_delta empty_gstore (TAKE q GTR)) ∧
  LENGTH (tap_fold gc_tap gc_delta empty_gstore (TAKE q GTR)).glog =
    gend (tap_fold gc_tap gc_delta empty_gstore (TAKE q GTR)) −
    cmin (tap_fold gc_tap gc_delta empty_gstore (TAKE q GTR))
Proof
  strip_tac >>
  drule_all gc_grounds_eq >> disch_then (qspec_then ‘ifds’ assume_tac) >>
  ‘ghist ifds (srelabel (gc_server lfdn)) s0 n = ghist ifds (srelabel (chat_server lfdn)) s0 n’
    by simp[ghist_def] >>
  qabbrev_tac ‘hh = MAP sfs (ghist ifds (srelabel (chat_server lfdn)) s0 n)’ >>
  qabbrev_tac ‘TT = trans (chat_inner lfdn) (tap_hist chat_tap chat_delta empty_store (chat_inner lfdn) hh)’ >>
  ‘fresh (trans (chat_server lfdn) hh) ∧ fds_ok (trans (chat_server lfdn) hh)’
    by (simp[Abbr ‘hh’] >> conj_tac
        >- (irule gen_fresh >> simp[] >> qexists_tac ‘lfdn’ >> simp[chat_uses_ok_v])
        >> irule fds_ok_TSg_chat >> simp[]) >>
  ‘trans (chat_server lfdn) hh = untag TT’
    by simp[Abbr ‘TT’, chat_server_def, trans_with_tap, wf_chat_inner] >>
  ‘freshc TT ∧ fds_ok (untag TT)’ by gvs[freshc_untag] >>
  ‘GTR = TT’ by (gvs[Abbr ‘TT’] >> AP_TERM_TAC >> irule gc_hist_eq >> gvs[]) >>
  ‘guard_ok gc_guard gc_tap gc_delta empty_gstore TT’
    by (simp[Abbr ‘TT’] >> irule chat_gc_guard >> simp[tap_answers, wf_chat_inner] >>
        gvs[]) >>
  ‘gR (tap_fold chat_tap chat_delta empty_store (TAKE q TT))
      (tap_fold gc_tap gc_delta empty_gstore (TAKE q TT))’
    by (irule (MATCH_MP tap_fold_sim gc_sim_ok) >> simp[gR_empty] >>
        irule guard_ok_prefix >> qexists_tac ‘TT’ >> simp[IS_PREFIX_EQ_TAKE] >>
        qexists_tac ‘q’ >> gvs[]) >>
  ‘gc_inv (tap_fold gc_tap gc_delta empty_gstore (TAKE q TT))’ by fs[gR_def] >>
  gvs[gc_space]
QED
