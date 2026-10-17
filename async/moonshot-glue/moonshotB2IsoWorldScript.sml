(*
  b2_iso_stmt, the per-process part: under fd0_safe (moonshotStep12Stmts),
  no process ever has a socket on fd 0 (zinv), so every channel that sends
  is an episode's (oinv: a channel outside the ghost list cs has sent
  nothing).  Two cases of fd0_safe:
   - fdok_first ∧ no_close0: the first call found fd 0 open, while no
     socket or listener existed, so fd 0 is in use and is neither; it stays
     in use (never closed) and so is never handed out;
   - no_conn: no connect and no accept, so no fd is ever a socket.
*)
Theory moonshotB2IsoWorld
Ancestors
  moonshotW2 honestL0World honestL0WorldProps honestL0Rely l0sys l0sysEpisodes
  l0sysInv l0sysInvCall l0sysMono l0sysStep honestL0
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* fd0_safe's two cases *)

Definition fdok_first_def:
  fdok_first evs ⇔ ∃i rest. evs = IO_event (ExtCall «sys_fdok») [0w] [(i, 1w)] :: rest
End

Definition no_conn_def:
  no_conn evs ⇔
    ∀conf bs. ¬MEM (IO_event (ExtCall «sys_connect») conf bs) evs ∧
              ¬MEM (IO_event (ExtCall «sys_accept») conf bs) evs
End

(*---------------------------------------------------------------------------*)
(* The invariants: G is the process's whole trace, evs its calls so far *)

Definition zinv_def:
  zinv G evs (w : l0world) ⇔
    ¬MEM 0w (MAP FST w.open_fds) ∧
    (evs = [] ⇒ w.open_fds = [] ∧ w.listeners = []) ∧
    (fdok_first G ∧ no_close0 G ∧ evs ≠ [] ⇒
     MEM 0w (l0_used w) ∧ ¬MEM 0w (MAP FST w.listeners)) ∧
    (no_conn G ⇒ w.open_fds = [])
End

Definition oinv_def:
  oinv (w : l0world) cs ⇔ ∀c. c < LENGTH w.chans ∧ ¬MEM c cs ⇒ (EL c w.chans).sent = []
End

Theorem zinv_clock_hist[simp]:
  zinv G evs (w with <| clock := n; hist := h |>) ⇔ zinv G evs w
Proof
  simp[zinv_def, l0_used_def]
QED

Theorem oinv_clock_hist[simp]:
  oinv (w with <| clock := n; hist := h |>) cs ⇔ oinv w cs
Proof
  simp[oinv_def]
QED

Theorem MAP_FST_NIL:
  MAP FST l = [] ⇔ l = []
Proof
  Cases_on ‘l’ >> simp[]
QED

Theorem MEM_sub_NIL:
  (∀x. MEM x l1 ⇒ MEM x l2) ∧ l2 = [] ⇒ l1 = []
Proof
  Cases_on ‘l1’ >> rw[] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Arrivals *)

Theorem deliver_fields:
  (l0_deliver w a).open_fds = w.open_fds ∧ (l0_deliver w a).reserved = w.reserved ∧
  MAP FST (l0_deliver w a).listeners = MAP FST w.listeners ∧
  LENGTH w.chans ≤ LENGTH (l0_deliver w a).chans ∧
  ∀c. c < LENGTH (l0_deliver w a).chans ⇒
      (EL c (l0_deliver w a).chans).sent = if c < LENGTH w.chans then (EL c w.chans).sent else []
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> gvs[] >>
  gvs[EL_LUPDATE, EL_APPEND1, EL_APPEND2, break_lchan_def, fresh_lchan_def] >>
  rw[] >> gvs[] >>
  ‘c = LENGTH w.chans’ by simp[] >> simp[EL_APPEND2, fresh_lchan_def]
QED

Theorem zinv_deliver:
  zinv G evs w ⇒ zinv G evs (l0_deliver w a)
Proof
  qspecl_then [‘w’, ‘a’] strip_assume_tac (GEN_ALL deliver_fields) >>
  rw[zinv_def, l0_used_def] >> gvs[] >>
  metis_tac[MAP_FST_NIL]
QED

Theorem oinv_deliver:
  oinv w cs ⇒ oinv (l0_deliver w a) cs
Proof
  qspecl_then [‘w’, ‘a’] strip_assume_tac (GEN_ALL deliver_fields) >>
  rw[oinv_def] >> first_x_assum drule >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Exit *)

Theorem FOLDL_breaks_fields:
  ∀q w. (FOLDL (λw j. upd_lchan j (break_lchan e kp) w) w q).open_fds = w.open_fds ∧
        (FOLDL (λw j. upd_lchan j (break_lchan e kp) w) w q).listeners = w.listeners ∧
        (FOLDL (λw j. upd_lchan j (break_lchan e kp) w) w q).reserved = w.reserved ∧
        LENGTH (FOLDL (λw j. upd_lchan j (break_lchan e kp) w) w q).chans = LENGTH w.chans ∧
        ∀c. c < LENGTH w.chans ⇒
            (EL c (FOLDL (λw j. upd_lchan j (break_lchan e kp) w) w q).chans).sent =
            (EL c w.chans).sent
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘upd_lchan h (break_lchan e kp) w’ strip_assume_tac) >>
  gvs[upd_lchan_def, EL_LUPDATE] >> rw[break_lchan_def]
QED

Theorem close_fd_fields:
  ∀f w.
  (∀x. MEM x (close_fd f w).open_fds ⇒ MEM x w.open_fds) ∧
  (∀g. MEM g (MAP FST (close_fd f w).listeners) ⇒ MEM g (MAP FST w.listeners)) ∧
  LENGTH (close_fd f w).chans = LENGTH w.chans ∧
  (∀c. c < LENGTH w.chans ⇒ (EL c (close_fd f w).chans).sent = (EL c w.chans).sent)
Proof
  rpt gen_tac >> simp[close_fd_def] >> every_case_tac >> simp[FOLDL_breaks_fields] >>
  gvs[upd_lchan_def, EL_LUPDATE, ADELKEY_def, MEM_FILTER, MEM_MAP] >> rw[] >>
  metis_tac[]
QED

Theorem close_fds_fields:
  ∀fs w. (∀x. MEM x (FOLDL (λw f. close_fd f w) w fs).open_fds ⇒ MEM x w.open_fds) ∧
         (∀g. MEM g (MAP FST (FOLDL (λw f. close_fd f w) w fs).listeners) ⇒
              MEM g (MAP FST w.listeners)) ∧
         LENGTH (FOLDL (λw f. close_fd f w) w fs).chans = LENGTH w.chans ∧
         (∀c. c < LENGTH w.chans ⇒
              (EL c (FOLDL (λw f. close_fd f w) w fs).chans).sent = (EL c w.chans).sent) ∧
         (MEM 0w (l0_used w) ∧ ¬MEM 0w fs ⇒ MEM 0w (l0_used (FOLDL (λw f. close_fd f w) w fs)))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘close_fd (h:word64) (w:l0world)’ strip_assume_tac) >>
  qspecl_then [‘h’, ‘w’] strip_assume_tac (GEN_ALL close_fd_fields) >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >>
  metis_tac[close_fd_used]
QED

Theorem zinv_close_all:
  zinv G evs w ⇒ zinv G evs (close_all w)
Proof
  rewrite_tac[zinv_def] >> strip_tac >>
  qspecl_then [‘MAP FST w.open_fds ++ MAP FST w.listeners’, ‘w’] strip_assume_tac
    close_fds_fields >>
  ‘close_all w = FOLDL (λw f. close_fd f w) w (MAP FST w.open_fds ++ MAP FST w.listeners)’
    by simp[close_all_def] >>
  pop_assum SUBST1_TAC >>
  qabbrev_tac ‘w2 = FOLDL (λw f. close_fd f w) w (MAP FST w.open_fds ++ MAP FST w.listeners)’ >>
  rpt conj_tac
  >- (strip_tac >> fs[MEM_MAP] >> metis_tac[])
  >- (strip_tac >> fs[] >> conj_tac >- (irule MEM_sub_NIL >> metis_tac[]) >>
      ‘MAP FST w2.listeners = []’
        by (irule MEM_sub_NIL >> qexists_tac ‘MAP FST w.listeners’ >> simp[]) >>
      fs[MAP_FST_NIL])
  >- (strip_tac >> fs[] >> rpt conj_tac >> metis_tac[])
  >- (strip_tac >> fs[] >> irule MEM_sub_NIL >> metis_tac[])
QED

Theorem oinv_close_all:
  oinv w cs ⇒ oinv (close_all w) cs
Proof
  qspecl_then [‘MAP FST w.open_fds ++ MAP FST w.listeners’, ‘w’] strip_assume_tac
    close_fds_fields >>
  rw[oinv_def, close_all_def] >> gvs[]
QED

(*---------------------------------------------------------------------------*)
(* Calls *)

Theorem call_fields:
  fds_lt w ∧ l0_rely w ∧ l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
  (∀x. MEM x w1.open_fds ⇒
       MEM x w.open_fds ∨ (nm = «sys_connect» ∨ nm = «sys_accept») ∧ ¬MEM (FST x) (l0_used w)) ∧
  (∀g. MEM g (MAP FST w1.listeners) ⇒ MEM g (MAP FST w.listeners) ∨ ¬MEM g (l0_used w)) ∧
  (∀c. c < LENGTH w.chans ∧ (∀f. l0_chan_of w f ≠ SOME c) ⇒
       (EL c w1.chans).sent = (EL c w.chans).sent)
Proof
  strip_tac >> ‘w.fd_limit ≤ 2 ** 31’ by fs[l0_rely_def] >>
  ‘∀f. l0_alloc w = SOME f ⇒ ¬MEM f (l0_used w)’ by metis_tac[l0_alloc_fresh] >>
  Cases_on ‘nm = «sys_poll»’ >- (gvs[] >> drule l0_call_poll_unblock >> simp[]) >>
  gvs[unblock_other, l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  FIRST [
    qpat_x_assum ‘l0_listen _ _ = _’ mp_tac >> rw[l0_listen_def, AllCaseEqs()] >> gvs[] >>
    res_tac >> gvs[] >> NO_TAC,
    qpat_x_assum ‘l0_accept _ _ = _’ (strip_assume_tac o MATCH_MP l0_accept_cases) >>
    gvs[upd_lchan_def, EL_LUPDATE] >> rw[break_lchan_def] >> res_tac >> gvs[] >> NO_TAC,
    qpat_x_assum ‘l0_recv _ _ _ = _’ (strip_assume_tac o MATCH_MP l0_recv_cases) >>
    gvs[upd_lchan_def, EL_LUPDATE] >> rw[] >> NO_TAC,
    qpat_x_assum ‘l0_send _ _ _ = _’ (strip_assume_tac o MATCH_MP l0_send_cases) >>
    gvs[upd_lchan_def, EL_LUPDATE] >> rw[] >> gvs[] >> NO_TAC,
    qpat_x_assum ‘l0_shutdown _ _ = _’ mp_tac >>
    rw[l0_shutdown_def, AllCaseEqs()] >> gvs[upd_lchan_def, EL_LUPDATE] >> rw[] >> NO_TAC,
    qpat_x_assum ‘l0_connect _ _ = _’
      (strip_assume_tac o SIMP_RULE std_ss [LET_THM] o MATCH_MP l0_connect_cases) >>
    gvs[upd_lchan_def, EL_LUPDATE, EL_APPEND1] >> rw[EL_APPEND1] >> res_tac >> gvs[] >> NO_TAC,
    qpat_x_assum ‘l0_connerr _ _ = _’ mp_tac >>
    rw[l0_connerr_def, AllCaseEqs()] >> gvs[upd_lchan_def, EL_LUPDATE] >> rw[] >> NO_TAC,
    qpat_x_assum ‘l0_close _ _ = _’ mp_tac >> rw[l0_close_def, AllCaseEqs()] >>
    qspecl_then [‘bytes_fd conf’, ‘w’] strip_assume_tac close_fd_fields >>
    gvs[] >> metis_tac[] >> NO_TAC,
    gvs[] >> NO_TAC]
QED

Theorem fdok_call_same:
  l0_call «sys_fdok» conf bytes w = SOME (FFIreturn out w1) ⇒ w1 = w
Proof
  simp[Once l0_call_def] >> rw[]
QED

Theorem fdok0_first_call:
  l0_rely w ∧ l0_call «sys_fdok» (unblock «sys_fdok» [0w]) bytes w = SOME (FFIreturn out w1) ∧
  [(i, 1w)] = ZIP (bytes, out) ⇒ w1 = w ∧ MEM 0w (l0_used w)
Proof
  strip_tac >> ‘w1 = w’ by (drule fdok_call_same >> simp[]) >>
  drule_all fdok_ev_used >> simp[]
QED

Theorem zinv_call:
  zinv G evs w ∧ (fdok_first G ∧ no_close0 G ∨ no_conn G) ∧ fds_lt w ∧ l0_rely w ∧
  l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ∧
  evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))] ≼ G ⇒
  zinv G (evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))]) w1
Proof
  strip_tac >> drule_all call_fields >> strip_tac >>
  ‘MEM (IO_event (ExtCall nm) conf (ZIP (bytes, out))) G’
    by (gvs[IS_PREFIX_APPEND] >> simp[]) >>
  ‘no_conn G ⇒ nm ≠ «sys_connect» ∧ nm ≠ «sys_accept»’
    by (rewrite_tac[no_conn_def] >> rpt strip_tac >> gvs[]) >>
  ‘no_conn G ⇒ w1.open_fds = []’
    by (strip_tac >> ‘nm ≠ «sys_connect» ∧ nm ≠ «sys_accept»’ by fs[] >>
        ‘w.open_fds = []’ by fs[zinv_def] >> Cases_on ‘w1.open_fds’ >> simp[] >>
        qpat_x_assum ‘∀x. MEM x (_ :: _) ⇒ _’ (qspec_then ‘h’ mp_tac) >> simp[]) >>
  ‘fdok_first G ∧ no_close0 G ⇒ MEM 0w (l0_used w1) ∧ ¬MEM 0w (MAP FST w1.listeners) ∧
                               ¬MEM 0w (MAP FST w1.open_fds)’
    by (strip_tac >> Cases_on ‘evs’
        >- ((* the first call: sys_fdok of fd 0, answered 1 *)
            qpat_x_assum ‘fdok_first G’ (strip_assume_tac o REWRITE_RULE [fdok_first_def]) >>
            qpat_x_assum ‘_ ≼ G’ mp_tac >> asm_rewrite_tac[APPEND, isPREFIX_THM] >>
            simp_tac (srw_ss()) [] >> rpt strip_tac >>
            qpat_x_assum ‘nm = _’ SUBST_ALL_TAC >> qpat_x_assum ‘conf = _’ SUBST_ALL_TAC >>
            ‘[(i, 1w)] = ZIP (bytes, out)’ by asm_rewrite_tac[] >>
            drule_all fdok0_first_call >> strip_tac >>
            qpat_x_assum ‘zinv _ _ _’ (strip_assume_tac o SIMP_RULE std_ss [zinv_def]) >>
            qpat_x_assum ‘w1 = w’ SUBST_ALL_TAC >>
            rpt (qpat_x_assum ‘MEM 0w (MAP FST _)’ mp_tac) >> asm_rewrite_tac[MAP, MEM]) >>
        ‘MEM 0w (l0_used w) ∧ ¬MEM 0w (MAP FST w.listeners) ∧ ¬MEM 0w (MAP FST w.open_fds)’
          by fs[zinv_def] >>
        rpt conj_tac
        >- (irule call_used_keep >> qexistsl_tac [‘bytes’, ‘unblock nm conf’, ‘nm’, ‘out’, ‘w’] >>
            simp[] >> rpt strip_tac >> gvs[unblock_def] >>
            qpat_x_assum ‘no_close0 G’ mp_tac >> rewrite_tac[no_close0_def] >>
            disch_then (qspecl_then [‘conf’, ‘ZIP (bytes, out)’] mp_tac) >> simp[])
        >- (qpat_x_assum ‘∀g. MEM g (MAP FST w1.listeners) ⇒ _’ (qspec_then ‘0w’ mp_tac) >>
            simp[])
        >- (simp[MEM_MAP] >> rpt strip_tac >> rename1 ‘MEM y w1.open_fds’ >>
            qpat_x_assum ‘∀x. MEM x w1.open_fds ⇒ _’ drule >> strip_tac >> gvs[MEM_MAP])) >>
  rewrite_tac[zinv_def, APPEND_eq_NIL, NOT_CONS_NIL] >> rpt strip_tac >>
  TRY (‘w1.open_fds = []’
         by (qpat_x_assum ‘no_conn G ⇒ w1.open_fds = []’ irule >> first_assum ACCEPT_TAC)) >>
  TRY (‘MEM 0w (l0_used w1) ∧ ¬MEM 0w (MAP FST w1.listeners) ∧ ¬MEM 0w (MAP FST w1.open_fds)’
         by (qpat_x_assum ‘fdok_first G ∧ no_close0 G ⇒ _’ irule >> conj_tac >>
             first_assum ACCEPT_TAC)) >>
  rpt (qpat_x_assum ‘MEM 0w (MAP FST _)’ mp_tac) >> asm_rewrite_tac[MAP, MEM]
QED

Theorem oinv_call:
  oinv w cs ∧ ¬MEM 0w (MAP FST w.open_fds) ∧ pinv evs w cs ∧ fds_lt w ∧ l0_rely w ∧
  l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
  oinv w1 (cs ++ X)
Proof
  strip_tac >> drule_all call_fields >> strip_tac >>
  ‘wmono w w1’ by metis_tac[wmono_call] >>
  rw[oinv_def] >> Cases_on ‘c < LENGTH w.chans’ >- (
    Cases_on ‘∃f. l0_chan_of w f = SOME c’
    >- (gvs[] >> ‘MEM (f, c) w.open_fds’
          by (gvs[l0_chan_of_def, AllCaseEqs()] >> metis_tac[ALOOKUP_MEM]) >>
        ‘f ≠ 0w’ by (strip_tac >> gvs[MEM_MAP] >> metis_tac[FST]) >>
        qpat_x_assum ‘pinv _ _ _’ mp_tac >> rewrite_tac[pinv_def] >> strip_tac >>
        first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
        metis_tac[EL_MEM]) >>
    gvs[oinv_def] >> metis_tac[]) >>
  fs[wmono_def]
QED

(*---------------------------------------------------------------------------*)
(* No episode on fd 0 *)

Theorem fdok_first_checked:
  fdok_first evs ⇒ fd0_checked evs
Proof
  rw[fdok_first_def, fd0_checked_def] >> Cases_on ‘pre’ >> gvs[ev_new_def] >> metis_tac[MEM]
QED

Theorem fd0_safe_no_ev0:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ∧
  (fdok_first (proc_events k rs) ∧ no_close0 (proc_events k rs) ∨ no_conn (proc_events k rs)) ⇒
  EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) (proc_events k rs)
Proof
  rpt strip_tac >> TRY (metis_tac[l0sys_no_fd0, fdok_first_checked] >> NO_TAC) >>
  (gvs[no_conn_def, EVERY_MEM] >> rpt strip_tac >>
      Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >> gvs[ev_new_def] >>
      rename1 ‘ExtCall n’ >> gvs[AllCaseEqs()] >> metis_tac[])
QED
