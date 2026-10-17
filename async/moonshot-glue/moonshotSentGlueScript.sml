(*
  G1 (design/45 §3, moonshot step 12): on the trace of an E1 run, what
  l0sysEpisodes counts as episode j's sent bytes (l0_ep_sent) is what E1's
  ghost ersent credits to channel j; so, by l1ep_sent, a prefix of what the
  layer's channel j was sent.

  The episodes and the channels are numbered alike: both count, in trace
  order, the connects that made a socket and the accepts that returned an
  fd.  One hypothesis: fd 0 is open at the start (the startup contract
  l0sys's l0_fresh also has), so no connect or accept returns fd 0, whose
  episode l0sysEpisodes counts but gives no bytes.
*)
Theory moonshotSentGlue
Ancestors
  honestL1EPRefine honestL1EPOut honestL1EPModel honestL1PFOut honestL1Model
  honestL0World honestL0 l0sysEpisodes
Libs
  preamble

(* The two readings of a send event agree: honestL1PFOut's (the bytes taken
   on f) is l0sysEpisodes' (the fd and the bytes taken), on f *)
Theorem ev_sent_l0sys:
  honestL1PFOut$ev_sent f ev =
  case l0sysEpisodes$ev_sent ev of SOME (g, bs) => if g = f then bs else [] | NONE => []
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event n conf bl’ >> Cases_on ‘n’ >>
  simp[honestL1PFOutTheory.ev_sent_def, l0sysEpisodesTheory.ev_sent_def, taken_def,
       l0_res_of_def] >>
  rw[] >> every_case_tac >> gvs[] >>
  ‘DROP 8 conf = []’ by simp[DROP_NIL] >> simp[]
QED

(* ------------------------------------------------------------------------
   Episodes, event by event
   ------------------------------------------------------------------------ *)

(* The episode state after an event: the fds' latest episodes, the count *)
Definition ep_next_def:
  ep_next (opn : (word64 # num) list, n : num) ev =
    case ev_new ev of
    | SOME (f, _) => ((if f = 0w then opn else (f, n) :: opn), n + 1)
    | NONE => (opn, n)
End

Theorem ep_io_append:
  ∀xs opn n.
    ep_io sel j opn n (xs ++ ys) =
    ep_io sel j opn n xs ++
    ep_io sel j (FST (FOLDL ep_next (opn, n) xs)) (SND (FOLDL ep_next (opn, n) xs)) ys
Proof
  Induct >> simp[ep_io_def] >> rpt gen_tac >> simp[ep_next_def] >>
  Cases_on ‘ev_new h’ >> simp[] >> PairCases_on ‘x’ >> simp[]
QED

(* Episode j's sends among events, by a fixed episode map *)
Definition credit_def:
  credit opn j evs =
    FLAT (MAP (λev. case l0sysEpisodes$ev_sent ev of
                    | SOME (f, bs) => if ALOOKUP opn f = SOME j then bs else []
                    | NONE => []) evs)
End

Theorem credit_simps[simp]:
  credit opn j [] = [] ∧
  credit opn j (xs ++ ys) = credit opn j xs ++ credit opn j ys
Proof
  simp[credit_def]
QED

(* No new episodes: the map stays and the sends are credited by it *)
Theorem ep_io_nonew:
  ∀evs opn n.
    EVERY (λev. ev_new ev = NONE) evs ⇒
    ep_io l0sysEpisodes$ev_sent j opn n evs = credit opn j evs ∧
    FOLDL ep_next (opn, n) evs = (opn, n)
Proof
  Induct >> simp[ep_io_def, credit_def, ep_next_def] >> rpt gen_tac >> strip_tac >>
  fs[credit_def]
QED

(* No sends: nothing credited *)
Theorem ep_io_nosend:
  ∀evs opn n.
    EVERY (λev. l0sysEpisodes$ev_sent ev = NONE) evs ⇒
    ep_io l0sysEpisodes$ev_sent j opn n evs = []
Proof
  Induct >> simp[ep_io_def] >> rpt gen_tac >> strip_tac >> every_case_tac >> fs[]
QED

(* Two maps that differ only on fds with nothing sent credit alike *)
Theorem credit_cong:
  ∀evs. (∀g. ALOOKUP o1 g ≠ ALOOKUP o2 g ⇒ evs_sent g evs = []) ⇒
        credit o1 j evs = credit o2 j evs
Proof
  Induct >> simp[credit_def] >> rpt gen_tac >> strip_tac >>
  ‘∀g. ALOOKUP o1 g ≠ ALOOKUP o2 g ⇒
       honestL1PFOut$ev_sent g h = [] ∧ evs_sent g evs = []’
    by (rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac >- (CASE_TAC >> PairCases_on ‘x’ >> simp[] >>
               Cases_on ‘ALOOKUP o1 x0 = ALOOKUP o2 x0’ >> simp[] >>
               first_x_assum drule >> simp[ev_sent_l0sys] >> rw[]) >>
  fs[credit_def]
QED

(* With distinct episode numbers, episode j's credit is its fd's sends *)
Theorem credit_one:
  ∀evs. (∀g. ALOOKUP cm g = SOME j ⇔ g = f) ⇒ credit cm j evs = evs_sent f evs
Proof
  Induct >> simp[credit_def] >> rpt strip_tac >> fs[credit_def] >>
  simp[ev_sent_l0sys] >> CASE_TAC >> PairCases_on ‘x’ >> simp[] >> rw[] >> gvs[]
QED

Theorem credit_none:
  ∀evs. (∀g. ALOOKUP cm g ≠ SOME j) ⇒ credit cm j evs = []
Proof
  Induct >> simp[credit_def] >> rpt strip_tac >> fs[credit_def] >>
  CASE_TAC >> PairCases_on ‘x’ >> simp[]
QED

Theorem credit_ecred:
  ALL_DISTINCT (MAP SND cm) ⇒ credit cm j evs = ecred cm j evs
Proof
  strip_tac >> Cases_on ‘∃f. ALOOKUP cm f = SOME j’
  >- (fs[] >> drule_all ecred_eq >> simp[] >> disch_then kall_tac >>
      irule credit_one >> metis_tac[ALOOKUP_SND_inj]) >>
  fs[] >> simp[ecred_nil, credit_none]
QED

(* ------------------------------------------------------------------------
   Which of E1's calls start an episode, and which send
   ------------------------------------------------------------------------ *)

Theorem res_val_same:
  l0sysEpisodes$res_val = honestL1EPModel$res_val
Proof
  simp[FUN_EQ_THM, l0sysEpisodesTheory.res_val_def, honestL1EPModelTheory.res_val_def]
QED

Theorem ev_other:
  (n ≠ «sys_connect» ∧ n ≠ «sys_accept» ⇒ ev_new (IO_event (ExtCall n) conf bl) = NONE) ∧
  (n ≠ «sys_send» ⇒ l0sysEpisodes$ev_sent (IO_event (ExtCall n) conf bl) = NONE)
Proof
  simp[ev_new_def, l0sysEpisodesTheory.ev_sent_def]
QED

Theorem l0_do_ev:
  l0_do n conf alen w = SOME (out, w', ev) ∧ l0_rely w ⇒
  ∃bl. ev = IO_event (ExtCall n) conf bl ∧ MAP SND bl = out
Proof
  rw[l0_do_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> simp[MAP_ZIP]
QED

Theorem port_bytes_w22n:
  p < 65536 ⇒ w22n (port_bytes p) = p
Proof
  strip_tac >> ‘port_bytes p = n2w2 p’ by simp[port_bytes_def, n2w2_def] >>
  simp[w22n_n2w2]
QED

(* A connect starts an episode exactly when it got a socket, whose fd is
   its value field (not 0: fd 0 is open, and new fds are free ones) *)
Theorem sys_connect_new:
  sys_connect p w = SOME (out, w', ev) ∧ l0_rely w ∧ fds_lt w ∧ MEM 0w (l0_used w) ∧
  p < 65536 ⇒
  l0sysEpisodes$ev_sent ev = NONE ∧
  ev_new ev = if honestL1EPModel$res_val out = 0 then NONE
              else SOME (n2w (honestL1EPModel$res_val out), INL p)
Proof
  strip_tac >>
  ‘∃bl. ev = IO_event (ExtCall «sys_connect») (port_bytes p) bl ∧ MAP SND bl = out’
    by (gvs[sys_connect_def] >> drule_all l0_do_ev >> simp[]) >>
  gvs[ev_other, port_bytes_w22n] >>
  simp[ev_new_def, port_bytes_w22n, GSYM res_val_same] >>
  ‘LENGTH (port_bytes p) = 2’ by simp[port_bytes_def] >> simp[] >>
  qpat_x_assum ‘sys_connect _ _ = _’ mp_tac >>
  simp[sys_connect_def, l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >> strip_tac >>
  qabbrev_tac ‘tw = l0_tick «sys_connect» w’ >>
  ‘l0_used tw = l0_used w ∧ tw.fd_limit = w.fd_limit’ by simp[Abbr ‘tw’] >>
  ‘fds_lt tw’ by gvs[honestL0WorldPropsTheory.fds_lt_def] >>
  ‘w.fd_limit ≤ 2 ** 31’ by gvs[l0_rely_def] >>
  ‘¬MEM (lowest_fd tw) (l0_used tw)’ by (irule lowest_fd_fresh >> fs[]) >>
  ‘lowest_fd tw ≠ 0w’ by (strip_tac >> gvs[]) >>
  ‘w2n (lowest_fd tw) < 2 ** 64 ∧ w2n (lowest_fd tw) ≠ 0’
    by (assume_tac (w2n_lt |> INST_TYPE [alpha |-> “:64”]) >> fs[] >>
        strip_tac >> fs[]) >>
  gvs[l0_call_def, l0_connect_def, fail_def, l0_alloc_def, AllCaseEqs()] >>
  gvs[res_val_enc, GSYM res_val_same, l0sysEpisodesTheory.res_val_def,
      dec_enc_res, enc_err_val_def, dec_res_def, enc_res_def, l0_res_ok_def] >>
  cheat
QED

(* An accept starts an episode exactly when it returned an fd (not 0) *)
Theorem sys_accept_new:
  sys_accept l w = SOME (out, w', ev) ∧ l0_rely w ∧ fds_lt w ∧ MEM 0w (l0_used w) ⇒
  l0sysEpisodes$ev_sent ev = NONE ∧
  ev_new ev = (case l0_res_of out of Ok v => SOME (n2w v, INR l) | Fail _ _ => NONE) ∧
  ∀v. l0_res_of out = Ok v ⇒ n2w v ≠ 0w
Proof
  strip_tac >>
  ‘∃bl. ev = IO_event (ExtCall «sys_accept») (fd_bytes l) bl ∧ MAP SND bl = out’
    by (gvs[sys_accept_def] >> drule_all l0_do_ev >> simp[]) >>
  gvs[ev_other] >>
  simp[ev_new_def, l0_res_of_def] >>
  conj_tac >- (every_case_tac >> simp[]) >>
  rpt strip_tac >> drule_all sys_accept_fresh >> fs[]
QED
