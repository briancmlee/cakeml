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
  honestL1EPRefine honestL1EPOut honestL1EPModel honestL1PFOut honestL1PFModel honestL1Model
  honestL1PFConnRun honestL1PFConn honestL1PFRound honestL1PFRefine honestL1Steps honestL0WorldProps honestL0Rely honestL0World honestL0 Marshalling
  l0sysEpisodes moonshotEpRenum
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

(* [R3] The channel numbering (moonshotEpRenum's cep_io): a transient
   connect starts no channel *)
Definition cep_next_def:
  cep_next (opn : (word64 # num) list, n : num) ev =
    case cev_new ev of
    | SOME (f, _) => ((if f = 0w then opn else (f, n) :: opn), n + 1)
    | NONE => (opn, n)
End

Theorem cep_io_append:
  ∀xs opn n.
    cep_io sel j opn n (xs ++ ys) =
    cep_io sel j opn n xs ++
    cep_io sel j (FST (FOLDL cep_next (opn, n) xs)) (SND (FOLDL cep_next (opn, n) xs)) ys
Proof
  Induct >> simp[cep_io_def] >> rpt gen_tac >> simp[cep_next_def] >>
  Cases_on ‘cev_new h’ >> simp[] >> PairCases_on ‘x’ >> simp[]
QED

Theorem cep_io_nonew:
  ∀evs opn n.
    EVERY (λev. cev_new ev = NONE) evs ⇒
    cep_io l0sysEpisodes$ev_sent j opn n evs = credit opn j evs ∧
    FOLDL cep_next (opn, n) evs = (opn, n)
Proof
  Induct >> simp[cep_io_def, credit_def, cep_next_def] >> rpt gen_tac >> strip_tac >>
  fs[credit_def]
QED

Theorem cep_io_nosend:
  ∀evs opn n.
    EVERY (λev. l0sysEpisodes$ev_sent ev = NONE) evs ⇒
    cep_io l0sysEpisodes$ev_sent j opn n evs = []
Proof
  Induct >> simp[cep_io_def] >> rpt gen_tac >> strip_tac >> every_case_tac >> fs[]
QED

(* Two maps that differ only on fds with nothing sent credit alike *)
Theorem credit_cong:
  ∀evs. (∀g. ALOOKUP o1 g ≠ ALOOKUP o2 g ⇒ evs_sent g evs = []) ⇒
        credit o1 j evs = credit o2 j evs
Proof
  Induct >- simp[credit_def] >> rpt gen_tac >> strip_tac >>
  ‘∀g. ALOOKUP o1 g ≠ ALOOKUP o2 g ⇒
       honestL1PFOut$ev_sent g h = [] ∧ evs_sent g evs = []’
    by (rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[]) >>
  ‘credit o1 j evs = credit o2 j evs’ by (first_x_assum irule >> metis_tac[]) >>
  fs[credit_def] >>
  CASE_TAC >> PairCases_on ‘x’ >> simp[] >>
  Cases_on ‘ALOOKUP o1 x0 = ALOOKUP o2 x0’ >> simp[] >>
  first_x_assum drule >> simp[ev_sent_l0sys] >> rw[]
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

Theorem cev_other:
  n ≠ «sys_connect» ⇒
  cev_new (IO_event (ExtCall n) conf bl) = ev_new (IO_event (ExtCall n) conf bl)
Proof
  simp[cev_new_def, tconn_def]
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

Theorem dec_err_val:
  LENGTH (x : word8 list) = 4 ∧ v < 2 ** 64 ⇒
  dec_res (n2w (err_code e) :: (n2w8 v ++ x)) = SOME (Fail e x) ∧
  l0sysEpisodes$res_val (n2w (err_code e) :: (n2w8 v ++ x)) = v
Proof
  strip_tac >> ‘0 < err_code e ∧ err_code e < 256’ by simp[err_code_range] >>
  ‘LENGTH (n2w8 v) = 8’ by simp[LENGTH_n2w8] >>
  simp[dec_res_def, l0sysEpisodesTheory.res_val_def, DROP_APPEND, TAKE_APPEND1,
       TAKE_LENGTH_ID_rwt] >>
  ‘n2w (err_code e) ≠ (0w : word8)’ by simp[n2w_11] >>
  ‘w82n (n2w8 v) = v’ by (irule w82n_n2w8 >> fs[]) >>
  simp[]
QED

(* What a connect returns: a new fd (not 0), or an error with a value *)
Theorem sys_connect_out:
  sys_connect p w = SOME (out, w', ev) ∧ l0_rely w ∧ fds_lt w ∧ MEM 0w (l0_used w) ⇒
  (∃v. out = enc_res (Ok v) ∧ v ≠ 0 ∧ v < 2 ** 64) ∨
  (∃e v x. out = n2w (err_code e) :: (n2w8 v ++ x) ∧ LENGTH x = 4 ∧ v < 2 ** 64)
Proof
  strip_tac >>
  ‘LENGTH out = 13’
    by (gvs[sys_connect_def, l0_do_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> simp[]) >>
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
  gvs[enc_err_val_def, LENGTH_n2w8] >>
  TRY (disj1_tac >> qexists_tac ‘w2n (lowest_fd tw)’ >> simp[] >> NO_TAC) >>
  disj2_tac >>
  MAP_FIRST (fn (e, v) => qexistsl_tac [e, v, ‘tw.ch.errno_of tw.hist’] >>
                          fs[l0_hdr_def] >> NO_TAC)
    [(‘e’, ‘0’), (‘e’, ‘w2n (lowest_fd tw)’), (‘E_INPROGRESS’, ‘w2n (lowest_fd tw)’),
     (‘E_MFILE’, ‘0’)]
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
  drule_all sys_connect_out >> strip_tac >>
  gvs[ev_other] >>
  ‘LENGTH (port_bytes p) = 2’ by simp[port_bytes_def] >>
  simp[ev_new_def, port_bytes_w22n, GSYM res_val_same]
  >- (‘dec_res (enc_res (Ok v)) = SOME (Ok v)’
        by (mp_tac (Q.INST [‘rest’ |-> ‘[]’] (Q.SPEC ‘Ok v’ (Q.GEN ‘r’ dec_enc_res))) >>
            simp[l0_res_ok_def]) >>
      ‘l0sysEpisodes$res_val (enc_res (Ok v)) = v’
        by simp[res_val_same, res_val_enc] >>
      simp[]) >>
  mp_tac (Q.SPECL [‘x’, ‘v’, ‘e’] (Q.GENL [‘x’, ‘v’, ‘e’] dec_err_val)) >>
  impl_tac >- fs[] >> strip_tac >> asm_rewrite_tac[] >> simp[] >> rw[]
QED

(* [R3] A connect is transient (tconn: no channel) exactly when L1 closes
   its socket at once *)
Theorem sys_connect_tconn:
  sys_connect p w = SOME (out, w', ev) ∧ l0_rely w ∧ fds_lt w ∧ MEM 0w (l0_used w) ∧
  p < 65536 ⇒
  (tconn ev ⇔ conn_transient out ∧ honestL1EPModel$res_val out ≠ 0)
Proof
  strip_tac >>
  ‘∃bl. ev = IO_event (ExtCall «sys_connect») (port_bytes p) bl ∧ MAP SND bl = out’
    by (gvs[sys_connect_def] >> drule_all l0_do_ev >> simp[]) >>
  drule_all sys_connect_out >> strip_tac >>
  ‘LENGTH (port_bytes p) = 2’ by simp[port_bytes_def] >>
  gvs[tconn_def, conn_transient_def, GSYM res_val_same]
  >- (‘dec_res (enc_res (Ok v)) = SOME (Ok v)’
        by (mp_tac (Q.INST [‘rest’ |-> ‘[]’] (Q.SPEC ‘Ok v’ (Q.GEN ‘r’ dec_enc_res))) >>
            simp[l0_res_ok_def]) >>
      simp[l0_res_of_def]) >>
  mp_tac (Q.SPECL [‘x’, ‘v’, ‘e’] (Q.GENL [‘x’, ‘v’, ‘e’] dec_err_val)) >>
  impl_tac >- fs[] >> strip_tac >> asm_rewrite_tac[] >> simp[l0_res_of_def] >>
  metis_tac[]
QED

(* An accept starts an episode exactly when it returned an fd (not 0) *)
Theorem sys_accept_new:
  sys_accept l w = SOME (out, w', ev) ∧ l0_rely w ∧ fds_lt w ∧ MEM 0w (l0_used w) ⇒
  l0sysEpisodes$ev_sent ev = NONE ∧
  ev_new ev = (case l0_res_of out of Ok v => SOME (n2w v, INR l) | Fail _ _ => NONE) ∧
  (∀v. l0_res_of out = Ok v ⇒ (n2w v : word64) ≠ 0w) ∧
  cev_new ev = ev_new ev ∧ ¬tconn ev
Proof
  strip_tac >>
  ‘∀v. l0_res_of out = Ok v ⇒ (n2w v : word64) ≠ 0w’
    by (rpt strip_tac >> drule_all sys_accept_fresh >>
        qpat_x_assum ‘n2w v = 0w’ SUBST1_TAC >> strip_tac >> fs[]) >>
  ‘∃bl. ev = IO_event (ExtCall «sys_accept») (fd_bytes l) bl ∧ MAP SND bl = out’
    by (gvs[sys_accept_def] >> drule_all l0_do_ev >> simp[]) >>
  gvs[ev_other] >>
  simp[cev_new_def, tconn_def] >>
  simp[ev_new_def, l0_res_of_def] >>
  every_case_tac >> fs[l0_res_of_def]
QED

(* ------------------------------------------------------------------------
   fd 0 stays open: L1 closes only fds it got from L0, which were free
   then, so not 0
   ------------------------------------------------------------------------ *)

(* The fds in L1's tables *)
Definition tfds_def:
  tfds (es : l1e) = MAP SND es.p.b.tbl ++ es.p.b.closing ++ es.p.acq ++ MAP SND es.ctbl
End

Definition fd0_ok_def:
  fd0_ok w es ⇔ MEM 0w (l0_used w) ∧ ¬MEM 0w (tfds es)
End

Theorem fds_lt_sub:
  fds_lt w ∧ (∀g. MEM g (l0_used w') ⇒ MEM g (l0_used w)) ∧ w'.fd_limit = w.fd_limit ⇒
  fds_lt w'
Proof
  rw[honestL0WorldPropsTheory.fds_lt_def] >> metis_tac[]
QED

Theorem edo_fd0:
  edo lfd pol (wl, es) a = SOME (r, (wl', es'), evs) ∧ l0_rely wl ∧ fds_lt wl ∧
  fd0_ok wl es ∧ noclose a ⇒
  l0_rely wl' ∧ fds_lt wl' ∧ fd0_ok wl' es'
Proof
  strip_tac >> Cases_on ‘a’ >> gvs[edo_def, AllCaseEqs(), noclose_def]
  >~ [‘pdo _ _ (Accept _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule pdo_accept_ostep >> strip_tac >>
      gvs[fd0_ok_def, tfds_def] >> Cases_on ‘es.p.acq’ >> gvs[])
  >>~- ([‘pdo _ _ (Read _ _) = _’],
      PairCases_on ‘z’ >> gvs[] >> qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >>
      simp[pdo_def, AllCaseEqs()] >> rw[] >> gvs[fd0_ok_def, tfds_def, set_inb_def] >>
      TRY (PairCases_on ‘z’ >> gvs[] >> drule_all l1_close_l0 >> strip_tac) >>
      rename1 ‘ALOOKUP es.p.b.tbl h = SOME f’ >>
      ‘MEM f (MAP SND es.p.b.tbl)’
        by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND]) >>
      ‘f ≠ 0w’ by (strip_tac >> gvs[]) >>
      gvs[MEM_FILTER] >>
      TRY (irule fds_lt_sub >> qexists_tac ‘wl’ >> simp[] >> NO_TAC) >>
      metis_tac[MEM_SND_ADELKEY_sub, fds_lt_sub])
  >~ [‘pdo _ _ (Write _ _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule pdo_write_held >> strip_tac >>
      qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >> strip_tac >>
      pairarg_tac >> gvs[] >> drule_all l1do_write_l0 >> strip_tac >>
      gvs[fd0_ok_def, tfds_def, honestL0WorldPropsTheory.fds_lt_def])
  >~ [‘l1_close _ _ = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule_all l1_close_l0 >> strip_tac >>
      rename1 ‘ALOOKUP es.ctbl h = SOME f’ >>
      ‘MEM f (MAP SND es.ctbl)’
        by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND]) >>
      ‘f ≠ 0w’ by (strip_tac >> gvs[fd0_ok_def, tfds_def]) >>
      gvs[fd0_ok_def, tfds_def, ec_del_def, MEM_FILTER] >>
      conj_tac >- (irule fds_lt_sub >> qexists_tac ‘wl’ >> simp[]) >>
      metis_tac[MEM_SND_ADELKEY_sub])
  >~ [‘sys_close _ _ = SOME z’]
  >- ((* a transient connect failure: its fresh fd closed at once *)
      PairCases_on ‘z’ >> gvs[] >>
      drule_all sys_connect_l0 >> strip_tac >>
      qpat_x_assum ‘_ ≠ 0 ⇒ _’
        (fn th => qpat_assum ‘_ ≠ 0’ (strip_assume_tac o MATCH_MP th)) >>
      drule_all sys_close_l0 >> strip_tac >>
      ‘n2w (honestL1EPModel$res_val out) ≠ (0w : word64)’
        by (strip_tac >>
            pop_assum (fn th => qpat_x_assum ‘¬MEM _ (l0_used wl)’
                                  (mp_tac o REWRITE_RULE [th])) >>
            qpat_x_assum ‘fd0_ok wl es’ mp_tac >> REWRITE_TAC [fd0_ok_def] >>
            rpt strip_tac >> res_tac) >>
      rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (irule fds_lt_sub >> qexists_tac ‘w'’ >> rpt conj_tac >> first_assum ACCEPT_TAC)
      >> qpat_x_assum ‘fd0_ok wl es’ mp_tac >> REWRITE_TAC [fd0_ok_def] >> strip_tac >>
      asm_rewrite_tac [] >>
      qpat_x_assum ‘∀g. g ≠ _ ∧ MEM g (l0_used w') ⇒ _’ (qspec_then ‘0w’ mp_tac) >>
      qpat_x_assum ‘∀g. MEM g (l0_used wl) ⇒ _’ (qspec_then ‘0w’ mp_tac) >>
      qpat_x_assum ‘n2w _ ≠ 0w’ mp_tac >>
      qpat_x_assum ‘MEM 0w (l0_used wl)’ mp_tac >> rpt (pop_assum kall_tac) >>
      metis_tac [])
  >> drule_all sys_connect_l0 >> strip_tac >> fs[fd0_ok_def, tfds_def] >>
  rpt strip_tac >> TRY (metis_tac[] >> NO_TAC) >> gvs[] >>
  ‘honestL1EPModel$res_val out < 18446744073709551616’
    by (drule_all sys_connect_out >> strip_tac >> gvs[] >>
        TRY (drule dec_err_val >> simp[res_val_same] >> NO_TAC) >>
        simp[res_val_enc]) >>
  gvs[LESS_MOD]
QED

Theorem eacts_fd0:
  ∀acts wl es rs evs wl' es'.
    eacts lfd pol (wl, es) acts = SOME (rs, evs, (wl', es')) ∧ l0_rely wl ∧ fds_lt wl ∧
    fd0_ok wl es ∧ EVERY noclose acts ⇒
    l0_rely wl' ∧ fds_lt wl' ∧ fd0_ok wl' es'
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> PairCases_on ‘ws1’ >> drule_all edo_fd0 >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem settle_fds_used:
  ∀fs w es w' es' evs.
    settle_fds fs (w, es) = SOME ((w', es'), evs) ∧ l0_rely w ⇒ l0_used w' = l0_used w
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >> rw[AllCaseEqs()] >>
  drule_all sys_connerr_l0 >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem etail_fd0:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧
  l0_rely w ∧ fds_lt w ∧ fd0_ok w es ⇒
  fd0_ok w' es'
Proof
  simp[etail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  ‘es'.p = (promote es5).p ∧ es'.ctbl = (promote es5).ctbl’
    by (qpat_x_assum ‘_ = es'’ (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_x_assum ‘FILTER _ hs = rdy’ kall_tac >> qpat_x_assum ‘_ = es'’ kall_tac >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of es.p.b) log ps3'’ >>
  drule_all l1_polls_l0 >> strip_tac >>
  drule_all l1_flush_l0 >> strip_tac >>
  ‘fds_lt w2’ by gvs[honestL0WorldPropsTheory.fds_lt_def] >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
  drule_all fetch_acq >> strip_tac >> drule_all pf_fetch_quiet >> strip_tac >>
  ‘ps3.b.tbl = ps3'.b.tbl ∧ ps3.b.closing = ps3'.b.closing ∧ ps3.acq = ps3'.acq’
    by simp[Abbr ‘ps3’, stall_out] >>
  drule_all l1_reap_l0 >> strip_tac >>
  drule_all settle_fds_used >> strip_tac >>
  drule_all settle_fds_quiet >> simp[] >> strip_tac >>
  gvs[fd0_ok_def, tfds_def] >>
  ‘¬MEM 0w (fconns log)’ by (strip_tac >> res_tac >> gvs[]) >>
  mp_tac (Q.INST [‘es’ |-> ‘es5’] promote_fields) >> strip_tac >>
  ‘∀f. MEM f (MAP SND (promote es5).ctbl) ⇒ MEM f (MAP SND es5.ctbl)’
    by (simp[promote_def, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  gvs[] >> rpt strip_tac >> res_tac >> gvs[MEM_FILTER]
QED

(* ------------------------------------------------------------------------
   A round's actions: episodes are its connects that got a socket, in
   order (rfds); sends are credited as by the map before the round, since
   a fd that got a new episode in the round is not live, so sends nothing
   ------------------------------------------------------------------------ *)

Theorem name_new:
  ev_name ev ≠ ExtCall «sys_connect» ∧ ev_name ev ≠ ExtCall «sys_accept» ⇒ ev_new ev = NONE
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event n _ _’ >> Cases_on ‘n’ >> simp[ev_name_def, ev_new_def]
QED

Theorem name_sent:
  ev_name ev ≠ ExtCall «sys_send» ⇒ l0sysEpisodes$ev_sent ev = NONE
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event n _ _’ >> Cases_on ‘n’ >>
  simp[ev_name_def, l0sysEpisodesTheory.ev_sent_def]
QED

Theorem edo_names:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ (∀p. a ≠ EConnect p) ∧ noclose a ⇒
  EVERY (λev. ev_name ev = ExtCall «sys_send» ∨ ev_name ev = ExtCall «sys_close») evs
Proof
  Cases_on ‘a’ >> simp[edo_def, AllCaseEqs(), noclose_def] >> rw[] >> TRY (PairCases_on ‘z’) >> gvs[] >>
  TRY (drule pdo_names >> simp[] >> NO_TAC) >>
  gvs[l1_close_def, AllCaseEqs(), sys_close_def] >> drule l0_do_cases >> rw[] >>
  simp[ev_name_def]
QED

Theorem name_cnew:
  ev_name ev ≠ ExtCall «sys_connect» ∧ ev_name ev ≠ ExtCall «sys_accept» ⇒ cev_new ev = NONE
Proof
  strip_tac >> irule cev_new_none >> irule name_new >> simp[]
QED

Theorem cnonew_names:
  EVERY (λev. ev_name ev = ExtCall «sys_send» ∨ ev_name ev = ExtCall «sys_close») evs ⇒
  EVERY (λev. cev_new ev = NONE) evs
Proof
  rw[EVERY_MEM] >> res_tac >> irule name_cnew >> simp[]
QED

Theorem nonew_names:
  EVERY (λev. ev_name ev = ExtCall «sys_send» ∨ ev_name ev = ExtCall «sys_close») evs ⇒
  EVERY (λev. ev_new ev = NONE) evs
Proof
  rw[EVERY_MEM] >> res_tac >> irule name_new >> simp[]
QED

Theorem edo_ep:
  edo lfd pol (w, es) a = SOME (r1, (w1, es1), evs1) ∧ oown lfd es ∧ eown lfd es1 ∧
  okeys es.p.b ∧ l0_rely w ∧ fds_lt w ∧ fd0_ok w es ∧ noclose a ∧
  (∀g. ALOOKUP opn g ≠ ALOOKUP cm g ⇒ ¬live es g) ⇒
  cep_io l0sysEpisodes$ev_sent j opn kk evs1 = credit cm j evs1 ∧
  FOLDL cep_next (opn, kk) evs1 = (cnew kk (rfds es1 [r1]) ++ opn, kk + LENGTH (rfds es1 [r1])) ∧
  (∀g. ALOOKUP (cnew kk (rfds es1 [r1]) ++ opn) g ≠ ALOOKUP cm g ⇒ ¬live es1 g)
Proof
  strip_tac >> drule_all edo_live >> strip_tac >>
  Cases_on ‘∃p. a = EConnect p’
  >- (gvs[] >> qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def, AllCaseEqs()] >>
      strip_tac >> gvs[] >>
      ‘MEM 0w (l0_used w) ∧ p < 65536’ by fs[fd0_ok_def] >>
      drule_all sys_connect_new >> strip_tac >>
      drule_all sys_connect_tconn >> strip_tac
      >~ [‘sys_close _ _ = SOME z’]
      >- ((* transient: no channel; the connect and the close send nothing *)
          PairCases_on ‘z’ >> rename1 ‘sys_close _ _ = SOME (_, _, cev)’ >>
          ‘cev_new ev = NONE’
            by (qpat_x_assum ‘tconn ev ⇔ _’ (fn th => REWRITE_TAC [cev_new_def, th]) >>
                asm_rewrite_tac []) >>
          ‘ev_name cev = ExtCall «sys_close»’
            by (qpat_x_assum ‘sys_close _ _ = _’ mp_tac >> simp[sys_close_def] >>
                strip_tac >> drule l0_do_cases >> rw[] >> simp[ev_name_def]) >>
          ‘cev_new cev = NONE ∧ l0sysEpisodes$ev_sent cev = NONE’
            by (conj_tac >> FIRST [irule name_cnew, irule name_sent] >> simp[]) >>
          qpat_x_assum ‘∀g. ALOOKUP opn g ≠ _ ⇒ _’ mp_tac >>
          qpat_x_assum ‘cev_new ev = NONE’ mp_tac >>
          qpat_x_assum ‘l0sysEpisodes$ev_sent ev = NONE’ mp_tac >>
          qpat_x_assum ‘cev_new cev = NONE’ mp_tac >>
          qpat_x_assum ‘l0sysEpisodes$ev_sent cev = NONE’ mp_tac >>
          qpat_x_assum ‘(r1, _, _) = _’ (mp_tac o SIMP_RULE std_ss []) >>
          rpt (pop_assum kall_tac) >>
          simp[rfds_def, conn_hdls_def, cnew_thm, cep_io_def, credit_def, cep_next_def]) >>
      ‘cev_new ev = ev_new ev’
        by (qpat_x_assum ‘tconn ev ⇔ _’ (fn th => REWRITE_TAC [cev_new_def, th]) >>
            asm_simp_tac std_ss []) >>
      Cases_on ‘honestL1EPModel$res_val out = 0’ >>
      gvs[rfds_def, conn_hdls_def, cnew_thm, cep_io_def, credit_def, cep_next_def] >>
      TRY (rpt strip_tac >> qpat_x_assum ‘∀g. ALOOKUP opn g ≠ _ ⇒ _’ irule >> fs[] >>
           NO_TAC) >>
      ‘honestL1EPModel$res_val out < 18446744073709551616’
        by (drule_all sys_connect_out >> strip_tac >> gvs[] >>
            TRY (drule dec_err_val >> simp[res_val_same] >> NO_TAC) >>
            simp[res_val_enc]) >>
      ‘(n2w (honestL1EPModel$res_val out) : word64) ≠ 0w’
        by (drule_all sys_connect_l0 >> rpt strip_tac >>
            qpat_x_assum ‘n2w _ = 0w’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
            fs[]) >>
      simp[LESS_MOD] >> gen_tac >> Cases_on ‘g = n2w (honestL1EPModel$res_val out)’
      >- (simp[] >> strip_tac >> drule eown_ctbl_unlive >> simp[]) >>
      simp[] >> strip_tac >>
      ‘¬live es g’ by (qpat_x_assum ‘∀g. ALOOKUP opn g ≠ _ ⇒ _’ irule >> fs[]) >>
      qpat_x_assum ‘∀f. (live es f ⇒ _) ∧ _’ (qspec_then ‘g’ mp_tac) >> simp[]) >>
  fs[] >>
  ‘EVERY (λev. cev_new ev = NONE) evs1’ by (irule cnonew_names >> metis_tac[edo_names]) >>
  qspecl_then [‘evs1’, ‘opn’, ‘kk’] mp_tac cep_io_nonew >> impl_tac >- simp[] >>
  strip_tac >> simp[] >>
  ‘conn_hdls [r1] = []’ by (drule edo_conn_hdls >> metis_tac[]) >>
  simp[rfds_def, cnew_thm] >>
  rpt conj_tac >> TRY (irule credit_cong >> metis_tac[] >> NO_TAC) >> metis_tac[]
QED

Theorem eacts_rfds_cons:
  edo lfd pol (wl, es) a = SOME (r1, (wl1, es1), evs1) ∧
  eacts lfd pol (wl1, es1) acts = SOME (rs1, evs2, (wl', es')) ∧ ciss lfd es1 ∧
  EVERY noclose acts ⇒
  rfds es' (r1 :: rs1) = rfds es1 [r1] ++ rfds es' rs1
Proof
  strip_tac >>
  ‘∀h. MEM h (conn_hdls [r1]) ⇒ ALOOKUP es'.ctbl h = ALOOKUP es1.ctbl h’
    by (rpt strip_tac >> drule_all edo_conn_pending >> strip_tac >>
        drule_all eacts_keeps_pending >> simp[]) >>
  simp[rfds_def] >>
  ‘conn_hdls (r1 :: rs1) = conn_hdls [r1] ++ conn_hdls rs1’ by metis_tac[conn_hdls_cons] >>
  pop_assum SUBST1_TAC >> simp[MAP_APPEND] >> irule MAP_CONG >> simp[]
QED

Theorem eacts_ep:
  ∀acts w es rs evs w' es' opn kk.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧
    (∀i rs0 evs0 wi esi.
       i ≤ LENGTH acts ∧ eacts lfd pol (w, es) (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒
       eown lfd esi) ∧
    okeys es.p.b ∧ l0_rely w ∧ fds_lt w ∧ fd0_ok w es ∧ EVERY noclose acts ∧
    (∀g. ALOOKUP opn g ≠ ALOOKUP cm g ⇒ ¬live es g) ⇒
    cep_io l0sysEpisodes$ev_sent j opn kk evs = credit cm j evs ∧
    FOLDL cep_next (opn, kk) evs = (cnew kk (rfds es' rs) ++ opn, kk + LENGTH (rfds es' rs)) ∧
    (∀g. ALOOKUP (cnew kk (rfds es' rs) ++ opn) g ≠ ALOOKUP cm g ⇒ ¬live es' g)
Proof
  Induct >- simp[eacts_def, rfds_def, conn_hdls_def, cnew_thm, cep_io_def] >>
  rpt gen_tac >> rename1 ‘a :: acts’ >> strip_tac >>
  qpat_x_assum ‘eacts _ _ _ _ = _’ mp_tac >> simp[Once eacts_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> rename1 ‘edo _ _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘edo _ _ _ _ = SOME (r1, (w1, es1), evs1)’ >> strip_tac >> gvs[] >>
  rename1 ‘eacts _ _ _ acts = SOME (rs1, evs2, (w', es'))’ >>
  ‘eown lfd es’
    by (qpat_x_assum ‘∀i rs0 evs0 wi esi. _’ (qspecl_then [‘0’, ‘[]’, ‘[]’, ‘w’, ‘es’] mp_tac) >>
        simp[eacts_def]) >>
  ‘eown lfd es1’
    by (qpat_x_assum ‘∀i rs0 evs0 wi esi. _’
          (qspecl_then [‘1’, ‘[r1]’, ‘evs1’, ‘w1’, ‘es1’] mp_tac) >>
        simp[eacts_def]) >>
  ‘oown lfd es’ by metis_tac[eown_oown] >>
  drule_all edo_ep >> strip_tac >>
  drule_all edo_live >> strip_tac >>
  drule_all edo_fd0 >> strip_tac >>
  first_x_assum (qspecl_then [‘w1’, ‘es1’, ‘rs1’, ‘evs2’, ‘w'’, ‘es'’,
                              ‘cnew kk (rfds es1 [r1]) ++ opn’,
                              ‘kk + LENGTH (rfds es1 [r1])’] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt conj_tac >>
      TRY (rpt strip_tac >>
           qpat_x_assum ‘∀i rs0 evs0 wi esi. _’
             (qspecl_then [‘SUC i’, ‘r1 :: rs0’, ‘evs1 ++ evs0’, ‘wi’, ‘esi’] mp_tac) >>
           fs[eacts_def] >> NO_TAC) >>
      metis_tac[]) >>
  strip_tac >>
  ‘ciss lfd es1’ by metis_tac[eown_ciss] >>
  drule_all eacts_rfds_cons >> strip_tac >>
  simp[cep_io_append, FOLDL_APPEND, cnew_append]
QED

(* ------------------------------------------------------------------------
   A round's tail: its sends (the flush) come before its new episodes (the
   fetch's accepts, numbered as arrs numbers the log's FConn)
   ------------------------------------------------------------------------ *)

Definition fc_next_def:
  fc_next (opn : (word64 # num) list, k : num) (FConn f) = ((f, k) :: opn, k + 1) ∧
  fc_next (opn, k) _ = (opn, k)
End

Theorem arrs_fold:
  ∀l cm k. SND (arrs lfd (cm, k) l) = FOLDL fc_next (cm, k) l
Proof
  Induct >> simp[arrs_def] >> Cases >> simp[arrs_def, fc_next_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> metis_tac[SND]
QED

Theorem credit_nosend:
  ∀evs. EVERY (λev. l0sysEpisodes$ev_sent ev = NONE) evs ⇒ credit opn j evs = []
Proof
  Induct >> simp[credit_def] >> rpt strip_tac >> fs[credit_def]
QED

Theorem names_quiet:
  EVERY (λev. ev_name ev = ExtCall n) evs ∧ n ≠ «sys_connect» ∧ n ≠ «sys_accept» ⇒
  EVERY (λev. cev_new ev = NONE) evs ∧
  (n ≠ «sys_send» ⇒ EVERY (λev. l0sysEpisodes$ev_sent ev = NONE) evs)
Proof
  rw[EVERY_MEM] >> res_tac >> TRY (irule name_cnew) >> TRY (irule name_sent) >> simp[]
QED

Theorem settle_fds_names:
  ∀fs w es w' es' evs.
    settle_fds fs (w, es) = SOME ((w', es'), evs) ⇒
    EVERY (λev. ev_name ev = ExtCall «sys_connerr») evs
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >> rw[AllCaseEqs()] >>
  first_x_assum drule >> simp[] >> gvs[sys_connerr_def] >>
  drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

(* The fetch: an accept that returned an fd is a new episode, its FConn *)
Theorem pf_fetch_ep:
  ∀fs w ps w' ps' log evs opn k.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ∧ fds_lt w ∧
    MEM 0w (l0_used w) ⇒
    FOLDL cep_next (opn, k) evs = FOLDL fc_next (opn, k) log ∧
    EVERY (λev. l0sysEpisodes$ev_sent ev = NONE) evs
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘pf_fetch _ _ (f :: fs)’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (qpat_x_assum ‘f = lfd’ SUBST_ALL_TAC >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
      PairCases_on ‘x’ >> rename1 ‘sys_accept _ _ = SOME (out, w1, ev)’ >> simp[] >>
      pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl1)’ >>
      Cases_on ‘pf_fetch lfd pol fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
      PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
      drule_all sys_accept_new >> strip_tac >>
      ‘l0_rely w1’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule_all l0_do_rely >> simp[]) >>
      ‘fds_lt w1’ by (drule_all sys_accept_fds_lt >> simp[]) >>
      ‘MEM 0w (l0_used w1)’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule l0_do_used >> simp[]) >>
      Cases_on ‘l0_res_of out’ >> gvs[cep_next_def, fc_next_def]
      >- (first_x_assum drule_all >> simp[])
      >> pop_assum mp_tac >> rw[] >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  Cases_on ‘sys_recv f pf_chunk w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘sys_recv _ _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl1)’ >>
  Cases_on ‘pf_fetch lfd pol fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
  PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
  ‘∃bl. ev = IO_event (ExtCall «sys_recv») (fd_bytes f) bl’
    by (gvs[sys_recv_def] >> drule_all l0_do_ev >> metis_tac[]) >>
  ‘l0_rely w1’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        drule_all l0_do_rely >> simp[]) >>
  ‘l0_used w1 = l0_used w ∧ w1.fd_limit = w.fd_limit’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        imp_res_tac l0_do_env >> drule l0_do_used >> simp[]) >>
  ‘fds_lt w1’ by gvs[honestL0WorldPropsTheory.fds_lt_def] >>
  ‘FOLDL fc_next (opn, k) fl1 = (opn, k)’
    by (qpat_x_assum ‘_ = (ps1, fl1)’ mp_tac >> rw[AllCaseEqs()] >> simp[fc_next_def]) >>
  gvs[ev_other, cev_other, cep_next_def, FOLDL_APPEND] >>
  ‘MEM 0w (l0_used w1)’ by fs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem etail_ep:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧ oown lfd es ∧
  okeys es.p.b ∧ l0_rely w ∧ fds_lt w ∧ fd0_ok w es ∧ pown lfd es'.p ∧
  (∀g. ALOOKUP opn g ≠ ALOOKUP cm g ⇒ ¬live es g) ⇒
  cep_io l0sysEpisodes$ev_sent j opn kk tevs = credit cm j tevs ∧
  FOLDL cep_next (opn, kk) tevs = SND (arrs lfd (opn, kk) log)
Proof
  strip_tac >> drule_all etail_live >> strip_tac >>
  qpat_x_assum ‘etail _ _ _ _ = _’ mp_tac >> simp[etail_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  drule l1_polls_names >> strip_tac >> drule l1_flush_names >> strip_tac >>
  drule pf_fetch_names >> strip_tac >> drule l1_reap_names >> strip_tac >>
  drule settle_fds_names >> strip_tac >>
  drule_all l1_polls_l0 >> strip_tac >> drule_all l1_flush_l0 >> strip_tac >>
  ‘fds_lt w2 ∧ MEM 0w (l0_used w2)’
    by gvs[honestL0WorldPropsTheory.fds_lt_def, fd0_ok_def] >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
  drule_all pf_fetch_ep >> disch_then (qspecl_then [‘opn’, ‘kk’] strip_assume_tac) >>
  ‘EVERY (λev. cev_new ev = NONE) (pevs ++ fevs) ∧
   EVERY (λev. cev_new ev = NONE) (cevs ++ sevs) ∧
   EVERY (λev. l0sysEpisodes$ev_sent ev = NONE) (gevs ++ cevs ++ sevs)’
    by (rpt (qpat_x_assum ‘EVERY (λev. ev_name ev = _) _’ mp_tac) >>
        simp[EVERY_MEM] >> rpt strip_tac >> res_tac >>
        TRY (irule name_cnew >> simp[] >> NO_TAC) >> irule name_sent >> simp[]) >>
  qpat_x_assum ‘_ = tevs’ (SUBST_ALL_TAC o SYM) >>
  fs[EVERY_APPEND] >>
  ‘∀o1 n1. cep_io l0sysEpisodes$ev_sent j o1 n1 pevs = credit o1 j pevs ∧
           FOLDL cep_next (o1, n1) pevs = (o1, n1)’ by metis_tac[cep_io_nonew] >>
  ‘∀o1 n1. cep_io l0sysEpisodes$ev_sent j o1 n1 fevs = credit o1 j fevs ∧
           FOLDL cep_next (o1, n1) fevs = (o1, n1)’ by metis_tac[cep_io_nonew] >>
  ‘∀o1 n1. cep_io l0sysEpisodes$ev_sent j o1 n1 cevs = [] ∧
           FOLDL cep_next (o1, n1) cevs = (o1, n1)’ by metis_tac[cep_io_nonew, cep_io_nosend] >>
  ‘∀o1 n1. cep_io l0sysEpisodes$ev_sent j o1 n1 sevs = [] ∧
           FOLDL cep_next (o1, n1) sevs = (o1, n1)’ by metis_tac[cep_io_nonew, cep_io_nosend] >>
  ‘∀o1 n1. cep_io l0sysEpisodes$ev_sent j o1 n1 gevs = []’ by metis_tac[cep_io_nosend] >>
  ‘credit cm j gevs = [] ∧ credit cm j cevs = [] ∧ credit cm j sevs = []’
    by metis_tac[credit_nosend] >>
  ‘credit opn j pevs = credit cm j pevs ∧ credit opn j fevs = credit cm j fevs’
    by (conj_tac >> irule credit_cong >> rpt strip_tac >>
        ‘¬live es g’ by (qpat_x_assum ‘∀g. ALOOKUP opn g ≠ _ ⇒ _’ irule >> simp[]) >>
        qpat_x_assum ‘∀f. (live es f ⇒ _) ∧ _’ (qspec_then ‘g’ strip_assume_tac) >> gvs[]) >>
  asm_rewrite_tac[cep_io_append, FOLDL_APPEND, credit_simps, APPEND_NIL] >>
  simp[arrs_fold] >> Cases_on ‘FOLDL fc_next (opn, kk) log’ >> asm_rewrite_tac[]
QED

(* ------------------------------------------------------------------------
   The run: the trace's episodes are E1's channels, round by round, and
   episode j's sent bytes are what ersent credits to channel j
   ------------------------------------------------------------------------ *)

Theorem einit_fd0:
  MEM 0w (l0_used w0) ⇒ fd0_ok w0 einit
Proof
  simp[fd0_ok_def, tfds_def, einit_def, pinit_def, l1init_def]
QED

Theorem l0_ep_sent_run:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧ MEM 0w (l0_used w0) ∧
  (∀hh. EVERY noclose (new_actions (log_of m) hh)) ∧
  (∀n. SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs.
    erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    FOLDL cep_next ([], 0) evs = ecm lfd pol ifds m w0 n ∧ fd0_ok (FST ws) (SND ws) ∧
    ∀j. cep_io l0sysEpisodes$ev_sent j [] 0 evs = ersent lfd pol ifds m w0 j n
Proof
  strip_tac >> Induct
  >- (simp[erounds_def, ecm_def, cep_io_def, ersent_def] >>
      metis_tac[einit_fd0]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum ‘erounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [erounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum ‘eround _ _ _ _ _ = _’ mp_tac >> simp[eround_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘eacts _ _ ws' _ = SOME (rs, aevs, ws1)’ >>
  PairCases_on ‘ws'’ >> PairCases_on ‘ws1’ >> PairCases_on ‘ws’ >> fs[] >>
  (* E1's invariants at rounds n and n + 1 *)
  mp_tac (Q.INST [‘N’ |-> ‘SUC n’] l1ep_refines_ehl_upto_sent) >> impl_tac >- fs[] >>
  disch_then (fn th =>
    qspecl_then [‘n’, ‘h'’, ‘(ws'0, ws'1)’, ‘evs'’, ‘logs'’] mp_tac th >>
    qspecl_then [‘SUC n’, ‘h' ++ [ssnap rdy rs]’, ‘(ws0, ws1)’, ‘evs' ++ (aevs ++ tevs ++ shevs)’,
                 ‘logs' ++ [log]’] mp_tac th) >>
  simp[] >> rpt (disch_then strip_assume_tac) >>
  ‘∃cm k. ecm lfd pol ifds m w0 n = (cm, k)’ by metis_tac[pairTheory.PAIR] >>
  ‘ALL_DISTINCT (MAP SND cm)’
    by (qpat_x_assum ‘ev_rel _ _ (FST (ecm _ _ _ _ _ n)) _ _’ mp_tac >> simp[ev_rel_def]) >>
  ‘okeys ws'1.p.b’
    by (qpat_x_assum ‘sent_inv (FST (ecm _ _ _ _ _ n)) _ _ _’ mp_tac >> simp[sent_inv_def]) >>
  ‘pown lfd ws1.p’ by fs[eown_def] >>
  ‘∀i rs0 evs0 wi esi.
     i ≤ LENGTH (new_actions (log_of m) h') ∧
     eacts lfd pol (ws'0, ws'1) (TAKE i (new_actions (log_of m) h')) =
     SOME (rs0, evs0, (wi, esi)) ⇒ eown lfd esi’
    by (qpat_x_assum ‘∀n'. n' < SUC n ⇒ eround_own _ _ _ _ _ _’ (qspec_then ‘n’ mp_tac) >>
        simp[eround_own_def] >> disch_then drule >> simp[]) >>
  ‘eown lfd ws11’
    by (first_x_assum (qspecl_then [‘LENGTH (new_actions (log_of m) h')’, ‘rs’, ‘aevs’,
                                    ‘ws10’, ‘ws11’] mp_tac) >> simp[TAKE_LENGTH_ID]) >>
  ‘EVERY noclose (new_actions (log_of m) h')’
    by (qpat_assum ‘∀hh. EVERY noclose _’ (qspec_then ‘h'’ ACCEPT_TAC)) >>
  (* no EShut in E1 (eown): the shutdown step is the identity *)
  PairCases_on ‘ws2’ >>
  ‘ws21.shq = []’
    by (qpat_x_assum ‘etail _ _ _ _ = _’ (mp_tac o MATCH_MP etail_shq) >>
        qpat_x_assum ‘eown lfd ws11’ mp_tac >> simp[eown_def]) >>
  qpat_x_assum ‘eshuts _ = _’ mp_tac >>
  qpat_x_assum ‘ws21.shq = []’ (fn th => simp[MATCH_MP eshuts_nil th]) >> strip_tac >>
  qpat_x_assum ‘ws20 = ws0’ SUBST_ALL_TAC >> qpat_x_assum ‘ws21 = ws1’ SUBST_ALL_TAC >>
  qpat_x_assum ‘shevs = []’ SUBST_ALL_TAC >> RULE_ASSUM_TAC (REWRITE_RULE [APPEND_NIL]) >>
  REWRITE_TAC [APPEND_NIL] >>
  qpat_x_assum ‘eacts _ _ _ _ = _’ assume_tac >>
  drule eacts_live >> impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt strip_tac >> irule eown_oown >> first_x_assum irule >>
      qexistsl_tac [‘evs0’, ‘i’, ‘rs0’, ‘wi’] >> fs[]) >>
  strip_tac >>
  drule_all eacts_fd0 >> strip_tac >>
  ‘∀j. cep_io l0sysEpisodes$ev_sent j cm k aevs = credit cm j aevs ∧
       FOLDL cep_next (cm, k) aevs =
       (cnew k (rfds ws11 rs) ++ cm, k + LENGTH (rfds ws11 rs)) ∧
       ∀g. ALOOKUP (cnew k (rfds ws11 rs) ++ cm) g ≠ ALOOKUP cm g ⇒ ¬live ws11 g’
    by (gen_tac >> qpat_x_assum ‘eacts _ _ (ws'0, ws'1) _ = _’ assume_tac >>
        drule eacts_ep >> disch_then (qspecl_then [‘j’, ‘cm’, ‘cm’, ‘k’] mp_tac) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >> simp[]) >>
  ‘∀j. cep_io l0sysEpisodes$ev_sent j (cnew k (rfds ws11 rs) ++ cm) (k + LENGTH (rfds ws11 rs))
         tevs = credit cm j tevs ∧
       FOLDL cep_next (cnew k (rfds ws11 rs) ++ cm, k + LENGTH (rfds ws11 rs)) tevs =
       SND (arrs lfd (cnew k (rfds ws11 rs) ++ cm, k + LENGTH (rfds ws11 rs)) log)’
    by (gen_tac >> qpat_x_assum ‘etail _ _ _ _ = _’ assume_tac >>
        drule etail_ep >>
        disch_then (qspecl_then [‘cnew k (rfds ws11 rs) ++ cm’, ‘k + LENGTH (rfds ws11 rs)’,
                                 ‘j’, ‘cm’] mp_tac) >>
        impl_tac
        >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            TRY (irule eown_oown >> first_assum ACCEPT_TAC >> NO_TAC) >>
            qpat_x_assum ‘∀j. _ ∧ _ ∧ ∀g. _’ (qspec_then ‘j’ strip_assume_tac) >>
            first_assum ACCEPT_TAC) >> simp[]) >>
  ‘eacts_of lfd pol ifds m w0 n = SOME (rs, aevs, (ws10, ws11))’ by simp[eacts_of_def] >>
  ‘econ lfd pol ifds m w0 n = rfds ws11 rs’ by simp[econ_def] >>
  ‘elog lfd pol ifds m w0 n = log’
    by (‘LENGTH logs' = n’
          by (qpat_x_assum ‘erounds _ _ _ _ _ n = _’ assume_tac >>
              drule erounds_logs >> simp[]) >>
        qpat_x_assum ‘erounds _ _ _ _ _ (SUC n) = _’ assume_tac >>
        drule elog_EL >> disch_then (qspec_then ‘n’ mp_tac) >> simp[EL_APPEND2]) >>
  rpt conj_tac
  >- (fs[FOLDL_APPEND, ecm_SUC, ecm1_def])
  >- (drule_all etail_fd0 >> simp[])
  >> gen_tac >>
  ‘FOLDL cep_next ([], 0) evs' = (cm, k)’ by fs[] >>
  simp[cep_io_append, ersent_def, FOLDL_APPEND] >>
  qpat_x_assum ‘FOLDL cep_next ([], 0) evs' = (cm, k)’ (fn th => simp[th]) >>
  qpat_x_assum ‘∀j. cep_io _ j cm k aevs = _ ∧ _’ (fn th => simp[th]) >>
  qpat_x_assum ‘∀j. cep_io _ j (cnew _ _ ++ cm) _ tevs = _ ∧ _’ (fn th => simp[th]) >>
  qpat_x_assum ‘∀j. cep_io _ j [] 0 evs' = _’ (fn th => simp[GSYM th]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  ‘credit cm j aevs ++ credit cm j tevs = credit cm j (aevs ++ tevs)’ by simp[] >>
  pop_assum SUBST1_TAC >> irule credit_ecred >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   [R3] Nothing is sent on a fd whose latest episode is a transient connect
   (nodead): that fd was fresh, and L1 closed it at once, so it is neither
   live nor in ctbl until a later episode gives it again (dead_ok)
   ------------------------------------------------------------------------ *)

Definition dead_ok_def:
  dead_ok (es : l1e) D ⇔ ∀f. MEM f D ⇒ ¬live es f ∧ ¬MEM f (MAP SND es.ctbl)
End

Theorem name_notconn:
  ev_name ev ≠ ExtCall «sys_connect» ⇒ ¬tconn ev
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event n _ _’ >> Cases_on ‘n’ >> simp[ev_name_def, tconn_def]
QED

Theorem dnext_nonew:
  ∀evs D. EVERY (λev. ev_new ev = NONE) evs ⇒ FOLDL dnext D evs = D
Proof
  Induct >> simp[dnext_def]
QED

Theorem dnext_sub:
  ∀evs D f. EVERY (λev. ¬tconn ev) evs ∧ MEM f (FOLDL dnext D evs) ⇒ MEM f D
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> simp[dnext_def] >> every_case_tac >> simp[MEM_FILTER]
QED

Theorem nodead_sends:
  ∀evs D. (∀f. MEM f D ⇒ evs_sent f evs = []) ∧ EVERY (λev. ¬tconn ev) evs ⇒
          nodead l0sysEpisodes$ev_sent D evs
Proof
  Induct >> simp[nodead_cons] >> rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[ev_sent_l0sys]) >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  ‘MEM f D’ by (qspecl_then [‘[h]’, ‘D’, ‘f’] mp_tac dnext_sub >> simp[]) >>
  first_x_assum drule >> simp[]
QED

Theorem edo_dead:
  edo lfd pol (w, es) a = SOME (r1, (w1, es1), evs1) ∧ oown lfd es ∧ okeys es.p.b ∧
  l0_rely w ∧ fds_lt w ∧ fd0_ok w es ∧ l0owne lfd w es ∧ noclose a ∧ dead_ok es D ⇒
  nodead l0sysEpisodes$ev_sent D evs1 ∧ dead_ok es1 (FOLDL dnext D evs1)
Proof
  strip_tac >> drule_all edo_live >> strip_tac >>
  Cases_on ‘∃p. a = EConnect p’
  >- (gvs[] >> qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def, AllCaseEqs()] >>
      strip_tac >> gvs[] >>
      ‘MEM 0w (l0_used w) ∧ p < 65536’ by fs[fd0_ok_def] >>
      drule_all sys_connect_new >> strip_tac >>
      drule_all sys_connect_tconn >> strip_tac >>
      drule_all sys_connect_l0 >> strip_tac
      >~ [‘sys_close _ _ = SOME z’]
      >- (PairCases_on ‘z’ >> rename1 ‘sys_close _ _ = SOME (_, _, cev)’ >>
          ‘ev_name cev = ExtCall «sys_close»’
            by (qpat_x_assum ‘sys_close _ _ = _’ mp_tac >> simp[sys_close_def] >>
                strip_tac >> drule l0_do_cases >> rw[] >> simp[ev_name_def]) >>
          ‘ev_new cev = NONE ∧ l0sysEpisodes$ev_sent cev = NONE’
            by (conj_tac >> FIRST [irule name_new, irule name_sent] >> simp[]) >>
          ‘tconn ev’ by (qpat_x_assum ‘tconn ev ⇔ _’ (fn th => REWRITE_TAC [th]) >>
                         conj_tac >> first_assum ACCEPT_TAC) >>
          ‘¬MEM (n2w (honestL1EPModel$res_val out)) (l0_used w)’
            by (qpat_x_assum ‘_ ≠ 0 ⇒ _’
                  (fn th => qpat_assum ‘_ ≠ 0’ (strip_assume_tac o MATCH_MP th))) >>
          qpat_x_assum ‘(r1, _, _) = _’ (strip_assume_tac o SIMP_RULE std_ss []) >>
          rpt BasicProvers.VAR_EQ_TAC >>
          simp[nodead_cons, dnext_def] >>
          qpat_x_assum ‘dead_ok es D’ mp_tac >> qpat_x_assum ‘l0owne lfd w es’ mp_tac >>
          qpat_x_assum ‘¬MEM _ (l0_used w)’ mp_tac >>
          rpt (pop_assum kall_tac) >>
          simp[dead_ok_def, l0owne_def, l0own_def, live_def, held_def] >> metis_tac[]) >>
      Cases_on ‘honestL1EPModel$res_val out = 0’ >>
      TRY (qpat_assum ‘honestL1EPModel$res_val out = 0’ mp_tac >>
           qpat_assum ‘honestL1EPModel$res_val out ≠ 0’ mp_tac >> simp_tac bool_ss [] >> NO_TAC) >>
      TRY (qpat_assum ‘honestL1EPModel$res_val out = 0’ kall_tac >>
           gvs[nodead_cons, dnext_def] >> NO_TAC) >>
      ‘¬tconn ev’ by (qpat_x_assum ‘tconn ev ⇔ _’ (fn th => REWRITE_TAC [th]) >>
                      simp[]) >>
      simp[nodead_cons] >> qpat_x_assum ‘ev_new ev = _’ (fn th => simp[dnext_def, th]) >>
      qpat_x_assum ‘¬tconn ev’ (fn th => simp[th]) >>
      qpat_x_assum ‘dead_ok es D’ mp_tac >>
      qpat_x_assum ‘∀f. (live es f ⇒ _) ∧ _’ mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[dead_ok_def, MEM_FILTER] >> metis_tac[]) >>
  fs[] >>
  ‘EVERY (λev. ev_new ev = NONE) evs1’ by (irule nonew_names >> metis_tac[edo_names]) >>
  ‘conn_hdls [r1] = []’ by (drule edo_conn_hdls >> metis_tac[]) >>
  drule edo_ctbl >> simp[rfds_def] >> strip_tac >>
  drule_all dnext_nonew >> disch_then (qspec_then ‘D’ SUBST1_TAC) >>
  conj_tac
  >- (irule nodead_sends >> conj_tac
      >- (rpt strip_tac >> qpat_x_assum ‘dead_ok es D’ mp_tac >> simp[dead_ok_def] >>
          disch_then drule >> strip_tac >>
          qpat_x_assum ‘∀f. (live es f ⇒ _) ∧ _’ (qspec_then ‘f’ mp_tac) >> simp[]) >>
      qpat_x_assum ‘EVERY _ evs1’ mp_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
      res_tac >> metis_tac[tconn_new, optionTheory.NOT_SOME_NONE]) >>
  qpat_x_assum ‘dead_ok es D’ mp_tac >>
  qpat_x_assum ‘∀f. (live es f ⇒ _) ∧ _’ mp_tac >>
  qpat_x_assum ‘∀f. MEM f (MAP SND es1.ctbl) ⇒ _’ mp_tac >>
  rpt (pop_assum kall_tac) >> simp[dead_ok_def] >> metis_tac[]
QED

Theorem eacts_dead:
  ∀acts w es rs evs w' es' D.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧
    (∀i rs0 evs0 wi esi.
       i ≤ LENGTH acts ∧ eacts lfd pol (w, es) (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒
       eown lfd esi) ∧
    okeys es.p.b ∧ l0_rely w ∧ fds_lt w ∧ fd0_ok w es ∧ l0owne lfd w es ∧
    EVERY noclose acts ∧ dead_ok es D ⇒
    nodead l0sysEpisodes$ev_sent D evs ∧ dead_ok es' (FOLDL dnext D evs)
Proof
  Induct >- simp[eacts_def] >>
  rpt gen_tac >> rename1 ‘a :: acts’ >> strip_tac >>
  qpat_x_assum ‘eacts _ _ _ _ = _’ mp_tac >> simp[Once eacts_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> rename1 ‘edo _ _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘edo _ _ _ _ = SOME (r1, (w1, es1), evs1)’ >> strip_tac >> gvs[] >>
  rename1 ‘eacts _ _ _ acts = SOME (rs1, evs2, (w', es'))’ >>
  ‘eown lfd es’
    by (qpat_x_assum ‘∀i rs0 evs0 wi esi. _’ (qspecl_then [‘0’, ‘[]’, ‘[]’, ‘w’, ‘es’] mp_tac) >>
        simp[eacts_def]) >>
  ‘oown lfd es’ by metis_tac[eown_oown] >>
  drule_all edo_dead >> strip_tac >>
  drule_all edo_live >> strip_tac >>
  drule_all edo_fd0 >> strip_tac >>
  drule_all edo_l0 >> strip_tac >>
  first_x_assum (qspecl_then [‘w1’, ‘es1’, ‘rs1’, ‘evs2’, ‘w'’, ‘es'’,
                              ‘FOLDL dnext D evs1’] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum ‘∀i rs0 evs0 wi esi. _’
        (qspecl_then [‘SUC i’, ‘r1 :: rs0’, ‘evs1 ++ evs0’, ‘wi’, ‘esi’] mp_tac) >>
      fs[eacts_def]) >>
  strip_tac >> simp[nodead_append, FOLDL_APPEND]
QED

(* The fetch: an accept that returned an fd starts a (non-transient)
   episode on it, its FConn *)
Theorem pf_fetch_dead:
  ∀fs w ps w' ps' log evs D.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ∧ fds_lt w ∧
    MEM 0w (l0_used w) ⇒
    (∀f. MEM f (FOLDL dnext D evs) ⇔ MEM f D ∧ ¬MEM (FConn f) log) ∧
    EVERY (λev. ¬tconn ev) evs
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘pf_fetch _ _ (f :: fs)’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (qpat_x_assum ‘f = lfd’ SUBST_ALL_TAC >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
      PairCases_on ‘x’ >> rename1 ‘sys_accept _ _ = SOME (out, w1, ev)’ >> simp[] >>
      pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl1)’ >>
      Cases_on ‘pf_fetch lfd pol fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
      PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
      drule_all sys_accept_new >> strip_tac >>
      ‘l0_rely w1’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule_all l0_do_rely >> simp[]) >>
      ‘fds_lt w1’ by (drule_all sys_accept_fds_lt >> simp[]) >>
      ‘MEM 0w (l0_used w1)’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule l0_do_used >> simp[]) >>
      Cases_on ‘l0_res_of out’ >> gvs[dnext_def]
      >- (first_x_assum drule_all >> strip_tac >> simp[MEM_FILTER] >> metis_tac[])
      >> pop_assum mp_tac >> rw[] >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  Cases_on ‘sys_recv f pf_chunk w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘sys_recv _ _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl1)’ >>
  Cases_on ‘pf_fetch lfd pol fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
  PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
  ‘∃bl. ev = IO_event (ExtCall «sys_recv») (fd_bytes f) bl’
    by (gvs[sys_recv_def] >> drule_all l0_do_ev >> metis_tac[]) >>
  ‘l0_rely w1’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        drule_all l0_do_rely >> simp[]) >>
  ‘l0_used w1 = l0_used w ∧ w1.fd_limit = w.fd_limit’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        imp_res_tac l0_do_env >> drule l0_do_used >> simp[]) >>
  ‘fds_lt w1’ by gvs[honestL0WorldPropsTheory.fds_lt_def] >>
  ‘∀g. ¬MEM (FConn g) fl1’
    by (qpat_x_assum ‘_ = (ps1, fl1)’ mp_tac >> rw[AllCaseEqs()] >> simp[]) >>
  gvs[ev_other, dnext_def, tconn_def] >>
  ‘MEM 0w (l0_used w1)’ by fs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem etail_dnext:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧
  l0_rely w ∧ fds_lt w ∧ fd0_ok w es ⇒
  (∀f. MEM f (FOLDL dnext D tevs) ⇔ MEM f D ∧ ¬MEM (FConn f) log) ∧
  EVERY (λev. ¬tconn ev) tevs
Proof
  simp[etail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  drule l1_polls_names >> strip_tac >> drule l1_flush_names >> strip_tac >>
  drule l1_reap_names >> strip_tac >> drule settle_fds_names >> strip_tac >>
  drule_all l1_polls_l0 >> strip_tac >> drule_all l1_flush_l0 >> strip_tac >>
  ‘fds_lt w2 ∧ MEM 0w (l0_used w2)’
    by gvs[honestL0WorldPropsTheory.fds_lt_def, fd0_ok_def] >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
  drule_all pf_fetch_dead >> disch_then (qspec_then ‘D’ strip_assume_tac) >>
  ‘EVERY (λev. ev_new ev = NONE ∧ ¬tconn ev) (pevs ++ fevs ++ cevs ++ sevs)’
    by (rpt (qpat_x_assum ‘EVERY (λev. ev_name ev = _) _’ mp_tac) >>
        simp[EVERY_MEM] >> rpt strip_tac >> res_tac >>
        FIRST [irule name_new >> simp[] >> NO_TAC,
               qspec_then ‘ev’ mp_tac (GEN_ALL name_notconn) >> simp[]]) >>
  qpat_x_assum ‘_ = tevs’ (SUBST_ALL_TAC o SYM) >>
  fs[EVERY_APPEND, EVERY_CONJ] >>
  ‘∀D. FOLDL dnext D pevs = D ∧ FOLDL dnext D fevs = D ∧
       FOLDL dnext D cevs = D ∧ FOLDL dnext D sevs = D’
    by metis_tac[dnext_nonew] >>
  asm_rewrite_tac [FOLDL_APPEND]
QED

Theorem etail_dead:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧ oown lfd es ∧
  okeys es.p.b ∧ l0_rely w ∧ fds_lt w ∧ fd0_ok w es ∧ pown lfd es'.p ∧ dead_ok es D ⇒
  nodead l0sysEpisodes$ev_sent D tevs ∧ dead_ok es' (FOLDL dnext D tevs)
Proof
  strip_tac >> drule_all etail_live >> strip_tac >>
  drule_all etail_dnext >> disch_then (qspec_then ‘D’ strip_assume_tac) >>
  conj_tac
  >- (irule nodead_sends >> simp[] >> rpt strip_tac >>
      qpat_x_assum ‘dead_ok es D’ mp_tac >> simp[dead_ok_def] >>
      disch_then drule >> strip_tac >>
      qpat_x_assum ‘∀f. ¬live es f ⇒ _’ drule >> simp[]) >>
  simp[dead_ok_def] >> gen_tac >> strip_tac >>
  qpat_x_assum ‘dead_ok es D’ mp_tac >> simp[dead_ok_def] >>
  disch_then drule >> strip_tac >> metis_tac[]
QED

(* Receives: only the fetch receives, and only on table fds, which are live;
   so nothing is received on a dead fd either *)

Theorem name_recvd:
  ev_name ev ≠ ExtCall «sys_recv» ⇒ ev_recvd ev = NONE
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event n _ _’ >> Cases_on ‘n’ >>
  simp[ev_name_def, ev_recvd_def]
QED
Theorem bytes_fd_fd_bytes[simp]:
  bytes_fd (fd_bytes f) = f ∧ LENGTH (fd_bytes f) = 8
Proof
  simp[ffiSpikeSocketFFITheory.bytes_fd_def, ffiSpikeSocketFFITheory.fd_bytes_def, LENGTH_n2w8] >>
  ‘w82n (fd_bytes f) = w2n f’ by simp[] >> fs[ffiSpikeSocketFFITheory.fd_bytes_def]
QED
Theorem sys_recv_recvd:
  sys_recv f n w = SOME (out, w1, ev) ∧ l0_rely w ⇒
  ev_new ev = NONE ∧
  ev_recvd ev = case l0_res_of out of
                | Ok k => SOME (f, TAKE k (DROP 13 out))
                | Fail _ _ => NONE
Proof
  strip_tac >>
  ‘∃bl. ev = IO_event (ExtCall «sys_recv») (fd_bytes f) bl ∧ MAP SND bl = out’
    by (gvs[sys_recv_def] >> drule_all l0_do_ev >> simp[]) >>
  simp[ev_other, ev_recvd_def, l0_res_of_def, l0_hdr_def] >>
  Cases_on ‘dec_res out’ >> simp[] >> CASE_TAC >> simp[]
QED
Theorem edo_norecv:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ noclose a ⇒
  EVERY (λev. ev_recvd ev = NONE) evs
Proof
  Cases_on ‘∃p. a = EConnect p’
  >- (gvs[] >> simp[edo_def, AllCaseEqs()] >> rw[] >> gvs[sys_connect_def] >>
      TRY (drule l0_do_cases >> rw[] >> simp[ev_recvd_def] >> NO_TAC) >>
      PairCases_on ‘z’ >> gvs[] >>
      ‘ev_name z2 = ExtCall «sys_close»’
        by (qpat_x_assum ‘sys_close _ _ = _’ mp_tac >> simp[sys_close_def] >>
            strip_tac >> drule l0_do_cases >> rw[] >> simp[ev_name_def]) >>
      conj_tac >- (drule l0_do_cases >> rw[] >> simp[ev_recvd_def]) >>
      irule name_recvd >> simp[]) >>
  strip_tac >> drule edo_names >> impl_tac >- (fs[] >> metis_tac[]) >>
  simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> irule name_recvd >> simp[]
QED
Theorem eacts_norecv:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧ EVERY noclose acts ⇒
    EVERY (λev. ev_recvd ev = NONE) evs
Proof
  Induct >> simp[eacts_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘edo _ _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >> gvs[] >>
  drule_all edo_norecv >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem nodead_none:
  ∀evs D. EVERY (λev. sel ev = NONE) evs ⇒ nodead sel D evs
Proof
  Induct >> simp[nodead_cons]
QED

Theorem pf_fetch_nodead_recv:
  ∀fs w ps w' ps' log evs D.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ∧ fds_lt w ∧
    MEM 0w (l0_used w) ∧ (∀f. MEM f fs ∧ f ≠ lfd ⇒ ¬MEM f D) ⇒
    nodead ev_recvd D evs
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘pf_fetch _ _ (f :: fs)’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  IF_CASES_TAC
  >- (qpat_x_assum ‘f = lfd’ SUBST_ALL_TAC >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
      PairCases_on ‘x’ >> rename1 ‘sys_accept _ _ = SOME (out, w1, ev)’ >> simp[] >>
      pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl1)’ >>
      Cases_on ‘pf_fetch lfd pol fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
      PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
      drule_all sys_accept_new >> strip_tac >>
      ‘ev_recvd ev = NONE’
        by (irule name_recvd >> gvs[sys_accept_def] >> drule l0_do_cases >> rw[] >>
            simp[ev_name_def]) >>
      ‘l0_rely w1’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule_all l0_do_rely >> simp[]) >>
      ‘fds_lt w1’ by (drule_all sys_accept_fds_lt >> simp[]) >>
      ‘MEM 0w (l0_used w1)’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule l0_do_used >> simp[]) >>
      simp[nodead_cons] >> first_x_assum irule >> simp[] >> conj_tac
      >- (rpt strip_tac >>
          ‘MEM f (D : word64 list)’
            by (qspecl_then [‘[ev]’, ‘D’, ‘f’] mp_tac dnext_sub >> simp[]) >>
          metis_tac[]) >>
      qexistsl_tac [‘y2’, ‘ps1’, ‘ps'’, ‘w1’, ‘w'’] >> simp[]) >>
  Cases_on ‘sys_recv f pf_chunk w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘sys_recv _ _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl1)’ >>
  Cases_on ‘pf_fetch lfd pol fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
  PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
  drule_all sys_recv_recvd >> strip_tac >>
  ‘l0_rely w1’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        drule_all l0_do_rely >> simp[]) >>
  ‘l0_used w1 = l0_used w ∧ w1.fd_limit = w.fd_limit’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        imp_res_tac l0_do_env >> drule l0_do_used >> simp[]) >>
  ‘fds_lt w1’ by gvs[honestL0WorldPropsTheory.fds_lt_def] >>
  ‘¬MEM f D’ by metis_tac[] >>
  simp[nodead_cons, dnext_def] >> conj_tac
  >- (Cases_on ‘l0_res_of out’ >> simp[] >> rpt strip_tac >> gvs[]) >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [‘y2’, ‘ps1’, ‘ps'’, ‘w1’, ‘w'’] >> simp[]
QED

Theorem etail_nodead_recv:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧
  l0_rely w ∧ fds_lt w ∧ fd0_ok w es ∧ dead_ok es D ⇒
  nodead ev_recvd D tevs
Proof
  simp[etail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  drule l1_polls_names >> strip_tac >> drule l1_flush_names >> strip_tac >>
  drule l1_reap_names >> strip_tac >> drule settle_fds_names >> strip_tac >>
  drule_all l1_polls_l0 >> strip_tac >> drule_all l1_flush_l0 >> strip_tac >>
  ‘fds_lt w2 ∧ MEM 0w (l0_used w2)’
    by gvs[honestL0WorldPropsTheory.fds_lt_def, fd0_ok_def] >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
  drule pf_fetch_nodead_recv >> disch_then (qspec_then ‘D’ mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[MEM_FILTER] >> rpt strip_tac >>
      qpat_x_assum ‘MEM f (in_fds _)’ (strip_assume_tac o REWRITE_RULE [in_fds_pend]) >>
      drule honestL1PFRefineTheory.in_fds_poll_set >> simp[] >> strip_tac >>
      qpat_x_assum ‘dead_ok es D’ (mp_tac o REWRITE_RULE [dead_ok_def]) >>
      disch_then (qspec_then ‘f’ mp_tac) >> simp[live_def, held_def]) >>
  strip_tac >>
  ‘EVERY (λev. ev_new ev = NONE ∧ ev_recvd ev = NONE) (pevs ++ fevs ++ cevs ++ sevs)’
    by (rpt (qpat_x_assum ‘EVERY (λev. ev_name ev = _) _’ mp_tac) >>
        simp[EVERY_MEM] >> rpt strip_tac >> res_tac >>
        FIRST [irule name_new >> simp[] >> NO_TAC, irule name_recvd >> simp[]]) >>
  qpat_x_assum ‘_ = tevs’ (SUBST_ALL_TAC o SYM) >>
  fs[EVERY_APPEND, EVERY_CONJ] >>
  ‘∀D. FOLDL dnext D pevs = D ∧ FOLDL dnext D fevs = D ∧
       FOLDL dnext D cevs = D ∧ FOLDL dnext D sevs = D’
    by metis_tac[dnext_nonew] >>
  asm_rewrite_tac [nodead_append, FOLDL_APPEND] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >> irule nodead_none >> first_assum ACCEPT_TAC
QED

Theorem e1_nodead:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧ MEM 0w (l0_used w0) ∧
  (∀hh. EVERY noclose (new_actions (log_of m) hh)) ∧
  (∀n. SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs.
    erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    nodead l0sysEpisodes$ev_sent [] evs ∧ nodead ev_recvd [] evs ∧
    dead_ok (SND ws) (FOLDL dnext [] evs) ∧ fd0_ok (FST ws) (SND ws)
Proof
  strip_tac >> Induct
  >- (simp[erounds_def, dead_ok_def] >> metis_tac[einit_fd0]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum ‘erounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [erounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum ‘eround _ _ _ _ _ = _’ mp_tac >> simp[eround_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘eacts _ _ ws' _ = SOME (rs, aevs, ws1)’ >>
  PairCases_on ‘ws'’ >> PairCases_on ‘ws1’ >> PairCases_on ‘ws’ >> fs[] >>
  mp_tac (Q.INST [‘N’ |-> ‘SUC n’] l1ep_refines_ehl_upto_sent) >> impl_tac >- fs[] >>
  disch_then (fn th =>
    qspecl_then [‘n’, ‘h'’, ‘(ws'0, ws'1)’, ‘evs'’, ‘logs'’] mp_tac th >>
    qspecl_then [‘SUC n’, ‘h' ++ [ssnap rdy rs]’, ‘(ws0, ws1)’, ‘evs' ++ (aevs ++ tevs ++ shevs)’,
                 ‘logs' ++ [log]’] mp_tac th) >>
  simp[] >> rpt (disch_then strip_assume_tac) >>
  ‘okeys ws'1.p.b’
    by (qpat_x_assum ‘sent_inv (FST (ecm _ _ _ _ _ n)) _ _ _’ mp_tac >> simp[sent_inv_def]) >>
  ‘pown lfd ws1.p’ by fs[eown_def] >>
  ‘∀i rs0 evs0 wi esi.
     i ≤ LENGTH (new_actions (log_of m) h') ∧
     eacts lfd pol (ws'0, ws'1) (TAKE i (new_actions (log_of m) h')) =
     SOME (rs0, evs0, (wi, esi)) ⇒ eown lfd esi’
    by (qpat_x_assum ‘∀n'. n' < SUC n ⇒ eround_own _ _ _ _ _ _’ (qspec_then ‘n’ mp_tac) >>
        simp[eround_own_def] >> disch_then drule >> simp[]) >>
  ‘eown lfd ws11’
    by (first_x_assum (qspecl_then [‘LENGTH (new_actions (log_of m) h')’, ‘rs’, ‘aevs’,
                                    ‘ws10’, ‘ws11’] mp_tac) >> simp[TAKE_LENGTH_ID]) >>
  ‘EVERY noclose (new_actions (log_of m) h')’
    by (qpat_assum ‘∀hh. EVERY noclose _’ (qspec_then ‘h'’ ACCEPT_TAC)) >>
  PairCases_on ‘ws2’ >>
  ‘ws21.shq = []’
    by (qpat_x_assum ‘etail _ _ _ _ = _’ (mp_tac o MATCH_MP etail_shq) >>
        qpat_x_assum ‘eown lfd ws11’ mp_tac >> simp[eown_def]) >>
  qpat_x_assum ‘eshuts _ = _’ mp_tac >>
  qpat_x_assum ‘ws21.shq = []’ (fn th => simp[MATCH_MP eshuts_nil th]) >> strip_tac >>
  qpat_x_assum ‘ws20 = ws0’ SUBST_ALL_TAC >> qpat_x_assum ‘ws21 = ws1’ SUBST_ALL_TAC >>
  qpat_x_assum ‘shevs = []’ SUBST_ALL_TAC >> RULE_ASSUM_TAC (REWRITE_RULE [APPEND_NIL]) >>
  REWRITE_TAC [APPEND_NIL] >>
  qpat_x_assum ‘eacts _ _ _ _ = _’ assume_tac >>
  drule eacts_live >> impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt strip_tac >> irule eown_oown >> first_x_assum irule >>
      qexistsl_tac [‘evs0’, ‘i’, ‘rs0’, ‘wi’] >> fs[]) >>
  strip_tac >>
  drule_all eacts_fd0 >> strip_tac >>
  qpat_x_assum ‘eacts _ _ _ _ = _’ assume_tac >>
  drule eacts_dead >>
  disch_then (qspec_then ‘FOLDL dnext [] evs'’ mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum ‘etail _ _ _ _ = _’ assume_tac >>
  drule etail_dead >>
  disch_then (qspec_then ‘FOLDL dnext (FOLDL dnext [] evs') aevs’ mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      irule eown_oown >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  ‘nodead ev_recvd (FOLDL dnext (FOLDL dnext [] evs') aevs) tevs’
    by (qpat_x_assum ‘etail _ _ _ _ = _’ assume_tac >>
        drule etail_nodead_recv >> disch_then irule >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ‘nodead ev_recvd (FOLDL dnext [] evs') aevs’
    by (irule nodead_none >>
        qpat_x_assum ‘eacts _ _ (ws'0, ws'1) _ = _’
          (fn th => irule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] eacts_norecv) th)) >>
        first_assum ACCEPT_TAC) >>
  rpt conj_tac
  >- simp[nodead_append, FOLDL_APPEND]
  >- simp[nodead_append, FOLDL_APPEND]
  >- simp[FOLDL_APPEND]
  >> drule_all etail_fd0 >> simp[]
QED

(* G1: on the trace of any E1 run (fd 0 open at the start), what episode j
   sent (l0sysEpisodes' l0_ep_sent) is nothing if j is a transient connect
   (tsig: no channel), and otherwise a prefix of what the endpoint layer's
   channel (tsig evs j) was sent, in the world built from the run *)
Theorem e1_l0_ep_sent:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧ MEM 0w (l0_used w0) ∧
  (∀hh. EVERY noclose (new_actions (log_of m) hh)) ∧
  (∀n. SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs j.
    erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    case tsig evs j of
    | NONE => l0_ep_sent j evs = []
    | SOME c =>
        l0_ep_sent j evs ≼
        (EL c (FST (ehst lfd (elv lfd pol ifds m w0) ifds m
                     (pew lfd a pol ifds m w0 calls) n)).chans).sent
Proof
  rpt strip_tac >>
  mp_tac e1_nodead >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then drule >> strip_tac >>
  qpat_x_assum ‘nodead l0sysEpisodes$ev_sent [] evs’ (mp_tac o MATCH_MP ep_io_renum) >>
  disch_then (qspec_then ‘j’ assume_tac) >>
  simp[l0_ep_sent_def] >> pop_assum SUBST1_TAC >>
  Cases_on ‘tsig evs j’ >> simp[] >> rename1 ‘tsig evs j = SOME c’ >>
  mp_tac l0_ep_sent_run >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then drule >> strip_tac >> simp[] >>
  mp_tac l1ep_sent >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then drule >> simp[]
QED
