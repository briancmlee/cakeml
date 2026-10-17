(*
  The moonshot's client (design/45 §2.5, step 10), as a computation on the
  endpoint handle layer, and its proof (client_hl_claim).

  N logical connections to address a.  Connection i:
   - CIdle: connect (unless the client has used cbound handles);
   - CPend hd: its connect is pending; when the layer reports hd ready
     (the settle report), read it: refused (ERefused): back to CIdle, to
     retry; otherwise up: CUp, with all of rqs i to send;
   - CUp hd rest: write rest (the world takes what it takes), and read hd
     whenever it is ready (the client is a sink); EOF: CDone (a break
     reads as an EOF: not retried, bytes may have been sent);
   - CDone.
  A connect with no socket (EConnected NONE): back to CIdle.  The client
  finishes when every connection is CDone.

  The computation is a fold over the history: each snapshot's results
  update the state (paired with the previous round's actions), and the
  state and the snapshot's ready handles give the next round's actions.
*)
Theory moonshotClient
Ancestors
  moonshotClientSpec endpointHLModel endpointWorld HttpSpec HttpSpecBodies
  asyncLevel1 asyncCore asyncHLModel socketV2FFI honestL1Steps
Libs
  preamble

Datatype:
  cconn = CIdle | CPend word64 | CUp word64 (word8 list) | CDone
End

Datatype:
  cst = <| cs : cconn list               (* connection i's state *)
         ; last : (num # eact) list       (* the last round's actions, with their connection *)
         ; nh : num                       (* handles received so far *)
         ; hlc : (word64 # num) list |>   (* each handle's connection *)
End

Definition cread_def:
  cread = 4096n
End

(* Connection c's round actions, with nh handles used and the ready
   handles rdy *)
Definition cact1_def:
  cact1 a nh c (rdy : word64 set) =
    case c of
    | CIdle => if nh < cbound then [EConnect a] else []
    | CPend hd => if hd ∈ rdy then [ERead hd cread] else []
    | CUp hd rest =>
        (if rest ≠ [] then [EWrite hd rest] else []) ++
        (if hd ∈ rdy then [ERead hd cread] else [])
    | CDone => []
End

(* Round actions from state st, with the ready handles rdy, each with its
   connection *)
Definition cacts_def:
  cacts a st (rdy : word64 set) =
    FLAT (GENLIST (λi. MAP (λx. (i, x)) (cact1 a st.nh (EL i st.cs) rdy)) (LENGTH st.cs))
End

(* One result r of action x, for a connection in state c with requests b *)
Definition cres_def:
  cres (b : word8 list) c x r =
    case (x, r) of
    | (EConnect _, EConnected NONE) => CIdle
    | (EConnect _, EConnected (SOME hd)) => CPend hd
    | (ERead _ _, ERefused) => CIdle
    | (ERead _ _, EGot (SOME [])) => CDone
    | (ERead hd _, EGot _) => (case c of CPend _ => CUp hd b | _ => c)
    | (EWrite _ _, EWrote k) => (case c of CUp hd rest => CUp hd (DROP k rest) | _ => c)
    | _ => c
End

Definition new_hd_def:
  new_hd (EConnected (SOME hd)) = SOME hd ∧
  new_hd _ = NONE
End

(* The results of the last round's actions, in order *)
Definition cupd_def:
  cupd rqs st [] rs = st ∧
  cupd rqs st _ [] = st ∧
  cupd rqs st ((i, x) :: xs) (r :: rs) =
    cupd rqs (st with <| cs := LUPDATE (cres (brequests (rqs i)) (EL i st.cs) x r) i st.cs;
                         nh := st.nh + (if new_hd r = NONE then 0 else 1);
                         hlc := (case new_hd r of SOME hd => [(hd, i)] | NONE => []) ++ st.hlc |>)
         xs rs
End

Definition cinit_def:
  cinit a N =
    let st = <| cs := REPLICATE N CIdle; last := []; nh := 0; hlc := [] |> in
      st with last := cacts a st ∅
End

Definition cstep_def:
  cstep a rqs st (s : (word64, eresp) snapshot) =
    let st1 = cupd rqs st st.last s.results in st1 with last := cacts a st1 s.ready
End

Definition cstate_def:
  cstate a N rqs h = FOLDL (cstep a rqs) (cinit a N) h
End

Definition call_done_def:
  call_done st ⇔ EVERY (λc. c = CDone) st.cs
End

(* The computation: every round's actions so far; finished when all done *)
Definition cprog_def:
  cprog a N rqs (h : (word64, eresp) snapshot list) =
    <| actions := FLAT (GENLIST (λk. MAP SND (cstate a N rqs (TAKE k h)).last) (SUC (LENGTH h)));
       result := if call_done (cstate a N rqs h) then SOME () else NONE |>
End

(* The interest: the open handles *)
Definition chd_def:
  chd (CPend hd) = [hd] ∧
  chd (CUp hd rest) = [hd] ∧
  chd _ = []
End

Definition cifds_def:
  cifds a N rqs h = FLAT (MAP chd (cstate a N rqs h).cs)
End

(* ------------------------------------------------------------------------
   The computation's rounds
   ------------------------------------------------------------------------ *)

Theorem cstate_SNOC:
  cstate a N rqs (h ++ [s]) = cstep a rqs (cstate a N rqs h) s
Proof
  simp[cstate_def, FOLDL_APPEND]
QED

Theorem cprog_actions_SNOC:
  (cprog a N rqs (h ++ [s])).actions =
  (cprog a N rqs h).actions ++ MAP SND (cstate a N rqs (h ++ [s])).last
Proof
  simp[cprog_def] >>
  ‘SUC (LENGTH h + 1) = SUC (SUC (LENGTH h))’ by simp[] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC [GENLIST] >>
  ‘GENLIST (λk. MAP SND (cstate a N rqs (TAKE k (h ++ [s]))).last) (LENGTH h) =
   GENLIST (λk. MAP SND (cstate a N rqs (TAKE k h)).last) (LENGTH h)’
    by (irule GENLIST_CONG >> rw[] >> simp[TAKE_APPEND1]) >>
  pop_assum SUBST1_TAC >>
  simp[SNOC_APPEND, FLAT_APPEND, TAKE_LENGTH_ID_rwt, TAKE_APPEND1]
QED

(* The round polled with h emits the state's last actions *)
Theorem cprog_new_actions:
  new_actions (log_of (cprog a N rqs)) h = MAP SND (cstate a N rqs h).last
Proof
  Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_def, log_of_def, cprog_def, cstate_def] >>
  simp[new_actions_def, log_of_def, SNOC_APPEND, FRONT_APPEND, cprog_actions_SNOC] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

(* ------------------------------------------------------------------------
   The handle layer's operations on an open handle
   ------------------------------------------------------------------------ *)

(* w' is w but for channel j (and maybe the open fds) *)
Definition wframe_def:
  wframe j (w : eworld) w' ⇔
    LENGTH w'.chans = LENGTH w.chans ∧ (∀j'. j' ≠ j ⇒ EL j' w'.chans = EL j' w.chans) ∧
    w'.listening = w.listening ∧ w'.reserved = w.reserved ∧ w'.alloc = w.alloc ∧
    w'.takes = w.takes ∧ w'.env = w.env ∧ w'.clock = w.clock ∧ w'.hist = w.hist ∧
    w'.nosock = w.nosock ∧ w'.nconnects = w.nconnects ∧ w'.calls = w.calls
End

Theorem ehdo_read:
  ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧
  0 < n ∧ n < 256 ** 8 ⇒
  ∃r w' hs'. ehdo lfd v (w, hs) (ERead hd n) = SOME (r, (w', hs')) ∧ wframe j w w' ∧
   ((EL j w.chans).status = Refused ∧ r = ERefused ∧ hs' = eh_del hd hs ∧
    w'.open_fds = ADELKEY f w.open_fds ∧ (EL j w'.chans).status = Failed ∨
    (EL j w.chans).status ≠ Refused ∧ (EL j w.chans).inbox ≠ [] ∧
    r = EGot (SOME (TAKE n (EL j w.chans).inbox)) ∧ hs' = hs ∧ w'.open_fds = w.open_fds ∧
    EL j w'.chans = EL j w.chans with inbox := DROP n (EL j w.chans).inbox ∨
    (EL j w.chans).status ≠ Refused ∧ (EL j w.chans).inbox = [] ∧
    ((EL j w.chans).peer_eof ∨ (EL j w.chans).status = Failed) ∧
    r = EGot (SOME []) ∧ hs' = eh_del hd hs ∧ w'.open_fds = ADELKEY f w.open_fds ∧
    (EL j w'.chans).status = (EL j w.chans).status ∨
    (EL j w.chans).status ≠ Refused ∧ (EL j w.chans).inbox = [] ∧
    ¬(EL j w.chans).peer_eof ∧ (EL j w.chans).status ≠ Failed ∧
    r = EGot NONE ∧ hs' = hs ∧ w' = w)
Proof
  strip_tac >>
  simp[ehdo_def, ep_conn_err_def, ep_read_def, ep_chan_of_def, ep_close_def, upd_chan_def] >>
  rw[] >>
  TRY (‘∃t ts. TAKE n (EL j w.chans).inbox = t :: ts’
         by (Cases_on ‘(EL j w.chans).inbox’ >> gvs[] >> Cases_on ‘n’ >> gvs[]) >>
       pop_assum (fn th => simp[th] >> assume_tac th)) >>
  simp[wframe_def, EL_LUPDATE] >> rw[] >> gvs[ALOOKUP_ADELKEY]
QED

Theorem ehdo_write_up:
  ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧
  (EL j w.chans).status = Up ∧ ¬(EL j w.chans).shut ∧ w.takes = (λj b n. n) ⇒
  ehdo lfd v (w, hs) (EWrite hd bs) =
    SOME (EWrote (LENGTH bs),
          (upd_chan j (λc. c with <| sent := c.sent ++ bs; inflight := c.inflight + LENGTH bs |>) w,
           hs))
Proof
  strip_tac >> simp[ehdo_def, chan_status_def, ep_chan_of_def, ep_send_def]
QED

Theorem ehdo_connect:
  ehdo lfd v (w, hs) (EConnect a) =
    if w.nosock w.nconnects ∨ ¬(LENGTH (ep_used w) < dimword (:64)) then
      SOME (EConnected NONE, (w with nconnects := w.nconnects + 1, hs))
    else if hdln (w2n lfd) hs.nxt < dimword (:64) then
      SOME (EConnected (SOME (hdl lfd hs.nxt)),
            (w with <| chans := w.chans ++ [new_chan (SOME a) Connecting];
                       open_fds := (w.alloc (LENGTH w.chans) (ep_used w), LENGTH w.chans) :: w.open_fds;
                       nconnects := w.nconnects + 1 |>,
             eh_new lfd (w.alloc (LENGTH w.chans) (ep_used w)) hs with
               settling := hdl lfd hs.nxt :: hs.settling))
    else NONE
Proof
  simp[ehdo_def, ep_connect_def, ep_alloc_def] >>
  ‘∀X n. ep_used (w with <| chans := X; nconnects := n |>) = ep_used w’ by simp[ep_used_def] >>
  rw[] >> gvs[]
QED

(* ------------------------------------------------------------------------
   The history's pairs, round by round
   ------------------------------------------------------------------------ *)

Theorem hl_pairs_SNOC:
  hl_pairs m (h ++ [s]) = hl_pairs m h ++ ZIP (new_actions (log_of m) h, s.results)
Proof
  simp[hl_pairs_def] >>
  ‘LENGTH h + 1 = SUC (LENGTH h)’ by simp[] >> pop_assum SUBST1_TAC >>
  REWRITE_TAC [GENLIST] >>
  ‘GENLIST (λk. ZIP (new_actions (log_of m) (TAKE k (h ++ [s])), (EL k (h ++ [s])).results))
           (LENGTH h) =
   GENLIST (λk. ZIP (new_actions (log_of m) (TAKE k h), (EL k h).results)) (LENGTH h)’
    by (irule GENLIST_CONG >> rw[] >> simp[TAKE_APPEND1, EL_APPEND1]) >>
  pop_assum SUBST1_TAC >>
  simp[SNOC_APPEND, FLAT_APPEND, TAKE_LENGTH_APPEND, EL_APPEND2]
QED

Theorem hl_APPEND[simp]:
  hl_sent hd (ps1 ++ ps2) = hl_sent hd ps1 ++ hl_sent hd ps2 ∧
  hl_read hd (ps1 ++ ps2) = hl_read hd ps1 ++ hl_read hd ps2 ∧
  hl_connects (ps1 ++ ps2) = hl_connects ps1 ++ hl_connects ps2 ∧
  hl_conn_handles (ps1 ++ ps2) = hl_conn_handles ps1 ++ hl_conn_handles ps2 ∧
  (hl_eof hd (ps1 ++ ps2) ⇔ hl_eof hd ps1 ∨ hl_eof hd ps2) ∧
  (hl_refused hd (ps1 ++ ps2) ⇔ hl_refused hd ps1 ∨ hl_refused hd ps2)
Proof
  simp[hl_sent_def, hl_read_def, hl_connects_def, hl_conn_handles_def, hl_eof_def,
       hl_refused_def] >> metis_tac[]
QED

Theorem hl_NIL[simp]:
  hl_sent hd [] = [] ∧ hl_read hd [] = [] ∧ hl_connects [] = [] ∧
  hl_conn_handles [] = [] ∧ ¬hl_eof hd [] ∧ ¬hl_refused hd []
Proof
  simp[hl_sent_def, hl_read_def, hl_connects_def, hl_conn_handles_def, hl_eof_def,
       hl_refused_def]
QED

(* ------------------------------------------------------------------------
   The client's state and the layer's: the relation
   ------------------------------------------------------------------------ *)

(* Connection i in state c, its channel ch; sett: its connect is unreported
   (settling); rd: reported ready, to be read this round; sent: the bytes
   the history says it wrote *)
Definition cok_def:
  cok (b : word8 list) c (ch : chan) sett rd sent ⇔
    case c of
    | CPend hd =>
        ch.sent = [] ∧ sent = [] ∧ ¬ch.shut ∧
        (ch.status = Connecting ∧ ch.inbox = [] ∧ ¬ch.peer_eof ∧ sett ∧ ¬rd ∨
         (ch.status = Up ∨ ch.status = Refused) ∧ (sett ∨ rd))
    | CUp hd rest => ch.status = Up ∧ ¬ch.shut ∧ ch.sent ++ rest = b ∧ sent = ch.sent
    | _ => T
End

(* rdyf i: the ready handles connection i's next actions see *)
Definition crel_def:
  crel a N rqs lfd st (rdyf : num -> word64 set) ps (w : eworld) hs ⇔
    LENGTH st.cs = N ∧ st.nh = hs.nxt ∧
    w.takes = (λj b n. n) ∧ alloc_ok w.alloc ∧
    LENGTH w.reserved + LENGTH w.listening ≤ 1 ∧
    ALL_DISTINCT (MAP FST hs.tbl) ∧ ALL_DISTINCT (MAP SND hs.tbl) ∧
    ALL_DISTINCT (MAP FST w.open_fds) ∧ ALL_DISTINCT (MAP SND w.open_fds) ∧
    EVERY (λj. j < LENGTH w.chans) (MAP SND w.open_fds) ∧
    (∀f. MEM f (MAP FST w.open_fds) ⇒ ¬MEM f (MAP FST w.listening)) ∧
    (∀f. MEM f (MAP FST w.open_fds) ⇔ MEM f (MAP SND hs.tbl)) ∧
    (* the open handles: the connections', one each *)
    (∀hd. MEM hd (MAP FST hs.tbl) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i st.cs))) ∧
    (∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 st.cs)) ∧ MEM hd (chd (EL i2 st.cs)) ⇒
                i1 = i2) ∧
    (∀i hd. i < N ∧ MEM hd (chd (EL i st.cs)) ⇒
            ∃f j. ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧
                  ALOOKUP st.hlc hd = SOME i ∧
                  cok (brequests (rqs i)) (EL i st.cs) (EL j w.chans) (MEM hd hs.settling)
                      (hd ∈ rdyf i) (hl_sent hd ps)) ∧
    (* every handle issued is a connect handle of the history, below nxt *)
    (∀hd. MEM hd (MAP FST st.hlc) ⇔ MEM hd (hl_conn_handles ps)) ∧
    ALL_DISTINCT (MAP FST st.hlc) ∧
    (∀hd. MEM hd (MAP FST st.hlc) ⇒ ∃k. k < hs.nxt ∧ hd = hdl lfd k) ∧
    LENGTH st.hlc = hs.nxt ∧
    (* what was sent, per handle *)
    (∀hd. hl_sent hd ps ≠ [] ⇒ MEM hd (MAP FST st.hlc)) ∧
    (∀hd i. ALOOKUP st.hlc hd = SOME i ⇒ i < N ∧ hl_sent hd ps ≼ brequests (rqs i)) ∧
    (∀hd hd' i. ALOOKUP st.hlc hd = SOME i ∧ ALOOKUP st.hlc hd' = SOME i ∧
                hl_sent hd ps ≠ [] ∧ hl_sent hd' ps ≠ [] ⇒ hd = hd') ∧
    (∀i hd'. i < N ∧ (EL i st.cs = CIdle ∨ ∃hd. EL i st.cs = CPend hd) ∧
             ALOOKUP st.hlc hd' = SOME i ⇒ hl_sent hd' ps = []) ∧
    (∀i hd rest hd'. i < N ∧ EL i st.cs = CUp hd rest ∧ ALOOKUP st.hlc hd' = SOME i ∧
                     hl_sent hd' ps ≠ [] ⇒ hd' = hd) ∧
    (* a refused or ended handle is closed for good *)
    (∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ MEM hd (MAP FST st.hlc)) ∧
    (∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ ¬MEM hd (MAP FST hs.tbl)) ∧
    (∀hd. ¬(hl_refused hd ps ∧ hl_eof hd ps)) ∧
    (∀hd. (hl_refused hd ps ∨ hl_eof hd ps) ⇒ ∀i. i < N ⇒ ¬MEM hd (chd (EL i st.cs))) ∧
    (* a connection that read an EOF is done *)
    (∀hd i. hl_eof hd ps ∧ ALOOKUP st.hlc hd = SOME i ⇒ EL i st.cs = CDone)
End

(* ------------------------------------------------------------------------
   One connection's actions keep the relation
   ------------------------------------------------------------------------ *)

(* What an action leaves of the world *)
Definition wkeep_def:
  wkeep (w : eworld) w' ⇔
    w'.listening = w.listening ∧ w'.reserved = w.reserved ∧ w'.alloc = w.alloc ∧
    w'.takes = w.takes ∧ w'.env = w.env ∧ w'.clock = w.clock ∧ w'.hist = w.hist ∧
    w'.nosock = w.nosock ∧ w'.calls = w.calls ∧ LENGTH w.chans ≤ LENGTH w'.chans ∧
    ∀j. j < LENGTH w.chans ⇒ (EL j w'.chans).status = (EL j w.chans).status ∨
                             (EL j w.chans).status = Refused ∧ (EL j w'.chans).status = Failed
End

Theorem wkeep_refl[simp]:
  wkeep w w
Proof
  simp[wkeep_def]
QED

Theorem cupd_one[simp]:
  cupd rqs st [(k, x)] [r] =
    st with <| cs := LUPDATE (cres (brequests (rqs k)) (EL k st.cs) x r) k st.cs;
               nh := st.nh + (if new_hd r = NONE then 0 else 1);
               hlc := (case new_hd r of SOME hd => [(hd, k)] | NONE => []) ++ st.hlc |>
Proof
  simp[cupd_def]
QED

Theorem chd_LUPDATE:
  i < LENGTH cs ⇒ (MEM hd (chd (EL i (LUPDATE c k cs))) ⇔
                   if i = k then MEM hd (chd c) else MEM hd (chd (EL i cs)))
Proof
  rw[EL_LUPDATE]
QED

Theorem hl_one[simp]:
  hl_sent hd [(x, r)] =
    (case (x, r) of (EWrite h' bs, EWrote k) => if h' = hd then TAKE k bs else [] | _ => []) ∧
  hl_read hd [(x, r)] =
    (case (x, r) of (ERead h' n, EGot (SOME d)) => if h' = hd then d else [] | _ => []) ∧
  hl_conn_handles [(x, r)] =
    (case x of EConnect p => (case r of EConnected (SOME h') => [h'] | _ => []) | _ => []) ∧
  (hl_eof hd [(x, r)] ⇔ ∃n. x = ERead hd n ∧ r = EGot (SOME [])) ∧
  (hl_refused hd [(x, r)] ⇔ ∃n. x = ERead hd n ∧ r = ERefused)
Proof
  simp[hl_sent_def, hl_read_def, hl_conn_handles_def, hl_connects_def, hl_eof_def,
       hl_refused_def] >>
  Cases_on ‘x’ >> Cases_on ‘r’ >> simp[] >> TRY (rename1 ‘EConnected oh’ >> Cases_on ‘oh’) >>
  simp[] >> metis_tac[]
QED

(* The ready sets matter only for the open handles *)
Theorem crel_rdyf:
  crel a N rqs lfd st rdyf ps w hs ∧
  (∀i hd. i < N ∧ MEM hd (chd (EL i st.cs)) ⇒ (hd ∈ rdyf' i ⇔ hd ∈ rdyf i)) ⇒
  crel a N rqs lfd st rdyf' ps w hs
Proof
  simp[crel_def] >> rpt strip_tac >> fs[] >> TRY (metis_tac[] >> NO_TAC) >>
  qpat_x_assum ‘∀i hd. i < N ∧ MEM hd _ ⇒ ∃f j. _’ drule_all >> strip_tac >>
  qexistsl_tac [‘f’, ‘j’] >> simp[] >>
  qpat_x_assum ‘∀i hd. i < N ∧ MEM hd _ ⇒ (_ ⇔ _)’ drule_all >> simp[]
QED

(* A connect that got no socket changes nothing the relation sees *)
Theorem crel_nosock:
  crel a N rqs lfd st rdyf ps w hs ⇒
  crel a N rqs lfd st rdyf (ps ++ [(EConnect p, EConnected NONE)]) (w with nconnects := n) hs
Proof
  simp[crel_def] >> rpt strip_tac >> fs[] >> metis_tac[]
QED

Theorem crel_connect:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ EL k st.cs = CIdle ∧
  hs.nxt + 2 < dimword (:64) ∧ N < dimword (:64) ⇒
  ∃r w1 hs1. ehdo lfd v (w, hs) (EConnect a) = SOME (r, (w1, hs1)) ∧
     crel a N rqs lfd (cupd rqs st [(k, EConnect a)] [r]) ((k =+ ∅) rdyf) (ps ++ [(EConnect a, r)])
       w1 hs1 ∧
     wkeep w w1
Proof
  strip_tac >> ‘LENGTH st.cs = N’ by fs[crel_def] >> simp[ehdo_connect] >>
  IF_CASES_TAC
  >- (simp[cres_def, new_hd_def] >>
      ‘LUPDATE CIdle k st.cs = st.cs’
        by (qpat_x_assum ‘EL k st.cs = CIdle’ (SUBST1_TAC o SYM) >> irule LUPDATE_SAME >> simp[]) >>
      simp[wkeep_def] >>
      ‘st with <| cs := st.cs; nh := st.nh; hlc := st.hlc |> = st’
        by simp[theorem "cst_component_equality"] >>
      simp[] >> irule crel_rdyf >> qexists_tac ‘rdyf’ >>
      conj_tac >> TRY (irule crel_nosock >> first_assum ACCEPT_TAC >> NO_TAC) >>
      rw[combinTheory.APPLY_UPDATE_THM] >> gvs[chd_def]) >>
  ‘hdln (w2n lfd) hs.nxt < 18446744073709551616’
    by (‘hdln (w2n lfd) hs.nxt ≤ hs.nxt + 1’ by rw[hdln_def] >> fs[]) >>
  ‘hdln (w2n lfd) hs.nxt < dimword (:64)’ by simp[] >>
  qpat_assum ‘hdln _ _ < 18446744073709551616’
    (fn th => simp[th, cres_def, new_hd_def, eh_new_def]) >>
  qabbrev_tac ‘f = w.alloc (LENGTH w.chans) (ep_used w)’ >>
  qabbrev_tac ‘hd = hdl lfd hs.nxt’ >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  ‘¬MEM f (ep_used w)’ by (fs[alloc_ok_def, Abbr ‘f’]) >>
  ‘¬MEM f (MAP FST w.open_fds) ∧ ¬MEM f (MAP FST w.listening)’ by fs[ep_used_def] >>
  ‘¬MEM f (MAP SND hs.tbl)’
    by (qpat_x_assum ‘∀f. MEM f (MAP FST w.open_fds) ⇔ _’ (qspec_then ‘f’ mp_tac) >> simp[]) >>
  ‘∀k'. k' < hs.nxt ⇒ hdl lfd k' ≠ hd’
    by (rw[Abbr ‘hd’] >> irule hdl_fresh >> simp[]) >>
  ‘¬MEM hd (MAP FST st.hlc)’
    by (strip_tac >> qpat_x_assum ‘∀hd. MEM hd (MAP FST st.hlc) ⇒ ∃k. _’ drule >>
        strip_tac >> qpat_x_assum ‘∀k'. k' < hs.nxt ⇒ _’ drule >> simp[]) >>
  ‘∀i. i < N ⇒ ¬MEM hd (chd (EL i st.cs))’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ _’ drule_all >> strip_tac >>
        imp_res_tac ALOOKUP_MEM >>
        ‘MEM hd (MAP FST st.hlc)’
          by (qpat_x_assum ‘ALOOKUP st.hlc hd = SOME i’ mp_tac >> rpt (pop_assum kall_tac) >>
              rw[] >> imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >> metis_tac[FST]) >>
        qpat_x_assum ‘¬MEM hd (MAP FST st.hlc)’ mp_tac >>
        pop_assum (fn th => REWRITE_TAC [th])) >>
  ‘¬MEM hd (MAP FST hs.tbl)’
    by (qpat_x_assum ‘∀hd. MEM hd (MAP FST hs.tbl) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
        qpat_x_assum ‘∀i. i < N ⇒ ¬MEM hd _’ mp_tac >> rpt (pop_assum kall_tac) >>
        metis_tac[]) >>
  reverse conj_tac
  >- (simp[wkeep_def, EL_APPEND1]) >>
  ‘hl_sent hd ps = []’
    by (CCONTR_TAC >> qpat_x_assum ‘∀hd. hl_sent hd ps ≠ [] ⇒ _’ drule >>
        qpat_x_assum ‘¬MEM hd (MAP FST st.hlc)’ mp_tac >> simp[]) >>
  ‘¬hl_refused hd ps ∧ ¬hl_eof hd ps’
    by (conj_tac >> strip_tac >>
        qpat_x_assum ‘∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ MEM hd (MAP FST st.hlc)’
          (qspec_then ‘hd’ mp_tac) >>
        qpat_x_assum ‘¬MEM hd (MAP FST st.hlc)’ mp_tac >> simp[]) >>
  ‘∀x. hl_refused x ps ∨ hl_eof x ps ⇒ x ≠ hd’
    by (rpt strip_tac >> qpat_x_assum ‘x = hd’ SUBST_ALL_TAC >> fs[]) >>
  simp[crel_def] >> rpt conj_tac >> TRY (simp[] >> NO_TAC)
  (* 1 the new channel's index is new *)
  >- (strip_tac >>
      qpat_x_assum ‘EVERY _ (MAP SND w.open_fds)’ (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
      disch_then drule >> simp[])
  (* 2 *)
  >- (qpat_x_assum ‘EVERY _ (MAP SND w.open_fds)’ mp_tac >> simp[EVERY_MEM] >>
      rpt strip_tac >> first_x_assum drule >> simp[])
  (* 2b no listener's fd *)
  >- (rpt strip_tac >> gvs[] >> res_tac)
  (* 3 the open handles *)
  >- (gen_tac >> simp[EL_LUPDATE] >> eq_tac
      >- (strip_tac
          >- (qexists_tac ‘k’ >> simp[chd_def]) >>
          qexists_tac ‘i’ >> Cases_on ‘i = k’ >> gvs[chd_def]) >>
      strip_tac >> Cases_on ‘i = k’ >> gvs[chd_def] >> disj2_tac >>
      qexists_tac ‘i’ >> simp[])
  (* 4 one owner *)
  >- (rpt gen_tac >> simp[EL_LUPDATE] >> rw[] >> gvs[chd_def] >>
      TRY (qpat_x_assum ‘∀i. i < N ⇒ ¬MEM hd _’ drule >> simp[] >> NO_TAC) >>
      qpat_x_assum ‘∀i1 i2 hd. _ ⇒ i1 = i2’ irule >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexists_tac ‘hd'’ >>
      conj_tac >> first_assum ACCEPT_TAC)
  (* 5 each connection's handle *)
  >- (rpt gen_tac >> strip_tac >> Cases_on ‘i = k’
      >- (gvs[EL_LUPDATE, chd_def] >>
          simp[cok_def, EL_LENGTH_APPEND, new_chan_def, combinTheory.APPLY_UPDATE_THM]) >>
      gvs[EL_LUPDATE, combinTheory.APPLY_UPDATE_THM] >>
      ‘hd' ≠ hd’ by (strip_tac >> gvs[] >> qpat_x_assum ‘∀i. i < N ⇒ ¬MEM hd _’ drule >> simp[]) >>
      qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
      ‘f' ≠ f’ by (strip_tac >> gvs[] >> imp_res_tac ALOOKUP_MEM >>
                   qpat_x_assum ‘¬MEM f (MAP SND hs.tbl)’ mp_tac >> simp[MEM_MAP, EXISTS_PROD] >>
                   metis_tac[]) >>
      ‘j < LENGTH w.chans’ by (imp_res_tac ALOOKUP_MEM >>
                               qpat_x_assum ‘EVERY _ (MAP SND w.open_fds)’ mp_tac >>
                               simp[EVERY_MEM, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
      simp[EL_APPEND1])
  (* 6 *)
  >- (gen_tac >> eq_tac >> rw[] >> simp[])
  (* 7 issued below nxt *)
  >- (rw[] >- (qexists_tac ‘hs.nxt’ >> simp[]) >>
      qpat_x_assum ‘∀hd. MEM hd (MAP FST st.hlc) ⇒ ∃k. _’ (qspec_then ‘hd'’ mp_tac) >>
      simp[] >> strip_tac >> qexists_tac ‘k'’ >> simp[])
  (* 8 prefixes *)
  >- (rpt gen_tac >> IF_CASES_TAC >> rw[] >> gvs[] >>
      qpat_x_assum ‘∀hd i. ALOOKUP st.hlc hd = SOME i ⇒ _’ drule >> simp[])
  (* 9 one sending handle per connection *)
  >- (rpt gen_tac >> rw[] >> gvs[] >>
      qpat_x_assum ‘∀hd hd' i. _ ⇒ hd = hd'’ irule >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexists_tac ‘i’ >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  (* 10 idle or pending: nothing sent *)
  >- (rpt gen_tac >> simp[EL_LUPDATE] >> rw[] >> gvs[] >>
      qpat_x_assum ‘∀i hd'. i < N ∧ (_ ∨ _) ∧ _ ⇒ _’ irule >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexists_tac ‘i’ >> simp[])
  (* 11 up: only its handle sent *)
  >- (rpt gen_tac >> simp[EL_LUPDATE] >> rw[] >> gvs[] >>
      qpat_x_assum ‘∀i hd rest hd'. _ ⇒ hd' = hd’ irule >> simp[] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexistsl_tac [‘i’, ‘rest’] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  (* 12 refused or ended: a connect handle *)
  >- (gen_tac >> disch_tac >> disj2_tac >>
      qpat_x_assum ‘∀hd. MEM hd (MAP FST st.hlc) ⇔ _’ (fn th => REWRITE_TAC [GSYM th]) >>
      qpat_x_assum ‘∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ MEM hd (MAP FST st.hlc)’ irule >>
      first_assum ACCEPT_TAC)
  (* 13 refused or ended: not open *)
  >- (gen_tac >> disch_tac >> conj_tac
      >- (qpat_x_assum ‘∀x. _ ⇒ x ≠ hd’ irule >> first_assum ACCEPT_TAC) >>
      gen_tac >> Cases_on ‘i < N’ >> simp[] >>
      qpat_x_assum ‘∀hd. _ ⇒ ∀i. i < N ⇒ ¬MEM hd _’ drule >> disch_then drule >> simp[])
  (* 14 *)
  >- (gen_tac >> qpat_x_assum ‘∀hd. ¬(hl_refused hd ps ∧ hl_eof hd ps)’ (qspec_then ‘hd'’ mp_tac) >>
      simp[])
  (* 15 refused or ended: no connection's *)
  >- (gen_tac >> disch_tac >> gen_tac >> strip_tac >> simp[EL_LUPDATE] >> IF_CASES_TAC
      >- (simp[chd_def] >> qpat_x_assum ‘∀x. _ ⇒ x ≠ hd’ irule >> first_assum ACCEPT_TAC) >>
      qpat_x_assum ‘∀hd. _ ⇒ ∀i. i < N ⇒ ¬MEM hd _’ drule >> disch_then drule >> simp[])
  (* 16 ended: done *)
  >> rpt gen_tac >> strip_tac >> Cases_on ‘hd' = hd’ >> gvs[] >>
  qpat_x_assum ‘∀hd i. hl_eof hd ps ∧ _ ⇒ _’ drule_all >> rw[EL_LUPDATE] >> gvs[]
QED

(* ------------------------------------------------------------------------
   Closing a connection's handle (refused, or EOF) keeps the relation
   ------------------------------------------------------------------------ *)

Theorem MAP_FST_ADELKEY:
  MAP FST (ADELKEY k l) = FILTER (λx. x ≠ k) (MAP FST l)
Proof
  simp[ADELKEY_def, FILTER_MAP, combinTheory.o_DEF]
QED

Theorem ALL_DISTINCT_MAP_FILTER:
  ∀l. ALL_DISTINCT (MAP f l) ⇒ ALL_DISTINCT (MAP f (FILTER P l))
Proof
  Induct >> rw[] >> gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem MEM_SND_ADELKEY:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ ALL_DISTINCT (MAP FST l) ∧ ALOOKUP l k = SOME v ⇒
      (MEM x (MAP SND (ADELKEY k l)) ⇔ MEM x (MAP SND l) ∧ x ≠ v)
Proof
  Induct >> simp[FORALL_PROD] >> rpt gen_tac >> rename1 ‘(k0, v0) :: l’ >> strip_tac >>
  simp[ADELKEY_def] >> Cases_on ‘k0 = k’ >> gvs[]
  >- (‘FILTER (λp. FST p ≠ k) l = l’
        by (simp[FILTER_EQ_ID, EVERY_MEM] >> gvs[MEM_MAP] >> metis_tac[FST]) >>
      simp[] >> metis_tac[]) >>
  ‘MEM v (MAP SND l)’ by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND]) >>
  ‘v0 ≠ v’ by metis_tac[] >>
  gvs[ADELKEY_def] >> metis_tac[]
QED

Theorem ALL_DISTINCT_ADELKEY:
  ALL_DISTINCT (MAP f l) ⇒ ALL_DISTINCT (MAP f (ADELKEY k l))
Proof
  simp[ADELKEY_def, ALL_DISTINCT_MAP_FILTER]
QED

Theorem ALOOKUP_SND_inj:
  ∀l a b v. ALL_DISTINCT (MAP SND l) ∧ ALOOKUP l a = SOME v ∧ ALOOKUP l b = SOME v ⇒ a = b
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> metis_tac[SND]
QED

(* Frame facts for one connection's state change (LUPDATE c' k) *)
Theorem lupd_owner:
  (∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 cs)) ∧ MEM hd (chd (EL i2 cs)) ⇒ i1 = i2) ∧
  LENGTH cs = N ∧ k < N ∧
  (∀hd. MEM hd (chd c') ⇒ MEM hd (chd (EL k cs))) ⇒
  Abbrev (
  ∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 (LUPDATE c' k cs))) ∧
             MEM hd (chd (EL i2 (LUPDATE c' k cs))) ⇒ i1 = i2)
Proof
  simp[markerTheory.Abbrev_def] >>
  rw[EL_LUPDATE] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem lupd_tbl_close:
  (∀hd. MEM hd (MAP FST tbl) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i cs))) ∧
  (∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 cs)) ∧ MEM hd (chd (EL i2 cs)) ⇒ i1 = i2) ∧
  LENGTH cs = N ∧ k < N ∧ chd (EL k cs) = [hd0] ∧ chd c' = [] ⇒
  Abbrev (
  ∀hd. MEM hd (MAP FST (ADELKEY hd0 tbl)) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i (LUPDATE c' k cs))))
Proof
  simp[markerTheory.Abbrev_def] >>
  rw[MAP_FST_ADELKEY, MEM_FILTER, EL_LUPDATE] >> eq_tac >> rw[]
  >- (qexists_tac ‘i’ >> rw[] >> gvs[]) >>
  Cases_on ‘i = k’ >> gvs[] >- (strip_tac >> gvs[] >> metis_tac[MEM]) >> metis_tac[]
QED

Theorem close_cok:
  (∀i hd. i < N ∧ MEM hd (chd (EL i cs)) ⇒
          ∃f j. ALOOKUP tbl hd = SOME f ∧ ALOOKUP ofds f = SOME j ∧ ALOOKUP hlc hd = SOME i ∧
                cok (brequests (rqs i)) (EL i cs) (EL j chans) (MEM hd sett) (hd ∈ rdyf i)
                    (hl_sent hd ps)) ∧
  (∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 cs)) ∧ MEM hd (chd (EL i2 cs)) ⇒ i1 = i2) ∧
  LENGTH cs = N ∧ k < N ∧ chd (EL k cs) = [hd0] ∧ chd c' = [] ∧
  ALOOKUP tbl hd0 = SOME f0 ∧ ALOOKUP ofds f0 = SOME j0 ∧
  ALL_DISTINCT (MAP SND tbl) ∧ ALL_DISTINCT (MAP SND ofds) ∧
  (∀j. j ≠ j0 ⇒ EL j chans' = EL j chans) ∧
  (∀i. i ≠ k ⇒ rdyf' i = rdyf i) ∧ (∀hd. hl_sent hd ps' = hl_sent hd ps) ⇒
  Abbrev (
  ∀i hd. i < N ∧ MEM hd (chd (EL i (LUPDATE c' k cs))) ⇒
         ∃f j. ALOOKUP (ADELKEY hd0 tbl) hd = SOME f ∧ ALOOKUP (ADELKEY f0 ofds) f = SOME j ∧
               ALOOKUP hlc hd = SOME i ∧
               cok (brequests (rqs i)) (EL i (LUPDATE c' k cs)) (EL j chans')
                   (MEM hd (FILTER (λy. hd0 ≠ y) sett)) (hd ∈ rdyf' i) (hl_sent hd ps'))
Proof
  simp[markerTheory.Abbrev_def] >>
  rpt strip_tac >> Cases_on ‘i = k’ >- gvs[EL_LUPDATE] >>
  gvs[EL_LUPDATE] >>
  ‘hd ≠ hd0’ by (strip_tac >> qpat_x_assum ‘hd = hd0’ SUBST_ALL_TAC >>
                 qpat_x_assum ‘∀i1 i2 hd. i1 < N ∧ i2 < N ∧ _ ⇒ _’
                   (qspecl_then [‘i’, ‘k’, ‘hd0’] mp_tac) >> simp[]) >>
  qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
  ‘f ≠ f0’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  ‘j ≠ j0’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  qexistsl_tac [‘f’, ‘j’] >> simp[ALOOKUP_ADELKEY, MEM_FILTER]
QED

Theorem close_idle:
  (∀i hd'. i < N ∧ (EL i cs = CIdle ∨ ∃hd. EL i cs = CPend hd) ∧ ALOOKUP hlc hd' = SOME i ⇒
           hl_sent hd' ps = []) ∧
  k < N ∧ LENGTH cs = N ∧ chd c' = [] ∧ (c' = CIdle ⇒ ∃h. EL k cs = CPend h) ∧
  (∀hd. hl_sent hd ps' = hl_sent hd ps) ⇒
  Abbrev (
  ∀i hd'. i < N ∧ (EL i (LUPDATE c' k cs) = CIdle ∨ ∃hd. EL i (LUPDATE c' k cs) = CPend hd) ∧
          ALOOKUP hlc hd' = SOME i ⇒ hl_sent hd' ps' = [])
Proof
  simp[markerTheory.Abbrev_def] >>
  rpt strip_tac >> Cases_on ‘i = k’ >> gvs[EL_LUPDATE, chd_def] >> metis_tac[]
QED

Theorem close_up:
  (∀i hd rest hd'. i < N ∧ EL i cs = CUp hd rest ∧ ALOOKUP hlc hd' = SOME i ∧
                   hl_sent hd' ps ≠ [] ⇒ hd' = hd) ∧
  k < N ∧ LENGTH cs = N ∧ (∀h r. c' ≠ CUp h r) ∧ (∀hd. hl_sent hd ps' = hl_sent hd ps) ⇒
  Abbrev (
  ∀i hd rest hd'. i < N ∧ EL i (LUPDATE c' k cs) = CUp hd rest ∧ ALOOKUP hlc hd' = SOME i ∧
                  hl_sent hd' ps' ≠ [] ⇒ hd' = hd)
Proof
  simp[markerTheory.Abbrev_def] >>
  rpt strip_tac >> Cases_on ‘i = k’ >> gvs[EL_LUPDATE] >> metis_tac[]
QED

Theorem close_ended:
  (∀hd. MEM hd (MAP FST hlc) ⇔ MEM hd (hl_conn_handles ps)) ∧
  (∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ MEM hd (MAP FST hlc)) ∧
  (∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ ¬MEM hd (MAP FST tbl)) ∧
  (∀hd. ¬(hl_refused hd ps ∧ hl_eof hd ps)) ∧
  (∀hd. MEM hd (MAP FST tbl) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i cs))) ∧
  MEM hd0 (MAP FST hlc) ∧
  (∀hd. hd ≠ hd0 ⇒ (hl_refused hd ps' ⇔ hl_refused hd ps) ∧ (hl_eof hd ps' ⇔ hl_eof hd ps)) ∧
  ¬(hl_refused hd0 ps' ∧ hl_eof hd0 ps') ∧
  (∀hd. MEM hd (MAP FST (ADELKEY hd0 tbl)) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i cs'))) ⇒
  Abbrev (
  (∀hd. hl_refused hd ps' ∨ hl_eof hd ps' ⇒ MEM hd (hl_conn_handles ps)) ∧
  (∀hd. hl_refused hd ps' ∨ hl_eof hd ps' ⇒ ¬MEM hd (MAP FST (ADELKEY hd0 tbl))) ∧
  (∀hd. ¬(hl_refused hd ps' ∧ hl_eof hd ps')) ∧
  (∀hd. hl_refused hd ps' ∨ hl_eof hd ps' ⇒ ∀i. i < N ⇒ ¬MEM hd (chd (EL i cs'))))
Proof
  simp[markerTheory.Abbrev_def] >>
  strip_tac >> rpt conj_tac >> gen_tac >> Cases_on ‘hd = hd0’ >>
  gvs[MAP_FST_ADELKEY, MEM_FILTER] >> metis_tac[]
QED

Theorem EVERY_ADELKEY:
  EVERY P (MAP g l) ⇒ EVERY P (MAP g (ADELKEY k l))
Proof
  simp[ADELKEY_def, EVERY_MEM, MEM_MAP, MEM_FILTER, PULL_EXISTS]
QED

Theorem eof_done_upd:
  (∀hd i. hl_eof hd ps ∧ ALOOKUP hlc hd = SOME i ⇒ EL i cs = CDone) ∧
  ALOOKUP hlc hd0 = SOME k ∧ EL k cs ≠ CDone ∧ k < LENGTH cs ∧
  (∀hd'. hd' ≠ hd0 ⇒ (hl_eof hd' ps' ⇔ hl_eof hd' ps)) ∧ (hl_eof hd0 ps' ⇒ c' = CDone) ⇒
  Abbrev (∀hd i. hl_eof hd ps' ∧ ALOOKUP hlc hd = SOME i ⇒ EL i (LUPDATE c' k cs) = CDone)
Proof
  simp[markerTheory.Abbrev_def, EL_LUPDATE] >> rpt strip_tac >> Cases_on ‘hd = hd0’
  >- (‘i = k’ by gvs[] >> gvs[]) >>
  ‘hl_eof hd ps’ by metis_tac[] >> ‘EL i cs = CDone’ by metis_tac[] >> rw[] >> gvs[]
QED

Theorem crel_close:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ chd (EL k st.cs) = [hd] ∧
  ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧
  wframe j w w1 ∧ w1.open_fds = ADELKEY f w.open_fds ∧
  chd c' = [] ∧ (∀h r. c' ≠ CUp h r) ∧
  (c' = CIdle ⇒ (∃h. EL k st.cs = CPend h) ∧ hl_sent hd ps = []) ∧
  (∀hd'. hl_sent hd' ps' = hl_sent hd' ps) ∧ hl_conn_handles ps' = hl_conn_handles ps ∧
  (∀hd'. hd' ≠ hd ⇒ (hl_refused hd' ps' ⇔ hl_refused hd' ps) ∧ (hl_eof hd' ps' ⇔ hl_eof hd' ps)) ∧
  ¬(hl_refused hd ps' ∧ hl_eof hd ps') ∧ (hl_eof hd ps' ⇒ c' = CDone) ∧
  (∀i. i ≠ k ⇒ rdyf' i = rdyf i) ⇒
  crel a N rqs lfd (st with cs := LUPDATE c' k st.cs) rdyf' ps' w1 (eh_del hd hs)
Proof
  strip_tac >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  qpat_x_assum ‘wframe _ _ _’ (strip_assume_tac o REWRITE_RULE [wframe_def]) >>
  ‘MEM hd (chd (EL k st.cs))’ by simp[] >>
  ‘ALOOKUP st.hlc hd = SOME k’
    by (qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
        first_assum ACCEPT_TAC) >>
  ‘MEM hd (MAP FST st.hlc)’
    by (qpat_x_assum ‘ALOOKUP st.hlc hd = SOME k’ mp_tac >> rpt (pop_assum kall_tac) >>
        rw[] >> imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >> metis_tac[FST]) >>
  ‘∀x. MEM x (MAP SND (ADELKEY hd hs.tbl)) ⇔ MEM x (MAP SND hs.tbl) ∧ x ≠ f’
    by (gen_tac >> irule MEM_SND_ADELKEY >> simp[]) >>
  ‘∀hd'. MEM hd' (chd c') ⇒ MEM hd' (chd (EL k st.cs))’ by simp[] >>
  ‘c' = CIdle ⇒ ∃h. EL k st.cs = CPend h’ by (strip_tac >> fs[]) >>
  drule_all lupd_tbl_close >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all close_cok >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all close_idle >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all close_up >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all close_ended >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all lupd_owner >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  ‘EL k st.cs ≠ CDone’ by (strip_tac >> fs[chd_def]) >>
  ‘k < LENGTH st.cs’ by simp[] >>
  ‘∀hd'. hd' ≠ hd ⇒ (hl_eof hd' ps' ⇔ hl_eof hd' ps)’ by simp[] >>
  drule_all eof_done_upd >>
    disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  SIMP_TAC (srw_ss()) [crel_def, eh_del_def] >> rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  TRY (irule ALL_DISTINCT_ADELKEY >> simp[] >> NO_TAC) >>
  TRY (irule EVERY_ADELKEY >> simp[] >> NO_TAC) >>
  TRY (gen_tac >> simp[MAP_FST_ADELKEY, MEM_FILTER] >>
       qpat_x_assum ‘∀f. MEM f (MAP FST w.open_fds) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
       eq_tac >> rw[] >> NO_TAC) >>
  qpat_x_assum ‘w1.open_fds = _’ (fn th => REWRITE_TAC [th]) >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  TRY (irule ALL_DISTINCT_ADELKEY >> simp[] >> NO_TAC) >>
  TRY (irule EVERY_ADELKEY >> simp[] >> NO_TAC) >>
  TRY (REWRITE_TAC [GSYM DE_MORGAN_THM] >> first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  TRY (rpt strip_tac >> qpat_x_assum ‘∀hd. MEM hd (MAP FST st.hlc) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
       qpat_x_assum ‘∀hd. hl_refused hd ps' ∨ hl_eof hd ps' ⇒ MEM hd (hl_conn_handles ps)’ irule >>
       simp[] >> NO_TAC) >>
  TRY (rpt gen_tac >> strip_tac >>
       qpat_x_assum ‘∀hd'. hl_sent hd' ps' = _’ (fn th => REWRITE_TAC [th]) >>
       qpat_x_assum ‘∀hd i. ALOOKUP st.hlc hd = SOME i ⇒ i < N ∧ _’ drule >> simp[] >> NO_TAC)
QED

(* ------------------------------------------------------------------------
   An action that keeps a connection's handle open keeps the relation
   ------------------------------------------------------------------------ *)

Theorem keep_tbl:
  (∀hd. MEM hd (MAP FST tbl) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i cs))) ∧
  LENGTH cs = N ∧ k < N ∧ chd c' = chd (EL k cs) ⇒
  Abbrev (∀hd. MEM hd (MAP FST tbl) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i (LUPDATE c' k cs))))
Proof
  simp[markerTheory.Abbrev_def] >> rw[EL_LUPDATE] >> eq_tac >> rw[]
  >- (qexists_tac ‘i’ >> rw[] >> gvs[]) >>
  qexists_tac ‘i’ >> Cases_on ‘i = k’ >> gvs[]
QED

Theorem keep_cok:
  (∀i hd. i < N ∧ MEM hd (chd (EL i cs)) ⇒
          ∃f j. ALOOKUP tbl hd = SOME f ∧ ALOOKUP ofds f = SOME j ∧ ALOOKUP hlc hd = SOME i ∧
                cok (brequests (rqs i)) (EL i cs) (EL j chans) (MEM hd sett) (hd ∈ rdyf i)
                    (hl_sent hd ps)) ∧
  (∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 cs)) ∧ MEM hd (chd (EL i2 cs)) ⇒ i1 = i2) ∧
  LENGTH cs = N ∧ k < N ∧ chd (EL k cs) = [hd0] ∧ chd c' = [hd0] ∧
  ALOOKUP tbl hd0 = SOME f0 ∧ ALOOKUP ofds f0 = SOME j0 ∧
  ALL_DISTINCT (MAP SND tbl) ∧ ALL_DISTINCT (MAP SND ofds) ∧
  (∀j. j ≠ j0 ⇒ EL j chans' = EL j chans) ∧
  cok (brequests (rqs k)) c' (EL j0 chans') (MEM hd0 sett) (hd0 ∈ rdyf' k) (hl_sent hd0 ps') ∧
  (∀i. i ≠ k ⇒ rdyf' i = rdyf i) ∧ (∀hd. hd ≠ hd0 ⇒ hl_sent hd ps' = hl_sent hd ps) ⇒
  Abbrev (
  ∀i hd. i < N ∧ MEM hd (chd (EL i (LUPDATE c' k cs))) ⇒
         ∃f j. ALOOKUP tbl hd = SOME f ∧ ALOOKUP ofds f = SOME j ∧ ALOOKUP hlc hd = SOME i ∧
               cok (brequests (rqs i)) (EL i (LUPDATE c' k cs)) (EL j chans') (MEM hd sett)
                   (hd ∈ rdyf' i) (hl_sent hd ps'))
Proof
  simp[markerTheory.Abbrev_def] >> rpt strip_tac >> Cases_on ‘i = k’
  >- (qpat_x_assum ‘i = k’ SUBST_ALL_TAC >>
      qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ (qspecl_then [‘k’, ‘hd0’] mp_tac) >>
      simp[] >> strip_tac >> gvs[EL_LUPDATE]) >>
  gvs[EL_LUPDATE] >>
  ‘hd ≠ hd0’ by (strip_tac >> qpat_x_assum ‘hd = hd0’ SUBST_ALL_TAC >>
                 qpat_x_assum ‘∀i1 i2 hd. i1 < N ∧ i2 < N ∧ _ ⇒ _’
                   (qspecl_then [‘i’, ‘k’, ‘hd0’] mp_tac) >> simp[]) >>
  qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
  ‘f ≠ f0’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  ‘j ≠ j0’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  qexistsl_tac [‘f’, ‘j’] >> simp[]
QED

Theorem keep_sends:
  (∀hd. hl_sent hd ps ≠ [] ⇒ MEM hd (MAP FST hlc)) ∧
  (∀hd i. ALOOKUP hlc hd = SOME i ⇒ i < N ∧ hl_sent hd ps ≼ brequests (rqs i)) ∧
  (∀hd hd' i. ALOOKUP hlc hd = SOME i ∧ ALOOKUP hlc hd' = SOME i ∧
              hl_sent hd ps ≠ [] ∧ hl_sent hd' ps ≠ [] ⇒ hd = hd') ∧
  (∀i hd'. i < N ∧ (EL i cs = CIdle ∨ ∃hd. EL i cs = CPend hd) ∧ ALOOKUP hlc hd' = SOME i ⇒
           hl_sent hd' ps = []) ∧
  (∀i hd rest hd'. i < N ∧ EL i cs = CUp hd rest ∧ ALOOKUP hlc hd' = SOME i ∧
                   hl_sent hd' ps ≠ [] ⇒ hd' = hd) ∧
  LENGTH cs = N ∧ k < N ∧ ALOOKUP hlc hd0 = SOME k ∧
  ((∃rest. EL k cs = CUp hd0 rest) ∨ EL k cs = CPend hd0) ∧
  ((∃rest. c' = CUp hd0 rest) ∨ c' = CPend hd0) ∧
  (∀h. c' = CPend h ⇒ EL k cs = CPend h) ∧
  (∀hd. hd ≠ hd0 ⇒ hl_sent hd ps' = hl_sent hd ps) ∧
  hl_sent hd0 ps' ≼ brequests (rqs k) ∧ (hl_sent hd0 ps' ≠ [] ⇒ ∃rest. c' = CUp hd0 rest) ⇒
  Abbrev (
  (∀hd. hl_sent hd ps' ≠ [] ⇒ MEM hd (MAP FST hlc)) ∧
  (∀hd i. ALOOKUP hlc hd = SOME i ⇒ i < N ∧ hl_sent hd ps' ≼ brequests (rqs i)) ∧
  (∀hd hd' i. ALOOKUP hlc hd = SOME i ∧ ALOOKUP hlc hd' = SOME i ∧
              hl_sent hd ps' ≠ [] ∧ hl_sent hd' ps' ≠ [] ⇒ hd = hd') ∧
  (∀i hd'. i < N ∧ (EL i (LUPDATE c' k cs) = CIdle ∨ ∃hd. EL i (LUPDATE c' k cs) = CPend hd) ∧
           ALOOKUP hlc hd' = SOME i ⇒ hl_sent hd' ps' = []) ∧
  (∀i hd rest hd'. i < N ∧ EL i (LUPDATE c' k cs) = CUp hd rest ∧ ALOOKUP hlc hd' = SOME i ∧
                   hl_sent hd' ps' ≠ [] ⇒ hd' = hd))
Proof
  simp[markerTheory.Abbrev_def] >> strip_tac >> rpt conj_tac >> rpt gen_tac >>
  TRY (Cases_on ‘hd = hd0’) >> TRY (Cases_on ‘hd' = hd0’) >> TRY (Cases_on ‘i = k’) >>
  rw[EL_LUPDATE] >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> metis_tac[FST]
QED

Theorem keep_chd:
  chd c' = chd (EL k cs) ∧ k < LENGTH cs ⇒
  Abbrev (∀i. i < LENGTH cs ⇒ chd (EL i (LUPDATE c' k cs)) = chd (EL i cs))
Proof
  simp[markerTheory.Abbrev_def] >> rw[EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem crel_keep:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ chd (EL k st.cs) = [hd] ∧ chd c' = [hd] ∧
  ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧
  wframe j w w1 ∧ w1.open_fds = w.open_fds ∧
  cok (brequests (rqs k)) c' (EL j w1.chans) (MEM hd hs.settling) (hd ∈ rdyf' k) (hl_sent hd ps') ∧
  (∀h. c' = CPend h ⇒ EL k st.cs = CPend h) ∧
  (∀hd'. hd' ≠ hd ⇒ hl_sent hd' ps' = hl_sent hd' ps) ∧
  hl_sent hd ps' ≼ brequests (rqs k) ∧ (hl_sent hd ps' ≠ [] ⇒ ∃rest. c' = CUp hd rest) ∧
  hl_conn_handles ps' = hl_conn_handles ps ∧
  (∀hd'. hl_refused hd' ps' ⇔ hl_refused hd' ps) ∧ (∀hd'. hl_eof hd' ps' ⇔ hl_eof hd' ps) ∧
  (∀i. i ≠ k ⇒ rdyf' i = rdyf i) ⇒
  crel a N rqs lfd (st with cs := LUPDATE c' k st.cs) rdyf' ps' w1 hs
Proof
  strip_tac >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  qpat_x_assum ‘wframe _ _ _’ (strip_assume_tac o REWRITE_RULE [wframe_def]) >>
  ‘MEM hd (chd (EL k st.cs))’ by simp[] >>
  ‘ALOOKUP st.hlc hd = SOME k’
    by (qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
        first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN ‘(∃rest. EL k st.cs = CUp hd rest) ∨ EL k st.cs = CPend hd’ assume_tac
  >- (qpat_x_assum ‘chd (EL k st.cs) = [hd]’ mp_tac >> rpt (pop_assum kall_tac) >>
      Cases_on ‘EL k st.cs’ >> simp[chd_def]) >>
  Q.SUBGOAL_THEN ‘(∃rest. c' = CUp hd rest) ∨ c' = CPend hd’ assume_tac
  >- (qpat_x_assum ‘chd c' = [hd]’ mp_tac >> rpt (pop_assum kall_tac) >>
      Cases_on ‘c'’ >> simp[chd_def]) >>
  ‘chd c' = chd (EL k st.cs)’ by simp[] >>
  ‘∀hd'. MEM hd' (chd c') ⇒ MEM hd' (chd (EL k st.cs))’ by simp[] >>
  ‘k < LENGTH st.cs’ by simp[] >>
  drule_all keep_chd >> disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all keep_tbl >> disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all keep_cok >> disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all keep_sends >> disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all lupd_owner >> disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  ‘¬hl_eof hd ps’
    by (strip_tac >>
        qpat_x_assum ‘∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ ∀i. i < N ⇒ ¬MEM hd _’
          (qspec_then ‘hd’ mp_tac) >> simp[] >> qexists_tac ‘k’ >> simp[]) >>
  ‘EL k st.cs ≠ CDone’ by (strip_tac >> fs[chd_def]) >>
  ‘hl_eof hd ps' ⇒ c' = CDone’ by simp[] >>
  ‘∀hd'. hd' ≠ hd ⇒ (hl_eof hd' ps' ⇔ hl_eof hd' ps)’ by simp[] >>
  drule_all eof_done_upd >> disch_then (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  SIMP_TAC (srw_ss()) [crel_def] >> rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  qpat_x_assum ‘w1.open_fds = _’ (fn th => REWRITE_TAC [th]) >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  TRY (REWRITE_TAC [GSYM DE_MORGAN_THM] >> first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  qpat_x_assum ‘∀hd'. hl_refused hd' ps' ⇔ _’ (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum ‘∀hd'. hl_eof hd' ps' ⇔ _’ (fn th => REWRITE_TAC [th]) >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  TRY (REWRITE_TAC [GSYM DE_MORGAN_THM] >> first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  gen_tac >> disch_tac >> gen_tac >> strip_tac >>
  ‘i < LENGTH st.cs’ by simp[] >>
  qpat_x_assum ‘∀i. i < LENGTH st.cs ⇒ chd _ = _’ (fn th => simp[th]) >>
  qpat_x_assum ‘∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ ∀i. i < N ⇒ ¬MEM hd _’ drule >>
  disch_then drule >> simp[]
QED

(* ------------------------------------------------------------------------
   A read on a connection's handle, a write on an up one
   ------------------------------------------------------------------------ *)

Theorem wframe_refl[simp]:
  wframe j w w
Proof
  simp[wframe_def]
QED

Theorem cupd_st_simp[simp]:
  st with <| cs := X; nh := st.nh; hlc := st.hlc |> = st with cs := X
Proof
  simp[theorem "cst_component_equality"]
QED

Theorem cread_bounds[simp]:
  0 < cread ∧ cread < 256 ** 8
Proof
  EVAL_TAC
QED

Theorem crel_handle:
  crel a N rqs lfd st rdyf ps w hs ∧ i < N ∧ MEM hd (chd (EL i st.cs)) ⇒
  ∃f j. ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧
        ALOOKUP st.hlc hd = SOME i ∧
        cok (brequests (rqs i)) (EL i st.cs) (EL j w.chans) (MEM hd hs.settling)
            (hd ∈ rdyf i) (hl_sent hd ps)
Proof
  strip_tac >> qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
  qexistsl_tac [‘f’, ‘j’] >> simp[] >>
  imp_res_tac ALOOKUP_MEM >> fs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> res_tac >> fs[]
QED

Theorem crel_takes:
  crel a N rqs lfd st rdyf ps w hs ⇒ w.takes = (λj b n. n) ∧ LENGTH st.cs = N
Proof
  simp[crel_def]
QED

Theorem crel_open_not_ended:
  crel a N rqs lfd st rdyf ps w hs ∧ ALOOKUP hs.tbl hd = SOME f ⇒
  ¬hl_refused hd ps ∧ ¬hl_eof hd ps
Proof
  strip_tac >>
  ‘MEM hd (MAP FST hs.tbl)’
    by (qpat_x_assum ‘ALOOKUP hs.tbl hd = SOME f’ mp_tac >> rpt (pop_assum kall_tac) >>
        rw[] >> imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >> metis_tac[FST]) >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  qpat_x_assum ‘∀hd. hl_refused hd ps ∨ hl_eof hd ps ⇒ ¬MEM hd (MAP FST hs.tbl)’
    (qspec_then ‘hd’ mp_tac) >> simp[]
QED

Theorem crel_read:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ MEM hd (chd (EL k st.cs)) ∧
  (∀h. EL k st.cs = CPend h ⇒ hd ∈ rdyf k) ⇒
  ∃r w1 hs1. ehdo lfd v (w, hs) (ERead hd cread) = SOME (r, (w1, hs1)) ∧
     crel a N rqs lfd (cupd rqs st [(k, ERead hd cread)] [r]) ((k =+ ∅) rdyf)
       (ps ++ [(ERead hd cread, r)]) w1 hs1 ∧ wkeep w w1
Proof
  strip_tac >> drule_all crel_handle >> strip_tac >>
  ‘chd (EL k st.cs) = [hd]’
    by (qpat_x_assum ‘MEM hd (chd _)’ mp_tac >> Cases_on ‘EL k st.cs’ >> simp[chd_def]) >>
  ‘(EL j w.chans).status ≠ Connecting ∧ (EL j w.chans).status ≠ Failed ∧
   ¬(EL j w.chans).shut ∧
   ((EL j w.chans).status = Refused ⇒ EL k st.cs = CPend hd) ∧
   hl_sent hd ps = (EL j w.chans).sent ∧
   (EL k st.cs = CPend hd ⇒ hl_sent hd ps = [])’
    by (Cases_on ‘EL k st.cs’ >> gvs[cok_def, chd_def]) >>
  ‘0 < cread ∧ cread < 256 ** 8’ by simp[] >>
  drule_all ehdo_read >> disch_then (qspecl_then [‘v’, ‘lfd’] strip_assume_tac) >>
  qexistsl_tac [‘r’, ‘w'’, ‘hs'’] >> simp[] >>
  drule_all crel_open_not_ended >> strip_tac >>
  ‘(EL j w.chans).status = Up ∨ (EL j w.chans).status = Refused’
    by (Cases_on ‘(EL j w.chans).status’ >> fs[]) >>
  (* refused *)
  TRY (qpat_x_assum ‘r = ERefused’ SUBST_ALL_TAC >> qpat_x_assum ‘hs' = _’ SUBST_ALL_TAC >>
       ‘EL k st.cs = CPend hd’
         by (qpat_x_assum ‘_ ⇒ EL k st.cs = CPend hd’ irule >> first_assum ACCEPT_TAC) >>
       simp[cres_def, new_hd_def] >> conj_tac
       >- (irule crel_close >> simp[chd_def, combinTheory.APPLY_UPDATE_THM] >>
           qexistsl_tac [‘j’, ‘ps’, ‘rdyf’, ‘w’] >> simp[chd_def, combinTheory.APPLY_UPDATE_THM]) >>
       fs[wkeep_def, wframe_def] >> rw[] >> Cases_on ‘j' = j’ >> simp[] >> NO_TAC) >>
  (* EOF *)
  TRY (qpat_x_assum ‘r = EGot (SOME [])’ SUBST_ALL_TAC >> qpat_x_assum ‘hs' = _’ SUBST_ALL_TAC >>
       simp[cres_def, new_hd_def] >> conj_tac
       >- (irule crel_close >> simp[chd_def, combinTheory.APPLY_UPDATE_THM] >>
           qexistsl_tac [‘j’, ‘ps’, ‘rdyf’, ‘w’] >> simp[chd_def, combinTheory.APPLY_UPDATE_THM]) >>
       fs[wkeep_def, wframe_def] >> rw[] >> Cases_on ‘j' = j’ >> simp[] >> NO_TAC) >>
  (* data, none: the connection stays (CPend becomes CUp) *)
  ‘∀d. r = EGot (SOME d) ⇒ d ≠ []’ by (rw[] >> fs[cread_def]) >>
  ‘∃rest. cres (brequests (rqs k)) (EL k st.cs) (ERead hd cread) r = CUp hd rest ∧
          (EL j w.chans).sent ++ rest = brequests (rqs k)’
    by (Cases_on ‘EL k st.cs’ >> gvs[chd_def, cok_def, cres_def] >>
        Cases_on ‘TAKE cread (EL j w.chans).inbox’ >> gvs[TAKE_EQ_NIL]) >>
  qpat_x_assum ‘r = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  qpat_x_assum ‘cres _ _ _ _ = _’ (fn th => simp[new_hd_def, th]) >>
  TRY (conj_tac >- (irule crel_keep >> simp[chd_def, combinTheory.APPLY_UPDATE_THM] >>
                    qexistsl_tac [‘j’, ‘ps’, ‘rdyf’, ‘w’] >> simp[cok_def] >>
                    gvs[wframe_def] >> metis_tac[rich_listTheory.IS_PREFIX_APPEND]) >>
       fs[wkeep_def, wframe_def] >> rw[] >> Cases_on ‘j' = j’ >> simp[] >> NO_TAC) >>
  irule crel_keep >> simp[chd_def, combinTheory.APPLY_UPDATE_THM] >>
  qexistsl_tac [‘j’, ‘ps’, ‘rdyf’, ‘w’] >> simp[cok_def] >>
  metis_tac[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem crel_write:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ EL k st.cs = CUp hd rest ∧ rest ≠ [] ⇒
  ∃r w1 hs1. ehdo lfd v (w, hs) (EWrite hd rest) = SOME (r, (w1, hs1)) ∧
     crel a N rqs lfd (cupd rqs st [(k, EWrite hd rest)] [r]) rdyf
       (ps ++ [(EWrite hd rest, r)]) w1 hs1 ∧ wkeep w w1 ∧
     EL k (cupd rqs st [(k, EWrite hd rest)] [r]).cs = CUp hd [] ∧ new_hd r = NONE
Proof
  strip_tac >> ‘MEM hd (chd (EL k st.cs))’ by simp[chd_def] >>
  drule_all crel_handle >> strip_tac >> drule crel_takes >> strip_tac >>
  ‘(EL j w.chans).status = Up ∧ ¬(EL j w.chans).shut ∧
   (EL j w.chans).sent ++ rest = brequests (rqs k) ∧ hl_sent hd ps = (EL j w.chans).sent’
    by gvs[cok_def] >>
  drule_all ehdo_write_up >> disch_then (fn th => simp[th]) >>
  simp[cres_def, new_hd_def, EL_LUPDATE] >>
  qabbrev_tac ‘w1 = upd_chan j (λc. c with <| sent := c.sent ++ rest;
                                              inflight := c.inflight + LENGTH rest |>) w’ >>
  ‘wframe j w w1 ∧ w1.open_fds = w.open_fds ∧
   EL j w1.chans = (EL j w.chans) with <| sent := (EL j w.chans).sent ++ rest;
                                         inflight := (EL j w.chans).inflight + LENGTH rest |>’
    by simp[Abbr ‘w1’, wframe_def, upd_chan_def, EL_LUPDATE] >>
  conj_tac
  >- (irule crel_keep >> simp[chd_def, cok_def, hl_one] >>
      qexistsl_tac [‘j’, ‘ps’, ‘rdyf’, ‘w’] >> simp[chd_def] >> rw[] >>
      gvs[hl_one, Abbr ‘w1’, upd_chan_def, EL_LUPDATE]) >>
  simp[wkeep_def, Abbr ‘w1’, upd_chan_def, EL_LUPDATE] >> rw[]
QED

Theorem wkeep_trans:
  wkeep w1 w2 ∧ wkeep w2 w3 ⇒ wkeep w1 w3
Proof
  rw[wkeep_def] >> rpt (first_x_assum (qspec_then ‘j’ mp_tac)) >> rw[] >> gvs[]
QED

Theorem ehacts_one:
  ehdo lfd (lv n k) st x = SOME (r, st1) ⇒ ehacts lfd lv n k st [x] = SOME ([r], st1)
Proof
  simp[ehacts_def]
QED

Theorem ehacts_two:
  ehdo lfd (lv n k) st x = SOME (r, st1) ∧ ehdo lfd (lv n (k + 1)) st1 y = SOME (r', st2) ⇒
  ehacts lfd lv n k st [x; y] = SOME ([r; r'], st2)
Proof
  simp[ehacts_def]
QED

(* The goal and the assumptions in the same normal form, without using the
   assumptions *)
val norm_tac = RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >> SIMP_TAC (srw_ss()) [] >>
               rpt conj_tac >> TRY (first_assum ACCEPT_TAC);

(* Connection k's actions of the round (started with nh0 handles used):
   the relation holds after them, k's ready set used up; the others'
   states are untouched; at most one handle is issued *)
Theorem crel_conn:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ N < dimword (:64) ∧
  (nh0 < cbound ⇒ st.nh + 2 < dimword (:64)) ⇒
  ∃rs w1 hs1.
    ehacts lfd lv n ix (w, hs) (cact1 a nh0 (EL k st.cs) (rdyf k)) = SOME (rs, (w1, hs1)) ∧
    crel a N rqs lfd (cupd rqs st (MAP (λx. (k, x)) (cact1 a nh0 (EL k st.cs) (rdyf k))) rs)
      ((k =+ ∅) rdyf) (ps ++ ZIP (cact1 a nh0 (EL k st.cs) (rdyf k), rs)) w1 hs1 ∧
    wkeep w w1 ∧ LENGTH rs = LENGTH (cact1 a nh0 (EL k st.cs) (rdyf k)) ∧
    (∀i. i ≠ k ⇒ EL i (cupd rqs st (MAP (λx. (k, x)) (cact1 a nh0 (EL k st.cs) (rdyf k))) rs).cs =
                 EL i st.cs) ∧
    (cupd rqs st (MAP (λx. (k, x)) (cact1 a nh0 (EL k st.cs) (rdyf k))) rs).nh ≤ st.nh + 1
Proof
  strip_tac >> ‘LENGTH st.cs = N ∧ st.nh = hs.nxt’ by fs[crel_def] >>
  (* no action: only the ready set changes *)
  ‘(∀hd. MEM hd (chd (EL k st.cs)) ⇒ hd ∉ rdyf k) ⇒
   crel a N rqs lfd st ((k =+ ∅) rdyf) ps w hs’
    by (strip_tac >> irule crel_rdyf >> qexists_tac ‘rdyf’ >>
        rw[combinTheory.APPLY_UPDATE_THM] >> metis_tac[]) >>
  Cases_on ‘EL k st.cs’ >> simp[cact1_def]
  >~ [‘EL k st.cs = CIdle’]
  >- (IF_CASES_TAC
      >- (‘hs.nxt + 2 < dimword (:64)’ by gvs[] >>
          drule_all crel_connect >> disch_then (qspec_then ‘lv n ix’ strip_assume_tac) >> drule ehacts_one >> strip_tac >>
          qexistsl_tac [‘[r]’, ‘w1’, ‘hs1’] >> norm_tac >> rw[EL_LUPDATE]) >>
      simp[ehacts_def, cupd_def] >>
      first_x_assum irule >> simp[chd_def])
  >~ [‘EL k st.cs = CDone’]
  >- (simp[ehacts_def, cupd_def] >>
      first_x_assum irule >> simp[chd_def])
  >~ [‘EL k st.cs = CPend hd’]
  >- (IF_CASES_TAC
      >- (‘MEM hd (chd (EL k st.cs)) ∧ ∀h. EL k st.cs = CPend h ⇒ hd ∈ rdyf k’ by simp[chd_def] >>
          drule_all crel_read >> disch_then (qspec_then ‘lv n ix’ strip_assume_tac) >> drule ehacts_one >> strip_tac >>
          qexistsl_tac [‘[r]’, ‘w1’, ‘hs1’] >> norm_tac >> rw[EL_LUPDATE]) >>
      simp[ehacts_def, cupd_def] >>
      first_x_assum irule >> simp[chd_def]) >>
  rename1 ‘EL k st.cs = CUp hd rest’ >>
  Cases_on ‘rest = []’ >> simp[]
  >- (IF_CASES_TAC
      >- (‘MEM hd (chd (EL k st.cs)) ∧ ∀h. EL k st.cs = CPend h ⇒ hd ∈ rdyf k’ by simp[chd_def] >>
          drule_all crel_read >> disch_then (qspec_then ‘lv n ix’ strip_assume_tac) >> drule ehacts_one >> strip_tac >>
          qexistsl_tac [‘[r]’, ‘w1’, ‘hs1’] >> norm_tac >> rw[EL_LUPDATE]) >>
      simp[ehacts_def, cupd_def] >>
      first_x_assum irule >> simp[chd_def]) >>
  drule_all crel_write >> disch_then (qspec_then ‘lv n ix’ strip_assume_tac) >>
  qabbrev_tac ‘st1 = cupd rqs st [(k, EWrite hd rest)] [r]’ >>
  ‘LENGTH st1.cs = N ∧ st1.nh = st.nh ∧ ∀i. i ≠ k ⇒ EL i st1.cs = EL i st.cs’
    by (simp[Abbr ‘st1’, EL_LUPDATE] >> fs[]) >>
  ‘∀r'. cupd rqs st [(k, EWrite hd rest); (k, ERead hd cread)] [r; r'] =
        cupd rqs st1 [(k, ERead hd cread)] [r']’
    by (rpt (qpat_x_assum ‘_ = _’ kall_tac) >> qunabbrev_tac ‘st1’ >>
        simp_tac (srw_ss()) [cupd_def]) >>
  ‘cupd rqs st [(k, EWrite hd rest)] [r] = st1’ by fs[markerTheory.Abbrev_def] >>
  IF_CASES_TAC
  >- (‘MEM hd (chd (EL k st1.cs)) ∧ ∀h. EL k st1.cs = CPend h ⇒ hd ∈ rdyf k’ by simp[chd_def] >>
      drule_all crel_read >> disch_then (qspec_then ‘lv n (ix + 1)’ strip_assume_tac) >>
      ‘ehacts lfd lv n ix (w, hs) [EWrite hd rest; ERead hd cread] = SOME ([r; r'], (w1', hs1'))’
        by (irule ehacts_two >> metis_tac[]) >>
      qexistsl_tac [‘[r; r']’, ‘w1'’, ‘hs1'’] >>
      SIMP_TAC list_ss [] >>
      qpat_x_assum ‘ehacts _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum ‘∀r'. cupd _ _ [_; _] _ = _’ (fn th => REWRITE_TAC [th]) >>
      ‘ps ++ [(EWrite hd rest, r); (ERead hd cread, r')] =
       ps ++ [(EWrite hd rest, r)] ++ [(ERead hd cread, r')]’ by simp[] >>
      pop_assum SUBST1_TAC >> rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (irule wkeep_trans >> qexists_tac ‘w1’ >> conj_tac >> first_assum ACCEPT_TAC)
      >- (rpt strip_tac >> asm_simp_tac (srw_ss()) [EL_LUPDATE])
      >> SIMP_TAC (srw_ss()) [] >> qpat_x_assum ‘st1.nh = _’ SUBST1_TAC >> rw[]) >>
  qexistsl_tac [‘[r]’, ‘w1’, ‘hs1’] >> drule ehacts_one >> disch_then (fn th => REWRITE_TAC [th]) >>
  SIMP_TAC list_ss [] >> qpat_x_assum ‘cupd _ _ [_] _ = st1’ (fn th => REWRITE_TAC [th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule crel_rdyf >> qexists_tac ‘rdyf’ >> conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rw[combinTheory.APPLY_UPDATE_THM] >> gvs[chd_def]) >>
  simp[]
QED

Theorem cupd_APPEND:
  ∀xs rs st. LENGTH rs = LENGTH xs ⇒
    cupd rqs st (xs ++ ys) (rs ++ rs') = cupd rqs (cupd rqs st xs rs) ys rs'
Proof
  Induct >> simp[cupd_def] >> rpt gen_tac >> PairCases_on ‘h’ >> Cases_on ‘rs’ >>
  simp[cupd_def]
QED

Theorem ehacts_APPEND:
  ∀xs k st rs st1. ehacts lfd lv n k st xs = SOME (rs, st1) ∧
    ehacts lfd lv n (k + LENGTH xs) st1 ys = SOME (rs', st2) ⇒
    ehacts lfd lv n k st (xs ++ ys) = SOME (rs ++ rs', st2)
Proof
  Induct >> simp[ehacts_def] >> rw[] >> gvs[AllCaseEqs()] >>
  first_x_assum (qspec_then ‘k + 1’ mp_tac) >> fs[ADD1] >> metis_tac[]
QED

Theorem ehacts_LENGTH:
  ∀xs k st rs st1. ehacts lfd lv n k st xs = SOME (rs, st1) ⇒ LENGTH rs = LENGTH xs
Proof
  Induct >> simp[ehacts_def] >> rw[] >> gvs[AllCaseEqs()] >> res_tac
QED

(* The round's actions, connection by connection: the first m *)
Definition cacts_upto_def:
  cacts_upto a st0 rdy m =
    FLAT (GENLIST (λi. MAP (λx. (i, x)) (cact1 a st0.nh (EL i st0.cs) rdy)) m)
End

Theorem cacts_upto_SUC:
  cacts_upto a st0 rdy (SUC m) =
    cacts_upto a st0 rdy m ++ MAP (λx. (m, x)) (cact1 a st0.nh (EL m st0.cs) rdy)
Proof
  simp[cacts_upto_def, GENLIST, SNOC_APPEND, FLAT_APPEND]
QED

Theorem cacts_upto_all:
  cacts a st0 rdy = cacts_upto a st0 rdy (LENGTH st0.cs)
Proof
  simp[cacts_def, cacts_upto_def]
QED

(* The round's actions (from st0, with the ready handles rdy) keep the
   relation; every connection's ready set used up *)
Theorem crel_acts:
  crel a N rqs lfd st0 (K rdy) ps w hs ∧ N < dimword (:64) ∧
  (st0.nh < cbound ⇒ st0.nh + N + 1 < dimword (:64)) ⇒
  ∀m. m ≤ N ⇒
    ∃rs w1 hs1.
      ehacts lfd lv n 0 (w, hs) (MAP SND (cacts_upto a st0 rdy m)) = SOME (rs, (w1, hs1)) ∧
      LENGTH rs = LENGTH (cacts_upto a st0 rdy m) ∧
      crel a N rqs lfd (cupd rqs st0 (cacts_upto a st0 rdy m) rs) (λi. if i < m then ∅ else rdy)
        (ps ++ ZIP (MAP SND (cacts_upto a st0 rdy m), rs)) w1 hs1 ∧
      wkeep w w1 ∧
      (∀i. m ≤ i ⇒ EL i (cupd rqs st0 (cacts_upto a st0 rdy m) rs).cs = EL i st0.cs) ∧
      (cupd rqs st0 (cacts_upto a st0 rdy m) rs).nh ≤ st0.nh + m
Proof
  strip_tac >> Induct
  >- (simp[cacts_upto_def, ehacts_def, cupd_def] >>
      ‘(λi:num. rdy) = K rdy’ by simp[FUN_EQ_THM] >> simp[]) >>
  strip_tac >> fs[] >>
  qabbrev_tac ‘st = cupd rqs st0 (cacts_upto a st0 rdy m) rs’ >>
  ‘m < N’ by simp[] >>
  ‘st0.nh < cbound ⇒ st.nh + 2 < dimword (:64)’ by simp[] >>
  qspecl_then [‘st’, ‘λi. if i < m then ∅ else rdy’, ‘ps ++ ZIP (MAP SND (cacts_upto a st0 rdy m), rs)’,
               ‘w1’, ‘hs1’, ‘m’, ‘st0.nh’, ‘lv’, ‘n’, ‘LENGTH (cacts_upto a st0 rdy m)’] mp_tac
    (Q.GENL [‘st’, ‘rdyf’, ‘ps’, ‘w’, ‘hs’, ‘k’, ‘nh0’, ‘lv’, ‘n’, ‘ix’] crel_conn) >> simp[] >>
  ‘EL m st.cs = EL m st0.cs’ by simp[] >> simp[] >> strip_tac >>
  qexistsl_tac [‘rs ++ rs'’, ‘w1'’, ‘hs1'’] >>
  qabbrev_tac ‘xs = cact1 a st0.nh (EL m st0.cs) rdy’ >>
  ‘MAP SND (cacts_upto a st0 rdy (SUC m)) = MAP SND (cacts_upto a st0 rdy m) ++ xs’
    by simp[cacts_upto_SUC, MAP_MAP_o, combinTheory.o_DEF] >>
  ‘cupd rqs st0 (cacts_upto a st0 rdy (SUC m)) (rs ++ rs') = cupd rqs st (MAP (λx. (m, x)) xs) rs'’
    by (simp[cacts_upto_SUC, Abbr ‘st’] >> irule cupd_APPEND >> simp[]) >>
  ‘(λi. if i < SUC m then ∅ else rdy) = (m =+ ∅) (λi. if i < m then ∅ else rdy)’
    by (simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> rw[] >> fs[]) >>
  ‘ps ++ ZIP (MAP SND (cacts_upto a st0 rdy m) ++ xs, rs ++ rs') =
   ps ++ ZIP (MAP SND (cacts_upto a st0 rdy m), rs) ++ ZIP (xs, rs')’
    by simp[ZIP_APPEND] >>
  ‘LENGTH (cacts_upto a st0 rdy (SUC m)) = LENGTH (cacts_upto a st0 rdy m) + LENGTH xs’
    by simp[cacts_upto_SUC] >>
  ntac 5 (pop_assum (fn th => REWRITE_TAC [th] >> mp_tac th)) >>
  ntac 5 (disch_then (fn th => REWRITE_TAC [th])) >> rpt conj_tac
  >- (irule ehacts_APPEND >> simp[] >> qexists_tac ‘(w1, hs1)’ >> simp[])
  >- simp[]
  >- first_assum ACCEPT_TAC
  >- (irule wkeep_trans >> qexists_tac ‘w1’ >> conj_tac >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> ‘i ≠ m ∧ m ≤ i’ by simp[] >> metis_tac[])
  >> simp[]
QED

(* ------------------------------------------------------------------------
   The poll keeps the relation
   ------------------------------------------------------------------------ *)

(* What time passing does to the world: arrivals only; a channel's
   connect may settle; a channel still connecting is untouched *)
Definition tick_rel_def:
  tick_rel (w : eworld) w' ⇔
    w'.open_fds = w.open_fds ∧ w'.takes = w.takes ∧ w'.alloc = w.alloc ∧
    w'.reserved = w.reserved ∧ MAP FST w'.listening = MAP FST w.listening ∧
    w'.nosock = w.nosock ∧ w'.nconnects = w.nconnects ∧ w'.calls = w.calls ∧
    w'.hist = w.hist ∧ w'.env = w.env ∧ LENGTH w.chans ≤ LENGTH w'.chans ∧
    ∀j. j < LENGTH w.chans ⇒
        (EL j w'.chans).shut = (EL j w.chans).shut ∧
        (EL j w'.chans).sent = (EL j w.chans).sent ∧
        ((EL j w'.chans).status = (EL j w.chans).status ∨
         (EL j w.chans).status = Connecting ∧
         ((EL j w'.chans).status = Up ∨ (EL j w'.chans).status = Refused)) ∧
        ((EL j w'.chans).status = Connecting ⇒
         (EL j w'.chans).inbox = (EL j w.chans).inbox ∧
         (EL j w'.chans).peer_eof = (EL j w.chans).peer_eof)
End

Theorem tick_rel_refl:
  tick_rel w (w with clock := n)
Proof
  simp[tick_rel_def]
QED

Theorem tick_rel_trans:
  tick_rel w1 w2 ∧ tick_rel w2 w3 ⇒ tick_rel w1 w3
Proof
  simp[tick_rel_def] >> strip_tac >> gen_tac >> strip_tac >>
  ‘j < LENGTH w2.chans’ by simp[] >>
  rpt (first_x_assum (qspec_then ‘j’ mp_tac)) >> simp[] >> rw[] >> gvs[]
QED

Theorem tick_rel_deliver:
  tick_rel w (ep_deliver w x)
Proof
  Cases_on ‘x’ >> rw[ep_deliver_def, tick_rel_def, upd_chan_def, EL_LUPDATE] >>
  TRY (CASE_TAC >> simp[] >> PairCases_on ‘h’ >> simp[MAP_FST_AFUPDKEY, EL_APPEND1] >> NO_TAC) >>
  rw[] >> gvs[]
QED

Theorem tick_rel_FOLDL:
  ∀xs w0. tick_rel w w0 ⇒ tick_rel w (FOLDL ep_deliver w0 xs)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  metis_tac[tick_rel_trans, tick_rel_deliver]
QED

Theorem tick_rel_tick:
  tick_rel w (ep_tick w)
Proof
  simp[ep_tick_def] >> irule tick_rel_FOLDL >> simp[tick_rel_refl]
QED

(* One connection's channel across the poll: sett' says whether the settle
   is still unreported; rd' whether the handle is reported ready *)
Theorem poll_cok:
  cok b c ch sett F sent ∧
  ch'.shut = ch.shut ∧ ch'.sent = ch.sent ∧
  (ch'.status = ch.status ∨ ch.status = Connecting ∧ (ch'.status = Up ∨ ch'.status = Refused)) ∧
  (ch'.status = Connecting ⇒ ch'.inbox = ch.inbox ∧ ch'.peer_eof = ch.peer_eof) ∧
  (sett' ⇔ sett ∧ ¬(inh ∧ ch'.status ≠ Connecting)) ∧
  (inh ∧ sett ∧ ch'.status ≠ Connecting ⇒ rd') ∧
  (rd' ⇒ ch'.inbox ≠ [] ∨ ch'.peer_eof ∨ ch'.status = Refused ∨ ch'.status = Failed ∨
         sett ∧ ch'.status ≠ Connecting) ⇒
  cok b c ch' sett' rd' sent
Proof
  Cases_on ‘c’ >> simp[cok_def] >> rw[] >> gvs[] >>
  Cases_on ‘ch'.status’ >> gvs[] >> metis_tac[]
QED

Theorem crel_poll:
  crel a N rqs lfd st (K ∅) ps w hs ∧ ehpoll lfd hs hfds w = (rdy, w', hs') ⇒
  crel a N rqs lfd st (K (set rdy)) ps w' hs'
Proof
  strip_tac >> qpat_x_assum ‘ehpoll _ _ _ _ = _’ mp_tac >> simp[ehpoll_def] >> strip_tac >>
  qabbrev_tac ‘w1 = ep_tick w’ >>
  ‘tick_rel w w1’ by simp[Abbr ‘w1’, tick_rel_tick] >>
  pop_assum (strip_assume_tac o REWRITE_RULE [tick_rel_def]) >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  gvs[] >>
  SIMP_TAC (srw_ss()) [crel_def] >> rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  TRY (‘LENGTH w'.listening = LENGTH w.listening’ by metis_tac[LENGTH_MAP] >> simp[] >> NO_TAC) >>
  TRY (fs[EVERY_MEM] >> rw[] >> res_tac >> simp[] >> NO_TAC) >>
  TRY (qpat_x_assum ‘∀hd. MEM hd (MAP FST st.hlc) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
       first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_x_assum ‘∀hd. MEM hd (MAP FST hs.tbl) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
       rpt strip_tac >> qpat_x_assum ‘∀hd. _ ⇒ ∀i. i < LENGTH st.cs ⇒ _’ drule >>
       disch_then drule >> simp[] >> NO_TAC) >>
  rpt strip_tac >> qpat_x_assum ‘∀i hd. i < LENGTH st.cs ∧ MEM hd _ ⇒ ∃f j. _’ drule_all >>
  strip_tac >> qexistsl_tac [‘f’, ‘j’] >> simp[] >>
  ‘j < LENGTH w.chans’
    by (imp_res_tac ALOOKUP_MEM >> fs[EVERY_MEM, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘¬MEM f (MAP FST w.listening)’
    by (imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘ep_chan_of w' f = SOME j’ by simp[ep_chan_of_def] >>
  ‘chan_status w' f = SOME (EL j w'.chans).status’ by simp[chan_status_def] >>
  ‘FILTER (λ(l, a, q). l = f) w'.listening = []’
    by (simp[FILTER_EQ_NIL, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
        qpat_x_assum ‘¬MEM f (MAP FST w.listening)’ mp_tac >>
        qpat_x_assum ‘MAP FST w'.listening = _’ (SUBST1_TAC o SYM) >>
        simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘ep_readable w' f ⇔ (EL j w'.chans).inbox ≠ [] ∨ (EL j w'.chans).peer_eof ∨
                      (EL j w'.chans).status = Refused ∨ (EL j w'.chans).status = Failed’
    by simp[ep_readable_def] >>
  qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
  irule poll_cok >>
  qexistsl_tac [‘EL j w.chans’, ‘MEM hd hfds’, ‘MEM hd hs.settling’] >>
  simp[MEM_FILTER] >> rpt (pop_assum kall_tac) >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

Theorem ehdo_new_hd:
  ehdo lfd v st x = SOME (r, st') ∧ (∀p. x ≠ EConnect p) ⇒ new_hd r = NONE
Proof
  PairCases_on ‘st’ >> Cases_on ‘x’ >> simp[ehdo_def] >> rw[] >>
  every_case_tac >> gvs[new_hd_def] >> pairarg_tac >> gvs[new_hd_def]
QED

Theorem ehacts_new_hd:
  ∀xs k st rs st'. ehacts lfd lv n k st xs = SOME (rs, st') ∧ EVERY (λx. ∀p. x ≠ EConnect p) xs ⇒
    EVERY (λr. new_hd r = NONE) rs
Proof
  Induct >> simp[ehacts_def] >> rw[] >> gvs[AllCaseEqs()] >>
  metis_tac[ehdo_new_hd]
QED

Theorem cupd_nh_same:
  ∀xs rs st. EVERY (λr. new_hd r = NONE) rs ⇒ (cupd rqs st xs rs).nh = st.nh
Proof
  Induct >> simp[cupd_def] >> rpt gen_tac >> PairCases_on ‘h’ >> Cases_on ‘rs’ >>
  simp[cupd_def]
QED

Theorem cacts_upto_noconnect:
  ¬(st0.nh < cbound) ⇒ EVERY (λx. ∀p. x ≠ EConnect p) (MAP SND (cacts_upto a st0 rdy m))
Proof
  strip_tac >> simp[cacts_upto_def, MAP_FLAT, EVERY_FLAT, EVERY_GENLIST, EVERY_MAP] >>
  rw[] >> Cases_on ‘EL i st0.cs’ >> rw[cact1_def]
QED

Theorem crel_last[simp]:
  crel a N rqs lfd (st with last := x) = crel a N rqs lfd st
Proof
  simp[FUN_EQ_THM, crel_def]
QED

Theorem cacts_last[simp]:
  cacts a (st with last := x) rdy = cacts a st rdy
Proof
  simp[cacts_def]
QED

Theorem crel_round:
  crel a N rqs lfd st0 (K rdy) ps w hs ∧ st0.last = cacts a st0 rdy ∧
  N < cbound ∧ st0.nh < cbound + N ∧
  ehacts_tot lfd lv n (w, hs) (MAP SND st0.last) = (rs, (w1, hs1)) ∧
  ehpoll lfd hs1 hfds w1 = (rdy', w2, hs2) ⇒
  ehacts lfd lv n 0 (w, hs) (MAP SND st0.last) = SOME (rs, (w1, hs1)) ∧
  crel a N rqs lfd (cstep a rqs st0 (ssnap rdy' rs)) (K (set rdy'))
    (ps ++ ZIP (MAP SND st0.last, rs)) w2 hs2 ∧
  (cstep a rqs st0 (ssnap rdy' rs)).last = cacts a (cstep a rqs st0 (ssnap rdy' rs)) (set rdy') ∧
  (cstep a rqs st0 (ssnap rdy' rs)).nh < cbound + N ∧ wkeep w w1
Proof
  strip_tac >> ‘LENGTH st0.cs = N’ by fs[crel_def] >>
  ‘N < dimword (:64) ∧ (st0.nh < cbound ⇒ st0.nh + N + 1 < dimword (:64))’
    by fs[cbound_def] >>
  drule crel_acts >> simp[] >> disch_then (qspecl_then [‘n’, ‘lv’, ‘N’] mp_tac) >> simp[] >> strip_tac >>
  ‘st0.last = cacts_upto a st0 rdy N’ by simp[cacts_upto_all] >>
  ‘ehacts lfd lv n 0 (w, hs) (MAP SND st0.last) = SOME (rs', (w1', hs1'))’ by simp[] >>
  ‘rs' = rs ∧ w1' = w1 ∧ hs1' = hs1’ by gvs[ehacts_tot_def] >> gvs[] >>
  simp[cstep_def, asyncM3WorldTheory.ssnap_def] >>
  conj_tac
  >- (‘crel a (LENGTH st0.cs) rqs lfd (cupd rqs st0 (cacts a st0 rdy) rs) (K ∅)
         (ps ++ ZIP (MAP SND (cacts a st0 rdy), rs)) w1 hs1’
        by (irule crel_rdyf >> qexists_tac ‘λi. if i < LENGTH st0.cs then ∅ else rdy’ >>
            conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
      drule_all crel_poll >> simp[]) >>
  Cases_on ‘st0.nh < cbound’
  >- simp[] >>
  ‘(cupd rqs st0 (cacts a st0 rdy) rs).nh = st0.nh’ suffices_by simp[] >>
  irule cupd_nh_same >> irule ehacts_new_hd >>
  metis_tac[cacts_upto_noconnect]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

(* The ready handles the client's state has seen last *)
Definition crdy_def:
  crdy (h : (word64, eresp) snapshot list) = if h = [] then ∅ else (LAST h).ready
End

(* The invariant at round n of the client's run in w0 *)
Definition cinv_def:
  cinv a N rqs lfd lv w0 n ⇔
    let h = ehhist lfd lv (cifds a N rqs) (cprog a N rqs) w0 n;
        st = cstate a N rqs h in
      crel a N rqs lfd st (K (crdy h)) (hl_pairs (cprog a N rqs) h)
        (FST (ehst lfd lv (cifds a N rqs) (cprog a N rqs) w0 n))
        (SND (ehst lfd lv (cifds a N rqs) (cprog a N rqs) w0 n)) ∧
      st.last = cacts a st (crdy h) ∧ st.nh < cbound + N
End

Theorem crel_init:
  client_world lfd c w0 ⇒ crel a N rqs lfd (cinit a N) (K ∅) [] w0 ehinit
Proof
  rw[client_world_def, crel_def, cinit_def, ehinit_def, endpointSpecFormsTheory.no_backpressure_def, EL_REPLICATE,
     chd_def] >>
  TRY (simp[FUN_EQ_THM] >> NO_TAC) >>
  Cases_on ‘i < N’ >> gvs[EL_REPLICATE, chd_def]
QED

Theorem cinv_0:
  client_world lfd c w0 ⇒ cinv a N rqs lfd lv w0 0
Proof
  strip_tac >> drule crel_init >>
  simp[cinv_def, ehhist_def, ehst_def, ehrounds_def, cstate_def, crdy_def, hl_pairs_def] >>
  simp[cinit_def, cbound_def, cacts_def]
QED

Theorem cinv_SUC:
  cinv a N rqs lfd lv w0 n ∧ N < cbound ⇒
  cinv a N rqs lfd lv w0 (SUC n) ∧
  ehacts lfd lv n 0 (ehst lfd lv (cifds a N rqs) (cprog a N rqs) w0 n)
    (new_actions (log_of (cprog a N rqs)) (ehhist lfd lv (cifds a N rqs) (cprog a N rqs) w0 n)) ≠ NONE
Proof
  qmatch_goalsub_abbrev_tac ‘ehst lfd lv ifds m w0 n’ >>
  simp[cinv_def] >> strip_tac >>
  qabbrev_tac ‘h = ehhist lfd lv ifds m w0 n’ >>
  qabbrev_tac ‘st = cstate a N rqs h’ >>
  Cases_on ‘ehst lfd lv ifds m w0 n’ >> rename1 ‘_ = (w, hs)’ >> fs[] >>
  ‘new_actions (log_of m) h = MAP SND st.last’ by simp[Abbr ‘m’, Abbr ‘st’, cprog_new_actions] >>
  Cases_on ‘ehacts_tot lfd lv n (w, hs) (MAP SND st.last)’ >> rename1 ‘_ = (rs, st1)’ >>
  PairCases_on ‘st1’ >> rename1 ‘_ = (rs, (w1, hs1))’ >>
  Cases_on ‘ehpoll lfd hs1 (ifds h) w1’ >> rename1 ‘_ = (rdy', r2)’ >>
  PairCases_on ‘r2’ >> rename1 ‘_ = (rdy', w2, hs2)’ >>
  ‘ehhist lfd lv ifds m w0 (SUC n) = h ++ [ssnap rdy' rs] ∧ ehst lfd lv ifds m w0 (SUC n) = (w2, hs2)’
    by (qunabbrev_tac ‘h’ >> irule honestL1EPRefineTheory.ehround_step >> gvs[]) >>
  ‘st.nh < cbound + N’ by simp[] >>
  drule_all crel_round >> strip_tac >>
  simp[cstate_SNOC, crdy_def, hl_pairs_SNOC] >>
  fs[asyncM3WorldTheory.ssnap_def, Abbr ‘st’, crdy_def] >>
  qpat_x_assum ‘(cstate a N rqs h).last = _’ (fn th => fs[GSYM th])
QED

Theorem cinv_all:
  client_world lfd c w0 ∧ N < cbound ⇒ ∀a rqs lv n. cinv a N rqs lfd lv w0 n
Proof
  strip_tac >> ntac 3 gen_tac >> Induct >- metis_tac[cinv_0] >> metis_tac[cinv_SUC]
QED

Overload cH[local] = “λa N rqs lfd lv w0. ehhist lfd lv (cifds a N rqs) (cprog a N rqs) w0”
Overload cS[local] = “λa N rqs lfd lv w0. ehst lfd lv (cifds a N rqs) (cprog a N rqs) w0”
Overload cst[local] = “λa N rqs lfd lv w0 n. cstate a N rqs (ehhist lfd lv (cifds a N rqs) (cprog a N rqs) w0 n)”

Theorem cinv_crel:
  client_world lfd c w0 ∧ N < cbound ⇒
  ∀a rqs lv n. crel a N rqs lfd (cst a N rqs lfd lv w0 n) (K (crdy (cH a N rqs lfd lv w0 n)))
    (hl_pairs (cprog a N rqs) (cH a N rqs lfd lv w0 n))
    (FST (cS a N rqs lfd lv w0 n)) (SND (cS a N rqs lfd lv w0 n))
Proof
  rpt strip_tac >> drule_all cinv_all >> simp[cinv_def]
QED

Theorem ehhist_SUC:
  ∀lfd lv ifds m w0 n. ∃s. ehhist lfd lv ifds m w0 (SUC n) = ehhist lfd lv ifds m w0 n ++ [s]
Proof
  rpt gen_tac >> simp[ehhist_def, ehrounds_def] >> rpt (pairarg_tac >> simp[])
QED

Theorem ehhist_LENGTH:
  LENGTH (ehhist lfd lv ifds m w0 n) = n
Proof
  Induct_on ‘n’ >- simp[ehhist_def, ehrounds_def] >>
  qspecl_then [‘lfd’, ‘lv’, ‘ifds’, ‘m’, ‘w0’, ‘n’] strip_assume_tac ehhist_SUC >> simp[]
QED

(* ------------------------------------------------------------------------
   Each handle's logical connection
   ------------------------------------------------------------------------ *)

Theorem cupd_hlc:
  ∀xs rs st. ∃l. (cupd rqs st xs rs).hlc = l ++ st.hlc
Proof
  Induct >> simp[cupd_def] >> rpt gen_tac >> PairCases_on ‘h’ >> Cases_on ‘rs’ >>
  simp[cupd_def] >>
  qmatch_goalsub_abbrev_tac ‘cupd rqs st1 xs t’ >>
  first_x_assum (qspecl_then [‘t’, ‘st1’] strip_assume_tac) >>
  simp[Abbr ‘st1’] >> qexists_tac ‘l ++ case new_hd h' of NONE => [] | SOME hd => [(hd, h0)]’ >>
  simp[]
QED

Theorem cst_hlc_mono:
  ∀n'. n ≤ n' ⇒ ∃l. (cst a N rqs lfd lv w0 n').hlc = l ++ (cst a N rqs lfd lv w0 n).hlc
Proof
  Induct >> rpt strip_tac
  >- (‘n = 0’ by simp[] >> qexists_tac ‘[]’ >> simp[]) >>
  Cases_on ‘n = SUC n'’ >- (qexists_tac ‘[]’ >> simp[]) >>
  ‘n ≤ n'’ by simp[] >> first_x_assum drule >> strip_tac >>
  qspecl_then [‘lfd’, ‘lv’, ‘cifds a N rqs’, ‘cprog a N rqs’, ‘w0’, ‘n'’] strip_assume_tac
    ehhist_SUC >>
  simp[cstate_SNOC, cstep_def] >>
  qspecl_then [‘(cst a N rqs lfd lv w0 n').last’, ‘s.results’, ‘cst a N rqs lfd lv w0 n'’]
    strip_assume_tac cupd_hlc >>
  simp[] >> qexists_tac ‘l' ++ l’ >> simp[]
QED

Theorem ALOOKUP_APPEND_distinct:
  ALL_DISTINCT (MAP FST (l ++ L)) ∧ ALOOKUP L k = SOME v ⇒ ALOOKUP (l ++ L) k = SOME v
Proof
  rw[ALOOKUP_APPEND] >> CASE_TAC >> imp_res_tac ALOOKUP_MEM >>
  fs[ALL_DISTINCT_APPEND, MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem cst_ALOOKUP_mono:
  client_world lfd c w0 ∧ N < cbound ∧ n1 ≤ n2 ∧
  ALOOKUP (cst a N rqs lfd lv w0 n1).hlc hd = SOME i ⇒
  ALOOKUP (cst a N rqs lfd lv w0 n2).hlc hd = SOME i
Proof
  strip_tac >>
  ‘ALL_DISTINCT (MAP FST (cst a N rqs lfd lv w0 n2).hlc)’
    by (drule_all cinv_crel >> disch_then (qspecl_then [‘a’, ‘rqs’, ‘lv’, ‘n2’] mp_tac) >> simp[crel_def]) >>
  drule cst_hlc_mono >> disch_then (qspecl_then [‘w0’, ‘rqs’, ‘lv’, ‘lfd’, ‘a’, ‘N’] strip_assume_tac) >>
  pop_assum (fn th => REWRITE_TAC [th] >> RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  irule ALOOKUP_APPEND_distinct >> conj_tac >> first_assum ACCEPT_TAC
QED

Definition clc_def:
  clc a N rqs lfd lv w0 hd = @i. ∃n. ALOOKUP (cst a N rqs lfd lv w0 n).hlc hd = SOME i
End

Theorem clc_eq:
  client_world lfd c w0 ∧ N < cbound ∧ ALOOKUP (cst a N rqs lfd lv w0 n).hlc hd = SOME i ⇒
  clc a N rqs lfd lv w0 hd = i
Proof
  strip_tac >> simp[clc_def] >> SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> rename1 ‘ALOOKUP (cst a N rqs lfd lv w0 n').hlc hd = SOME j’ >>
  ‘ALOOKUP (cst a N rqs lfd lv w0 (MAX n n')).hlc hd = SOME i’
    by (irule cst_ALOOKUP_mono >> simp[] >> conj_tac >- (qexists_tac ‘n’ >> simp[]) >>
        metis_tac[]) >>
  ‘ALOOKUP (cst a N rqs lfd lv w0 (MAX n n')).hlc hd = SOME j’
    by (irule cst_ALOOKUP_mono >> simp[] >> conj_tac >- (qexists_tac ‘n'’ >> simp[]) >>
        metis_tac[]) >>
  fs[]
QED

(* ------------------------------------------------------------------------
   The guarantee's safety clauses
   ------------------------------------------------------------------------ *)

Theorem MEM_ZIP_FST:
  ∀l1 l2. MEM (x, r) (ZIP (l1, l2)) ⇒ MEM x l1
Proof
  Induct >> Cases_on ‘l2’ >> simp[ZIP_def] >> metis_tac[]
QED

Theorem cstate_last:
  ∃rdy. (cstate a N rqs h).last = cacts a (cstate a N rqs h) rdy
Proof
  Cases_on ‘h’ using SNOC_CASES
  >- (simp[cstate_def, cinit_def] >> qexists_tac ‘∅’ >> simp[cacts_def]) >>
  simp[SNOC_APPEND, cstate_SNOC, cstep_def] >> metis_tac[]
QED

Theorem MEM_cacts:
  MEM x (MAP SND (cacts a st rdy)) ⇔ ∃i. i < LENGTH st.cs ∧ MEM x (cact1 a st.nh (EL i st.cs) rdy)
Proof
  simp[cacts_def, MEM_MAP, MEM_FLAT, MEM_GENLIST, PULL_EXISTS] >> metis_tac[]
QED

Theorem cprog_acts_ok:
  MEM (x, r) (hl_pairs (cprog a N rqs) h) ⇒ (∀p. x = EConnect p ⇒ p = a) ∧ ∀l. x ≠ EAccept l
Proof
  simp[hl_pairs_def, MEM_FLAT, MEM_GENLIST, PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  imp_res_tac MEM_ZIP_FST >> fs[cprog_new_actions] >>
  qspecl_then [‘a’, ‘N’, ‘rqs’, ‘TAKE k h’] strip_assume_tac (Q.GENL [‘a’, ‘N’, ‘rqs’, ‘h’] cstate_last) >>
  fs[MEM_cacts] >> Cases_on ‘EL i (cstate a N rqs (TAKE k h)).cs’ >> fs[cact1_def] >>
  qpat_x_assum ‘MEM x _’ mp_tac >> rw[] >> simp[]
QED

Theorem cst_tbl_ifds:
  client_world lfd c w0 ∧ N < cbound ∧ MEM hd (MAP FST (SND (cS a N rqs lfd lv w0 n)).tbl) ⇒
  MEM hd (cifds a N rqs (cH a N rqs lfd lv w0 n))
Proof
  strip_tac >> drule_all cinv_crel >> disch_then (qspecl_then [‘a’, ‘rqs’, ‘lv’, ‘n’] mp_tac) >>
  simp[crel_def] >> strip_tac >> gvs[] >>
  simp[cifds_def, MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM]
QED

Theorem cst_sink:
  client_world lfd c w0 ∧ N < cbound ∧
  hd ∈ (LAST (cH a N rqs lfd lv w0 (SUC n))).ready ∧
  MEM hd (MAP FST (SND (cS a N rqs lfd lv w0 (SUC n))).tbl) ⇒
  ∃k. MEM (ERead hd k) (new_actions (log_of (cprog a N rqs)) (cH a N rqs lfd lv w0 (SUC n)))
Proof
  strip_tac >> drule_all cinv_all >> disch_then (qspecl_then [‘a’, ‘rqs’, ‘lv’, ‘SUC n’] mp_tac) >>
  simp[cinv_def, crdy_def] >>
  ‘cH a N rqs lfd lv w0 (SUC n) ≠ []’
    by (strip_tac >> qspecl_then [‘lfd’, ‘lv’, ‘cifds a N rqs’, ‘cprog a N rqs’, ‘w0’, ‘SUC n’] mp_tac
          (Q.GENL [‘lfd’, ‘lv’, ‘ifds’, ‘m’, ‘w0’, ‘n’] ehhist_LENGTH) >> simp[]) >>
  simp[crel_def] >> strip_tac >> gvs[] >>
  simp[cprog_new_actions, MEM_cacts] >> qexists_tac ‘cread’ >> qexists_tac ‘i’ >> simp[] >>
  Cases_on ‘EL i (cst a N rqs lfd lv w0 (SUC n)).cs’ >> gvs[chd_def, cact1_def]
QED

Theorem cst_lookup_clc:
  client_world lfd c w0 ∧ N < cbound ∧ MEM hd (MAP FST (cst a N rqs lfd lv w0 n).hlc) ⇒
  ALOOKUP (cst a N rqs lfd lv w0 n).hlc hd = SOME (clc a N rqs lfd lv w0 hd) ∧
  clc a N rqs lfd lv w0 hd < N
Proof
  strip_tac >>
  Cases_on ‘ALOOKUP (cst a N rqs lfd lv w0 n).hlc hd’ >- gvs[ALOOKUP_NONE] >>
  drule_all clc_eq >> strip_tac >> gvs[] >>
  drule_all cinv_crel >> disch_then (qspecl_then [‘a’, ‘rqs’, ‘lv’, ‘n’] mp_tac) >>
  simp[crel_def] >> metis_tac[]
QED

(* The guarantee's clauses on handles, at round n *)
Theorem cst_handles:
  client_world lfd c w0 ∧ N < cbound ⇒
  let ps = hl_pairs (cprog a N rqs) (cH a N rqs lfd lv w0 n); lc = clc a N rqs lfd lv w0 in
    (∀hd. MEM hd (hl_conn_handles ps) ⇒ lc hd < N) ∧
    (∀hd. hl_sent hd ps ≼ brequests (rqs (lc hd))) ∧
    (∀hd hd'. hl_sent hd ps ≠ [] ∧ hl_sent hd' ps ≠ [] ∧ lc hd' = lc hd ⇒ hd' = hd) ∧
    (∀hd. ¬(hl_refused hd ps ∧ hl_eof hd ps))
Proof
  strip_tac >> simp[] >>
  drule_all cinv_crel >> disch_then (qspecl_then [‘a’, ‘rqs’, ‘lv’, ‘n’] assume_tac) >>
  ‘∀hd. MEM hd (MAP FST (cst a N rqs lfd lv w0 n).hlc) ⇒
        ALOOKUP (cst a N rqs lfd lv w0 n).hlc hd = SOME (clc a N rqs lfd lv w0 hd) ∧
        clc a N rqs lfd lv w0 hd < N’ by metis_tac[cst_lookup_clc] >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  rpt conj_tac
  >- metis_tac[]
  >- (gen_tac >> Cases_on ‘hl_sent hd (hl_pairs (cprog a N rqs) (cH a N rqs lfd lv w0 n)) = []’
      >- simp[] >> metis_tac[])
  >- metis_tac[]
  >> metis_tac[]
QED

Theorem cst_done:
  client_world lfd c w0 ∧ N < cbound ∧
  (∀i. i < N ⇒ ∃hd. clc a N rqs lfd lv w0 hd = i ∧
                    hl_eof hd (hl_pairs (cprog a N rqs) (cH a N rqs lfd lv w0 n))) ⇒
  (cprog a N rqs (cH a N rqs lfd lv w0 n)).result = SOME ()
Proof
  strip_tac >>
  drule_all cinv_crel >> disch_then (qspecl_then [‘a’, ‘rqs’, ‘lv’, ‘n’] assume_tac) >>
  ‘∀hd. MEM hd (MAP FST (cst a N rqs lfd lv w0 n).hlc) ⇒
        ALOOKUP (cst a N rqs lfd lv w0 n).hlc hd = SOME (clc a N rqs lfd lv w0 hd)’
    by metis_tac[cst_lookup_clc] >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  simp[cprog_def, call_done_def, EVERY_EL] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Liveness (D16)
   ------------------------------------------------------------------------ *)

(* The liveness to prove, as a proposition (proved below: TODO) *)
Definition client_live_def:
  client_live ⇔
    ∀a N rqs lfd lv c w0 i.
  client_world lfd c w0 ∧ N < cbound ∧
  conn_fair lfd lv (cifds a N rqs) (cprog a N rqs) w0 ∧ i < N ⇒
  ∃n. (∃hd. clc a N rqs lfd lv w0 hd = i ∧ ever_up lfd lv (cifds a N rqs) (cprog a N rqs) w0 n hd ∧
            hl_sent hd (hl_pairs (cprog a N rqs) (cH a N rqs lfd lv w0 n)) = brequests (rqs i)) ∨
      (∃hd. MEM hd (hl_conn_handles (hl_pairs (cprog a N rqs) (cH a N rqs lfd lv w0 n))) ∧
            clc a N rqs lfd lv w0 hd = i ∧
            hl_eof hd (hl_pairs (cprog a N rqs) (cH a N rqs lfd lv w0 n)) ∧
            hl_sent hd (hl_pairs (cprog a N rqs) (cH a N rqs lfd lv w0 n)) ≠ brequests (rqs i)) ∨
      cbound ≤ LENGTH (hl_conn_handles (hl_pairs (cprog a N rqs) (cH a N rqs lfd lv w0 n)))
End

(* ------------------------------------------------------------------------
   The claim
   ------------------------------------------------------------------------ *)

Theorem client_hl_claim_of_live:
  client_live ⇒ client_hl_claim cprog cifds
Proof
  strip_tac >> simp[client_hl_claim_def] >> rpt gen_tac >> rename1 ‘client_world lfd c w0’ >> strip_tac >>
  simp[client_guar'_def] >> qexists_tac ‘clc a N rqs lfd lv w0’ >>
  ‘N < cbound’ by simp[] >>
  rpt conj_tac
  >- (gen_tac >> drule_all cinv_all >> strip_tac >> irule (cj 2 cinv_SUC) >> simp[])
  >- (rpt gen_tac >> strip_tac >> drule cprog_acts_ok >> simp[])
  >- (drule_all cst_handles >> simp[] >> metis_tac[])
  >- (drule_all cst_handles >> simp[] >> metis_tac[])
  >- (drule_all cst_handles >> simp[] >> metis_tac[])
  >- (rpt strip_tac >> drule_all cst_tbl_ifds >> simp[])
  >- (rpt strip_tac >> drule_all cst_sink >> simp[])
  >- (drule_all cst_handles >> simp[] >> metis_tac[])
  >- (rpt strip_tac >> fs[client_live_def] >> first_x_assum drule_all >> simp[])
  >> rpt strip_tac >> qexists_tac ‘n’ >> simp[] >> irule cst_done >>
  simp[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Liveness: what one round does to one connection
   ------------------------------------------------------------------------ *)

(* A handle's channel status, as the layer sees it *)
Definition hstat_def:
  hstat ((w : eworld), (hs : ehstate)) hd =
    case ALOOKUP hs.tbl hd of SOME f => chan_status w f | NONE => NONE
End

(* An action on hd0 keeps every other open handle's fd and channel *)
Theorem frame_core:
  ALOOKUP hs.tbl hd0 = SOME f0 ∧ ALOOKUP w.open_fds f0 = SOME j0 ∧
  ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧
  hd ≠ hd0 ∧ ALL_DISTINCT (MAP SND hs.tbl) ∧ ALL_DISTINCT (MAP SND w.open_fds) ∧
  wframe j0 w w1 ∧ (w1.open_fds = w.open_fds ∨ w1.open_fds = ADELKEY f0 w.open_fds) ∧
  (hs1 = hs ∨ hs1 = eh_del hd0 hs) ⇒
  ALOOKUP hs1.tbl hd = SOME f ∧ hstat (w1, hs1) hd = hstat (w, hs) hd
Proof
  strip_tac >>
  ‘f ≠ f0’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  ‘j ≠ j0’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  gvs[eh_del_def, ALOOKUP_ADELKEY, hstat_def, chan_status_def, ep_chan_of_def, wframe_def]
QED

Theorem crel_other:
  crel a N rqs lfd st rdyf ps w hs ∧ MEM hd (MAP FST hs.tbl) ⇒
  ∃f j. ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans
Proof
  rw[crel_def] >> gvs[] >> first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [‘f’, ‘j’] >> simp[] >>
  imp_res_tac ALOOKUP_MEM >> fs[EVERY_MEM, MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem crel_distinct:
  crel a N rqs lfd st rdyf ps w hs ⇒
  ALL_DISTINCT (MAP SND hs.tbl) ∧ ALL_DISTINCT (MAP SND w.open_fds)
Proof
  simp[crel_def]
QED

Theorem frame_read:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ MEM hd0 (chd (EL k st.cs)) ∧
  ehdo lfd v (w, hs) (ERead hd0 cread) = SOME (r, (w1, hs1)) ∧
  hd ≠ hd0 ∧ MEM hd (MAP FST hs.tbl) ⇒
  ALOOKUP hs1.tbl hd = ALOOKUP hs.tbl hd ∧ hstat (w1, hs1) hd = hstat (w, hs) hd
Proof
  strip_tac >> drule_all crel_handle >> strip_tac >>
  rename1 ‘ALOOKUP hs.tbl hd0 = SOME f0’ >> rename1 ‘ALOOKUP w.open_fds f0 = SOME j0’ >>
  drule_all crel_other >> strip_tac >> drule crel_distinct >> strip_tac >>
  ‘0 < cread ∧ cread < 256 ** 8’ by simp[] >>
  qspecl_then [‘hs’, ‘hd0’, ‘f0’, ‘w’, ‘j0’, ‘cread’] mp_tac
    (Q.GENL [‘hs’, ‘hd’, ‘f’, ‘w’, ‘j’, ‘n’] ehdo_read) >> simp[] >>
  strip_tac >> mp_tac frame_core >> impl_tac >> simp[] >> gvs[]
QED


Theorem frame_write:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ EL k st.cs = CUp hd0 rest ∧
  ehdo lfd v (w, hs) (EWrite hd0 bs) = SOME (r, (w1, hs1)) ∧
  hd ≠ hd0 ∧ MEM hd (MAP FST hs.tbl) ⇒
  ALOOKUP hs1.tbl hd = ALOOKUP hs.tbl hd ∧ hstat (w1, hs1) hd = hstat (w, hs) hd
Proof
  strip_tac >> ‘MEM hd0 (chd (EL k st.cs))’ by simp[chd_def] >>
  drule_all crel_handle >> strip_tac >>
  rename1 ‘ALOOKUP hs.tbl hd0 = SOME f0’ >> rename1 ‘ALOOKUP w.open_fds f0 = SOME j0’ >>
  ‘(EL j0 w.chans).status = Up ∧ ¬(EL j0 w.chans).shut’
    by (qpat_x_assum ‘cok _ _ _ _ _ _’ mp_tac >> simp[cok_def]) >>
  drule crel_takes >> strip_tac >>
  drule_all crel_other >> strip_tac >> drule crel_distinct >> strip_tac >>
  ‘w1 = upd_chan j0 (λc. c with <| sent := c.sent ++ bs; inflight := c.inflight + LENGTH bs |>) w ∧
   hs1 = hs’
    by (qpat_x_assum ‘ehdo _ _ _ _ = SOME (r, (w1, hs1))’ mp_tac >>
        qspecl_then [‘hs’, ‘hd0’, ‘f0’, ‘w’, ‘j0’, ‘bs’, ‘lfd’, ‘v’] mp_tac
          (Q.GENL [‘hs’, ‘hd’, ‘f’, ‘w’, ‘j’, ‘bs’, ‘lfd’, ‘v’] ehdo_write_up) >>
        simp[] >> disch_then (fn th => simp[th])) >>
  ‘wframe j0 w w1 ∧ w1.open_fds = w.open_fds’ by simp[wframe_def, upd_chan_def, EL_LUPDATE] >>
  mp_tac frame_core >> impl_tac >> simp[]
QED

Theorem frame_connect:
  crel a N rqs lfd st rdyf ps w hs ∧ hs.nxt + 2 < dimword (:64) ∧
  ehdo lfd v (w, hs) (EConnect p) = SOME (r, (w1, hs1)) ∧ MEM hd (MAP FST hs.tbl) ⇒
  ALOOKUP hs1.tbl hd = ALOOKUP hs.tbl hd ∧ hstat (w1, hs1) hd = hstat (w, hs) hd
Proof
  strip_tac >> drule_all crel_other >> strip_tac >>
  qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_connect] >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[hstat_def, chan_status_def, ep_chan_of_def]) >>
  ‘hdln (w2n lfd) hs.nxt < dimword (:64)’
    by (‘hdln (w2n lfd) hs.nxt ≤ hs.nxt + 1’ by rw[hdln_def] >> fs[]) >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum ‘crel _ _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
  ‘hd ≠ hdl lfd hs.nxt’
    by (qpat_x_assum ‘∀hd. MEM hd (MAP FST hs.tbl) ⇔ _’ (qspec_then ‘hd’ mp_tac) >>
        simp[] >> strip_tac >>
        qpat_x_assum ‘∀i hd. i < N ∧ MEM hd (chd _) ⇒ ∃f j. _’ drule_all >> strip_tac >>
        ‘MEM hd (MAP FST st.hlc)’
          by (imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >> metis_tac[FST]) >>
        qpat_x_assum ‘∀hd. MEM hd (MAP FST st.hlc) ⇒ ∃k. _’ drule >> strip_tac >>
        gvs[] >> irule hdl_fresh >> simp[]) >>
  ‘¬MEM (w.alloc (LENGTH w.chans) (ep_used w)) (ep_used w)’ by fs[alloc_ok_def] >>
  ‘w.alloc (LENGTH w.chans) (ep_used w) ≠ f’
    by (strip_tac >> imp_res_tac ALOOKUP_MEM >> fs[ep_used_def, MEM_MAP] >>
        metis_tac[FST]) >>
  simp[eh_new_def, hstat_def, chan_status_def, ep_chan_of_def, EL_APPEND1]
QED

Theorem hstat_eq:
  ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ⇒
  hstat (w, hs) hd = SOME (EL j w.chans).status
Proof
  simp[hstat_def, chan_status_def, ep_chan_of_def]
QED

Theorem read_outcome:
  ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧
  ehdo lfd v (w, hs) (ERead hd cread) = SOME (r, st') ⇒
  (r = ERefused ⇔ (EL j w.chans).status = Refused) ∧
  (r = ERefused ∨ r = EGot (SOME []) ∨ r = EGot NONE ∨ ∃d. d ≠ [] ∧ r = EGot (SOME d))
Proof
  strip_tac >> ‘0 < cread ∧ cread < 256 ** 8’ by simp[] >>
  qspecl_then [‘hs’, ‘hd’, ‘f’, ‘w’, ‘j’, ‘cread’] mp_tac
    (Q.GENL [‘hs’, ‘hd’, ‘f’, ‘w’, ‘j’, ‘n’] ehdo_read) >> simp[] >>
  strip_tac >> gvs[] >> simp[TAKE_EQ_NIL, cread_def]
QED

(* What one round does to one connection: c its state before, c' after; stat
   the layer's channel status of a handle at the round's start; rd the
   handles reported ready; qs the round's (action, result) pairs *)
Definition ctr_def:
  ctr (b : word8 list) c c' (stat : word64 -> cstatus option) (rd : word64 set) qs ⇔
    case c of
    | CIdle => c' = CIdle ∨ ∃hd. c' = CPend hd
    | CPend hd =>
        hl_sent hd qs = [] ∧
        (hd ∉ rd ⇒ c' = c) ∧
        (hd ∈ rd ⇒ c' = CIdle ∧ stat hd = SOME Refused ∨
                   stat hd ≠ SOME Refused ∧ (c' = CDone ∧ hl_eof hd qs ∨ ∃r. c' = CUp hd r))
    | CUp hd rest => ((∃r. c' = CUp hd r) ∨ c' = CDone ∧ hl_eof hd qs) ∧ hl_sent hd qs = rest
    | CDone => c' = CDone
End

Theorem ehacts_one_eq:
  ehacts lfd lv n ix st [x] = SOME (rs, st1) ⇔
  ∃r. ehdo lfd (lv n ix) st x = SOME (r, st1) ∧ rs = [r]
Proof
  simp[ehacts_def] >> Cases_on ‘ehdo lfd (lv n ix) st x’ >> simp[] >>
  rename1 ‘ehdo _ _ _ _ = SOME q’ >> PairCases_on ‘q’ >> simp[ehacts_def] >> metis_tac[]
QED

Theorem ehacts_two_eq:
  ehacts lfd lv n ix st [x; y] = SOME (rs, st2) ⇔
  ∃r r' st1. ehdo lfd (lv n ix) st x = SOME (r, st1) ∧
             ehdo lfd (lv n (ix + 1)) st1 y = SOME (r', st2) ∧ rs = [r; r']
Proof
  simp[ehacts_def] >> Cases_on ‘ehdo lfd (lv n ix) st x’ >> simp[] >>
  rename1 ‘ehdo _ _ _ x = SOME q’ >> PairCases_on ‘q’ >> simp[] >>
  Cases_on ‘ehdo lfd (lv n (ix + 1)) (q1, q2) y’ >> simp[ehacts_def] >>
  rename1 ‘ehdo _ _ _ y = SOME q'’ >> PairCases_on ‘q'’ >> simp[ehacts_def] >> metis_tac[]
QED

Theorem trans_pend_read:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ EL k st.cs = CPend hd ∧
  ehdo lfd v (w, hs) (ERead hd cread) = SOME (r, st') ⇒
  cres b (CPend hd) (ERead hd cread) r = CIdle ∧ hstat (w, hs) hd = SOME Refused ∨
  hstat (w, hs) hd ≠ SOME Refused ∧
  (cres b (CPend hd) (ERead hd cread) r = CDone ∧ r = EGot (SOME []) ∨
   ∃x. cres b (CPend hd) (ERead hd cread) r = CUp hd x)
Proof
  strip_tac >> ‘MEM hd (chd (EL k st.cs))’ by simp[chd_def] >>
  drule_all crel_handle >> strip_tac >> drule_all hstat_eq >> strip_tac >>
  drule_all read_outcome >> strip_tac >> gvs[cres_def] >> Cases_on ‘d’ >> gvs[]
QED

Theorem trans_up_read:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ EL k st.cs = CUp hd rest ∧
  ehdo lfd v (w, hs) (ERead hd cread) = SOME (r, st') ⇒
  cres b (CUp hd rest) (ERead hd cread) r = CUp hd rest ∨
  cres b (CUp hd rest) (ERead hd cread) r = CDone ∧ r = EGot (SOME [])
Proof
  strip_tac >> ‘MEM hd (chd (EL k st.cs))’ by simp[chd_def] >>
  drule_all crel_handle >> strip_tac >>
  ‘(EL j w.chans).status = Up’ by (qpat_x_assum ‘cok _ _ _ _ _ _’ mp_tac >> simp[cok_def]) >>
  drule_all read_outcome >> strip_tac >> gvs[cres_def] >> Cases_on ‘d’ >> gvs[]
QED

Theorem write_result:
  rest ≠ [] ∧ cres b (CUp hd rest) (EWrite hd rest) r = CUp hd [] ⇒
  hl_sent hd [(EWrite hd rest, r)] = rest
Proof
  Cases_on ‘r’ >> simp[cres_def] >> rw[] >> gvs[DROP_NIL] >> simp[TAKE_LENGTH_TOO_LONG]
QED

Theorem conn_ctr:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ N < dimword (:64) ∧
  (nh0 < cbound ⇒ st.nh + 2 < dimword (:64)) ∧
  ehacts lfd lv n ix (w, hs) (cact1 a nh0 (EL k st.cs) (rdyf k)) = SOME (rs, (w1, hs1)) ⇒
  ctr (brequests (rqs k)) (EL k st.cs)
    (EL k (cupd rqs st (MAP (λx. (k, x)) (cact1 a nh0 (EL k st.cs) (rdyf k))) rs).cs)
    (hstat (w, hs)) (rdyf k) (ZIP (cact1 a nh0 (EL k st.cs) (rdyf k), rs))
Proof
  strip_tac >> ‘LENGTH st.cs = N’ by fs[crel_def] >>
  Cases_on ‘EL k st.cs’ >> fs[cact1_def] >> simp[ctr_def]
  (* CIdle *)
  >- (Cases_on ‘nh0 < cbound’ >> fs[ehacts_one_eq] >> fs[ehacts_def] >> gvs[cupd_def, EL_LUPDATE] >>
      Cases_on ‘r’ >> simp[cres_def] >> rename1 ‘EConnected oh’ >> Cases_on ‘oh’ >> simp[])
  (* CPend *)
  >- (rename1 ‘EL k st.cs = CPend hd’ >>
      Cases_on ‘hd ∈ rdyf k’ >> fs[ehacts_one_eq] >> fs[ehacts_def] >> gvs[cupd_def, EL_LUPDATE] >>
      drule_all trans_pend_read >> disch_then (qspec_then ‘brequests (rqs k)’ strip_assume_tac) >>
      Cases_on ‘r’ >> fs[] >> metis_tac[])
  (* CUp *)
  >- (rename1 ‘EL k st.cs = CUp hd rest’ >>
  Cases_on ‘rest = []’ >> fs[]
  >- (Cases_on ‘hd ∈ rdyf k’ >> fs[ehacts_one_eq] >> fs[ehacts_def] >> gvs[cupd_def, EL_LUPDATE] >>
      drule_all trans_up_read >> disch_then (qspec_then ‘brequests (rqs k)’ strip_assume_tac) >>
      Cases_on ‘r’ >> fs[] >> metis_tac[]) >>
  drule_all crel_write >> disch_then (qspec_then ‘lv n ix’ strip_assume_tac) >>
  Cases_on ‘hd ∈ rdyf k’ >> fs[ehacts_one_eq, ehacts_two_eq] >> gvs[]
  >- (qabbrev_tac ‘st1 = cupd rqs st [(k, EWrite hd rest)] [r]’ >>
      ‘crel a (LENGTH st.cs) rqs lfd st1 rdyf (ps ++ [(EWrite hd rest, r)]) w1' hs1' ∧
       EL k st1.cs = CUp hd [] ∧ k < LENGTH st.cs’ by simp[Abbr ‘st1’] >>
      qspecl_then [‘a’, ‘LENGTH st.cs’, ‘st1’, ‘ps ++ [(EWrite hd rest, r)]’, ‘w1'’, ‘hs1'’, ‘[]’,
                   ‘lv n (ix + 1)’, ‘r''’, ‘(w1, hs1)’, ‘brequests (rqs k)’] mp_tac
        (Q.GENL [‘a’, ‘N’, ‘st’, ‘ps’, ‘w’, ‘hs’, ‘rest’, ‘v’, ‘r’, ‘st'’, ‘b’] trans_up_read) >>
      impl_tac >- simp[] >> strip_tac >>
      ‘cupd rqs st [(k, EWrite hd rest); (k, ERead hd cread)] [r; r''] =
       cupd rqs st1 [(k, ERead hd cread)] [r'']’
        by (qunabbrev_tac ‘st1’ >> simp_tac (srw_ss()) [cupd_def]) >>
      pop_assum (fn th => REWRITE_TAC [th]) >>
      ‘hl_sent hd [(EWrite hd rest, r)] = rest’
        by (irule write_result >> conj_tac >- simp[] >> qexists_tac ‘brequests (rqs k)’ >>
            qpat_x_assum ‘EL k (LUPDATE _ _ _) = _’ mp_tac >> simp[EL_LUPDATE]) >>
      ‘hl_sent hd [(EWrite hd rest, r); (ERead hd cread, r'')] = rest’
        by (‘[(EWrite hd rest, r); (ERead hd cread, r'')] =
             [(EWrite hd rest, r)] ++ [(ERead hd cread, r'')]’ by simp[] >>
            pop_assum SUBST1_TAC >> simp_tac std_ss [hl_APPEND] >> simp[] >> Cases_on ‘r''’ >> simp[]) >>
      ‘k < LENGTH st1.cs’ by simp[Abbr ‘st1’] >>
      simp[EL_LUPDATE] >> fs[] >>
      ‘hl_eof hd [(EWrite hd rest, r); (ERead hd cread, EGot (SOME []))]’
        by simp[hl_eof_def] >> simp[Abbr ‘st1’]) >>
  ‘hl_sent hd [(EWrite hd rest, r)] = rest’
    by (irule write_result >> conj_tac >- simp[] >> qexists_tac ‘brequests (rqs k)’ >>
            qpat_x_assum ‘EL k (LUPDATE _ _ _) = _’ mp_tac >> simp[EL_LUPDATE]) >>
  fs[EL_LUPDATE])
  (* CDone *)
  >> gvs[ehacts_def, cupd_def]
QED

Theorem frame_read_core:
  ALOOKUP hs.tbl hd0 = SOME f0 ∧ ALOOKUP w.open_fds f0 = SOME j0 ∧ j0 < LENGTH w.chans ∧
  ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧
  hd ≠ hd0 ∧ ALL_DISTINCT (MAP SND hs.tbl) ∧ ALL_DISTINCT (MAP SND w.open_fds) ∧
  ehdo lfd v (w, hs) (ERead hd0 cread) = SOME (r, (w1, hs1)) ⇒
  ALOOKUP hs1.tbl hd = SOME f ∧ hstat (w1, hs1) hd = hstat (w, hs) hd
Proof
  strip_tac >> ‘0 < cread ∧ cread < 256 ** 8’ by simp[] >>
  qspecl_then [‘hs’, ‘hd0’, ‘f0’, ‘w’, ‘j0’, ‘cread’] mp_tac
    (Q.GENL [‘hs’, ‘hd’, ‘f’, ‘w’, ‘j’, ‘n’] ehdo_read) >> simp[] >>
  strip_tac >> mp_tac frame_core >> impl_tac >> simp[] >> gvs[]
QED

Theorem write_eq:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ EL k st.cs = CUp hd0 rest ∧
  ehdo lfd v (w, hs) (EWrite hd0 bs) = SOME (r, (w1, hs1)) ⇒
  hs1 = hs ∧ w1.open_fds = w.open_fds ∧ LENGTH w1.chans = LENGTH w.chans
Proof
  strip_tac >> ‘MEM hd0 (chd (EL k st.cs))’ by simp[chd_def] >>
  drule_all crel_handle >> strip_tac >>
  rename1 ‘ALOOKUP hs.tbl hd0 = SOME f0’ >> rename1 ‘ALOOKUP w.open_fds f0 = SOME j0’ >>
  ‘(EL j0 w.chans).status = Up ∧ ¬(EL j0 w.chans).shut’
    by (qpat_x_assum ‘cok _ _ _ _ _ _’ mp_tac >> simp[cok_def]) >>
  drule crel_takes >> strip_tac >>
  qpat_x_assum ‘ehdo _ _ _ _ = SOME (r, (w1, hs1))’ mp_tac >>
  qspecl_then [‘hs’, ‘hd0’, ‘f0’, ‘w’, ‘j0’, ‘bs’, ‘lfd’, ‘v’] mp_tac
    (Q.GENL [‘hs’, ‘hd’, ‘f’, ‘w’, ‘j’, ‘bs’, ‘lfd’, ‘v’] ehdo_write_up) >>
  simp[] >> disch_then (fn th => simp[th]) >> strip_tac >> gvs[upd_chan_def]
QED

Theorem conn_frame:
  crel a N rqs lfd st rdyf ps w hs ∧ k < N ∧ N < dimword (:64) ∧
  (nh0 < cbound ⇒ st.nh + 2 < dimword (:64)) ∧
  ehacts lfd lv n ix (w, hs) (cact1 a nh0 (EL k st.cs) (rdyf k)) = SOME (rs, (w1, hs1)) ∧
  ¬MEM hd (chd (EL k st.cs)) ∧ MEM hd (MAP FST hs.tbl) ⇒
  ALOOKUP hs1.tbl hd = ALOOKUP hs.tbl hd ∧ hstat (w1, hs1) hd = hstat (w, hs) hd
Proof
  strip_tac >> ‘LENGTH st.cs = N ∧ st.nh = hs.nxt’ by fs[crel_def] >>
  Cases_on ‘EL k st.cs’ >> fs[cact1_def, chd_def]
  (* CIdle *)
  >- (Cases_on ‘nh0 < cbound’ >> fs[ehacts_one_eq] >> fs[ehacts_def] >>
      ‘hs.nxt + 2 < dimword (:64)’ by gvs[] >>
      drule_all frame_connect >> simp[])
  (* CPend *)
  >- (rename1 ‘EL k st.cs = CPend h0’ >> ‘MEM h0 (chd (EL k st.cs))’ by simp[chd_def] >>
      Cases_on ‘h0 ∈ rdyf k’ >> fs[ehacts_one_eq] >> fs[ehacts_def] >>
      ‘hd ≠ h0’ by (strip_tac >> gvs[]) >> drule_all frame_read >> simp[])
  (* CUp *)
  >- (rename1 ‘EL k st.cs = CUp h0 rest’ >> ‘MEM h0 (chd (EL k st.cs))’ by simp[chd_def] >>
      ‘hd ≠ h0’ by (strip_tac >> gvs[]) >>
      Cases_on ‘rest = []’ >> fs[]
      >- (Cases_on ‘h0 ∈ rdyf k’ >> fs[ehacts_one_eq] >> fs[ehacts_def] >>
          drule_all frame_read >> simp[]) >>
      Cases_on ‘h0 ∈ rdyf k’ >> fs[ehacts_one_eq, ehacts_two_eq]
      >- (rename1 ‘ehdo _ _ (w, hs) (EWrite h0 rest) = SOME (r1, st1)’ >> PairCases_on ‘st1’ >>
          drule_all frame_write >> strip_tac >>
          drule_all write_eq >> strip_tac >> gvs[] >>
          ‘MEM h0 (chd (EL k st.cs))’ by simp[chd_def] >>
          drule_all crel_handle >> strip_tac >>
          drule_all crel_other >> strip_tac >> drule crel_distinct >> strip_tac >>
          qspecl_then [‘hs’, ‘h0’, ‘f’, ‘st10’, ‘j’, ‘hd’, ‘f'’, ‘j'’, ‘lv n (ix + 1)’, ‘r'’, ‘w1’, ‘hs1’]
            mp_tac (Q.GENL [‘hs’, ‘hd0’, ‘f0’, ‘w’, ‘j0’, ‘hd’, ‘f’, ‘j’, ‘v’, ‘r’, ‘w1’, ‘hs1’]
                      frame_read_core) >> simp[]) >>
      drule_all frame_write >> simp[])
  (* CDone *)
  >> fs[ehacts_def]
QED

Theorem ehacts_APPEND_inv:
  ∀xs k st rs st2. ehacts lfd lv n k st (xs ++ ys) = SOME (rs, st2) ⇒
    ∃rs1 rs2 st1. ehacts lfd lv n k st xs = SOME (rs1, st1) ∧
                  ehacts lfd lv n (k + LENGTH xs) st1 ys = SOME (rs2, st2) ∧ rs = rs1 ++ rs2
Proof
  Induct >> simp[ehacts_def] >> rw[] >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >> gvs[ADD1] >> metis_tac[]
QED

Theorem ctr_stat:
  ctr b c c' s rd qs ∧ (∀hd. MEM hd (chd c) ⇒ s' hd = s hd) ⇒ ctr b c c' s' rd qs
Proof
  Cases_on ‘c’ >> simp[ctr_def, chd_def]
QED

Theorem ctr_qs:
  ctr b c c' s rd qs ∧
  (∀hd. MEM hd (chd c) ⇒ hl_sent hd qs2 = hl_sent hd qs ∧ (hl_eof hd qs ⇒ hl_eof hd qs2)) ⇒
  ctr b c c' s rd qs2
Proof
  Cases_on ‘c’ >> simp[ctr_def, chd_def] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem hl_sent_nowrite:
  (∀bs r. ¬MEM (EWrite hd bs, r) qs) ⇒ hl_sent hd qs = []
Proof
  Induct_on ‘qs’ >> simp[hl_sent_def, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
  ‘hl_sent hd qs = []’ by (first_x_assum irule >> metis_tac[]) >>
  fs[hl_sent_def] >> Cases_on ‘p_1’ >> Cases_on ‘p_2’ >> simp[] >> rw[] >> metis_tac[]
QED

Theorem cact1_write:
  MEM (EWrite hd bs) (cact1 a nh c rd) ⇒ MEM hd (chd c)
Proof
  Cases_on ‘c’ >> rw[cact1_def, chd_def]
QED

Theorem cacts_upto_write:
  MEM (EWrite hd bs) (MAP SND (cacts_upto a st0 rdy m)) ⇒
  ∃i. i < m ∧ MEM hd (chd (EL i st0.cs))
Proof
  simp[cacts_upto_def, MEM_MAP, MEM_FLAT, MEM_GENLIST, PULL_EXISTS] >> rw[] >>
  qexists_tac ‘i’ >> simp[] >> irule cact1_write >> gvs[] >> metis_tac[]
QED



Theorem cupd_other:
  ∀xs rs st. EVERY (λ(j, x). j ≠ i) xs ⇒ EL i (cupd rqs st xs rs).cs = EL i st.cs
Proof
  Induct >> simp[cupd_def] >> rpt gen_tac >> PairCases_on ‘h’ >> Cases_on ‘rs’ >>
  simp[cupd_def] >> strip_tac >> simp[EL_LUPDATE]
QED

Theorem hl_sent_prefix:
  (∀i. i < m ⇒ ¬MEM hd (chd (EL i st0.cs))) ⇒
  hl_sent hd (ZIP (MAP SND (cacts_upto a st0 rdy m), rs)) = []
Proof
  strip_tac >> irule hl_sent_nowrite >> rpt strip_tac >> imp_res_tac MEM_ZIP_FST >>
  imp_res_tac cacts_upto_write >> metis_tac[]
QED

Theorem hl_sent_block:
  ¬MEM hd (chd c) ⇒ hl_sent hd (ZIP (cact1 a nh c rd, rs)) = []
Proof
  strip_tac >> irule hl_sent_nowrite >> rpt strip_tac >> imp_res_tac MEM_ZIP_FST >>
  imp_res_tac cact1_write
QED

Theorem acts_trans:
  crel a N rqs lfd st0 (K rdy) ps w hs ∧ N < dimword (:64) ∧
  (st0.nh < cbound ⇒ st0.nh + N + 1 < dimword (:64)) ⇒
  ∀m rs w1 hs1. m ≤ N ∧
    ehacts lfd lv n 0 (w, hs) (MAP SND (cacts_upto a st0 rdy m)) = SOME (rs, (w1, hs1)) ⇒
    (∀i. i < m ⇒
       ctr (brequests (rqs i)) (EL i st0.cs) (EL i (cupd rqs st0 (cacts_upto a st0 rdy m) rs).cs)
         (hstat (w, hs)) rdy (ZIP (MAP SND (cacts_upto a st0 rdy m), rs))) ∧
    (∀hd. (∀i. i < m ∧ MEM hd (chd (EL i st0.cs)) ⇒ cact1 a st0.nh (EL i st0.cs) rdy = []) ∧
          MEM hd (MAP FST hs.tbl) ⇒
       ALOOKUP hs1.tbl hd = ALOOKUP hs.tbl hd ∧ hstat (w1, hs1) hd = hstat (w, hs) hd)
Proof
  strip_tac >> Induct
  >- simp[cacts_upto_def, ehacts_def] >>
  rpt gen_tac >> strip_tac >> ‘m < N’ by simp[] >>
  qabbrev_tac ‘A = cacts_upto a st0 rdy m’ >>
  qabbrev_tac ‘xs = cact1 a st0.nh (EL m st0.cs) rdy’ >>
  ‘cacts_upto a st0 rdy (SUC m) = A ++ MAP (λx. (m, x)) xs’
    by simp[Abbr ‘A’, Abbr ‘xs’, cacts_upto_SUC] >>
  ‘MAP SND (A ++ MAP (λx. (m, x)) xs) = MAP SND A ++ xs’
    by simp[MAP_MAP_o, combinTheory.o_DEF] >>
  fs[] >>
  drule ehacts_APPEND_inv >> strip_tac >> rename1 ‘_ = SOME (rs1, stm)’ >>
  PairCases_on ‘stm’ >> rename1 ‘_ = SOME (rs1, (wm, hsm))’ >>
  first_x_assum drule >> strip_tac >>
  drule crel_acts >> simp[] >> disch_then (qspecl_then [‘n’, ‘lv’, ‘m’] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  qabbrev_tac ‘stm = cupd rqs st0 A rs1’ >>
  ‘EL m stm.cs = EL m st0.cs’ by simp[] >>
  qabbrev_tac ‘rdm = λi. if i < m then ∅ else rdy’ >>
  ‘rdm m = rdy’ by simp[Abbr ‘rdm’] >>
  ‘ehacts lfd lv n (LENGTH (MAP SND A)) (wm, hsm) (cact1 a st0.nh (EL m stm.cs) (rdm m)) =
   SOME (rs2, (w1, hs1))’ by fs[Abbr ‘xs’] >>
  ‘st0.nh < cbound ⇒ stm.nh + 2 < dimword (:64)’ by simp[] >>
  ‘crel a N rqs lfd stm rdm (ps ++ ZIP (MAP SND A, rs1)) wm hsm’ by simp[Abbr ‘rdm’] >>
  qspecl_then [‘stm’, ‘rdm’, ‘ps ++ ZIP (MAP SND A, rs1)’, ‘wm’, ‘hsm’, ‘m’, ‘st0.nh’,
               ‘LENGTH (MAP SND A)’, ‘rs2’, ‘w1’, ‘hs1’] mp_tac
    (Q.GENL [‘st’, ‘rdyf’, ‘ps’, ‘w’, ‘hs’, ‘k’, ‘nh0’, ‘ix’, ‘rs’, ‘w1’, ‘hs1’] conn_ctr) >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [‘stm’, ‘rdm’, ‘ps ++ ZIP (MAP SND A, rs1)’, ‘wm’, ‘hsm’, ‘m’, ‘st0.nh’,
               ‘LENGTH (MAP SND A)’, ‘rs2’, ‘w1’, ‘hs1’] assume_tac
    (Q.GENL [‘st’, ‘rdyf’, ‘ps’, ‘w’, ‘hs’, ‘k’, ‘nh0’, ‘ix’, ‘rs’, ‘w1’, ‘hs1’, ‘hd’] conn_frame) >>
  ‘cact1 a st0.nh (EL m stm.cs) (rdm m) = xs’ by simp[Abbr ‘xs’] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qpat_x_assum ‘EL m stm.cs = EL m st0.cs’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qpat_x_assum ‘rdm m = rdy’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  ‘cupd rqs st0 (A ++ MAP (λx. (m, x)) xs) (rs1 ++ rs2) = cupd rqs stm (MAP (λx. (m, x)) xs) rs2’
    by (qunabbrev_tac ‘stm’ >> irule cupd_APPEND >> simp[]) >>
  ‘ZIP (MAP SND A ++ xs, rs1 ++ rs2) = ZIP (MAP SND A, rs1) ++ ZIP (xs, rs2)’
    by (‘LENGTH rs2 = LENGTH xs’ by metis_tac[ehacts_LENGTH] >> simp[ZIP_APPEND]) >>
  ntac 2 (pop_assum (fn th => REWRITE_TAC [th])) >>
  ‘(∀i1 i2 hd. i1 < N ∧ i2 < N ∧ MEM hd (chd (EL i1 st0.cs)) ∧ MEM hd (chd (EL i2 st0.cs)) ⇒
               i1 = i2) ∧
   (∀hd. MEM hd (MAP FST hs.tbl) ⇔ ∃i. i < N ∧ MEM hd (chd (EL i st0.cs)))’
    by (qpat_x_assum ‘crel _ _ _ _ st0 _ _ _ _’ (strip_assume_tac o REWRITE_RULE [crel_def]) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on ‘i = m’
      >- (qpat_x_assum ‘i = m’ SUBST_ALL_TAC >>
          irule ctr_qs >> qexists_tac ‘ZIP (xs, rs2)’ >> rpt conj_tac >>
          TRY (irule ctr_stat >> qexists_tac ‘hstat (wm, hsm)’ >> simp[] >>
               rpt strip_tac >>
               qpat_x_assum ‘∀hd. (∀i. i < m ∧ _ ⇒ _) ∧ _ ⇒ _’ (qspec_then ‘hd’ mp_tac) >>
               impl_tac
               >- (conj_tac
                   >- (rpt strip_tac >> ‘i < N’ by simp[] >> ‘i = m’ by (qpat_x_assum ‘∀i1 i2 hd. _ ⇒ i1 = i2’ irule >> simp[] >> qexists_tac ‘hd’ >> simp[]) >> fs[]) >>
                   qpat_x_assum ‘∀hd. MEM hd (MAP FST hs.tbl) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
                   qexists_tac ‘m’ >> simp[]) >>
               simp[] >> NO_TAC) >>
          rpt strip_tac >> simp[] >>
          ‘hl_sent hd (ZIP (MAP SND A, rs1)) = []’
            by (simp[Abbr ‘A’] >> irule hl_sent_prefix >> rpt strip_tac >>
                ‘i < N’ by simp[] >> ‘i = m’ by (qpat_x_assum ‘∀i1 i2 hd. _ ⇒ i1 = i2’ irule >> simp[] >> qexists_tac ‘hd’ >> simp[]) >> fs[]) >> simp[]) >>
      ‘i < m’ by simp[] >>
      ‘EL i (cupd rqs stm (MAP (λx. (m, x)) xs) rs2).cs = EL i stm.cs’
        by (irule cupd_other >> simp[EVERY_MAP]) >> simp[] >>
      irule ctr_qs >> qexists_tac ‘ZIP (MAP SND A, rs1)’ >> simp[] >> rpt strip_tac >>
      ‘hl_sent hd (ZIP (xs, rs2)) = []’
        by (simp[Abbr ‘xs’] >> irule hl_sent_block >> strip_tac >>
            ‘i < N’ by simp[] >> ‘i = m’ by (qpat_x_assum ‘∀i1 i2 hd. _ ⇒ i1 = i2’ irule >> simp[] >> qexists_tac ‘hd’ >> simp[]) >> fs[]) >> simp[]) >>
  rpt strip_tac >>
  ‘ALOOKUP hsm.tbl hd = ALOOKUP hs.tbl hd ∧ hstat (wm, hsm) hd = hstat (w, hs) hd’
    by (qpat_x_assum ‘∀hd. (∀i. i < m ∧ _ ⇒ _) ∧ _ ⇒ _’ (qspec_then ‘hd’ mp_tac) >>
        impl_tac
        >- (conj_tac >- (rpt strip_tac >> qpat_x_assum ‘∀i. i < SUC m ∧ _ ⇒ _’ irule >> simp[]) >>
            first_assum ACCEPT_TAC) >>
        simp[]) >>
  Cases_on ‘MEM hd (chd (EL m st0.cs))’ >>
  TRY (‘xs = []’
         by (simp[Abbr ‘xs’] >> qpat_x_assum ‘∀i. i < SUC m ∧ _ ⇒ _’ irule >> simp[]) >>
       ‘w1 = wm ∧ hs1 = hsm’
         by (qpat_x_assum ‘ehacts _ _ _ (LENGTH (MAP SND A)) _ _ = _’ mp_tac >>
             simp[ehacts_def]) >>
       simp[] >> NO_TAC) >>
  ‘MEM hd (MAP FST hsm.tbl)’
    by (qpat_x_assum ‘ALOOKUP hsm.tbl hd = _’ mp_tac >>
        qpat_x_assum ‘MEM hd (MAP FST hs.tbl)’ mp_tac >> rpt (pop_assum kall_tac) >>
        rpt strip_tac >> Cases_on ‘ALOOKUP hs.tbl hd’ >> gvs[ALOOKUP_NONE] >>
        imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >> metis_tac[FST]) >>
  ‘ALOOKUP hs1.tbl hd = ALOOKUP hsm.tbl hd ∧ hstat (w1, hs1) hd = hstat (wm, hsm) hd’
    by (qpat_x_assum ‘∀hd. crel _ _ _ _ _ _ _ _ _ ∧ _ ⇒ _’ irule >> simp[]) >>
  simp[]
QED

(* The poll, for a handle in the interest *)
Theorem poll_keep:
  ehpoll lfd hs1 hfds w1 = (rdy', w2, hs2) ∧
  ALOOKUP hs1.tbl hd = SOME f ∧ ALOOKUP w1.open_fds f = SOME j ∧ j < LENGTH w1.chans ∧
  MEM hd hfds ⇒
  ALOOKUP hs2.tbl hd = SOME f ∧
  (hstat (w1, hs1) hd ≠ SOME Connecting ⇒ hstat (w2, hs2) hd = hstat (w1, hs1) hd) ∧
  (hstat (w2, hs2) hd ≠ SOME Connecting ⇒ ¬MEM hd hs2.settling)
Proof
  strip_tac >> qpat_x_assum ‘ehpoll _ _ _ _ = _’ mp_tac >> simp[ehpoll_def] >> strip_tac >>
  ‘tick_rel w1 w2’ by (gvs[] >> simp[tick_rel_tick]) >>
  pop_assum (strip_assume_tac o REWRITE_RULE [tick_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  gvs[hstat_def, chan_status_def, ep_chan_of_def, MEM_FILTER]
QED

Theorem hstat_SOME:
  hstat (w, hs) hd = SOME s ⇒
  ∃f j. ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧
        s = (EL j w.chans).status
Proof
  simp[hstat_def, chan_status_def, ep_chan_of_def, AllCaseEqs()] >> rw[] >> simp[]
QED

(* One round of the run, for connection i *)
Theorem cround_trans:
  client_world lfd c w0 ∧ N < cbound ∧ i < N ⇒
  ∃qs. hl_pairs (cprog a N rqs) (cH a N rqs lfd lv w0 (SUC n)) =
       hl_pairs (cprog a N rqs) (cH a N rqs lfd lv w0 n) ++ qs ∧
     ctr (brequests (rqs i)) (EL i (cst a N rqs lfd lv w0 n).cs)
       (EL i (cst a N rqs lfd lv w0 (SUC n)).cs) (hstat (cS a N rqs lfd lv w0 n))
       (crdy (cH a N rqs lfd lv w0 n)) qs ∧
     ∀hd. EL i (cst a N rqs lfd lv w0 n).cs = CPend hd ∧
          EL i (cst a N rqs lfd lv w0 (SUC n)).cs = CPend hd ⇒
          ALOOKUP (SND (cS a N rqs lfd lv w0 (SUC n))).tbl hd =
            ALOOKUP (SND (cS a N rqs lfd lv w0 n)).tbl hd ∧
          (hstat (cS a N rqs lfd lv w0 n) hd ≠ SOME Connecting ⇒
           hstat (cS a N rqs lfd lv w0 (SUC n)) hd = hstat (cS a N rqs lfd lv w0 n) hd) ∧
          (hstat (cS a N rqs lfd lv w0 (SUC n)) hd ≠ SOME Connecting ⇒
           ¬MEM hd (SND (cS a N rqs lfd lv w0 (SUC n))).settling)
Proof
  strip_tac >> drule_all cinv_all >> disch_then (qspecl_then [‘a’, ‘rqs’, ‘lv’, ‘n’] mp_tac) >>
  qmatch_goalsub_abbrev_tac ‘ehst lfd lv ifds m w0 n’ >>
  simp[cinv_def] >> strip_tac >>
  qabbrev_tac ‘h = ehhist lfd lv ifds m w0 n’ >>
  qabbrev_tac ‘st = cstate a N rqs h’ >>
  Cases_on ‘ehst lfd lv ifds m w0 n’ >> rename1 ‘_ = (w, hs)’ >> fs[] >>
  ‘new_actions (log_of m) h = MAP SND st.last’ by simp[Abbr ‘m’, Abbr ‘st’, cprog_new_actions] >>
  Cases_on ‘ehacts_tot lfd lv n (w, hs) (MAP SND st.last)’ >> rename1 ‘_ = (rs, st1)’ >>
  PairCases_on ‘st1’ >> rename1 ‘_ = (rs, (w1, hs1))’ >>
  Cases_on ‘ehpoll lfd hs1 (ifds h) w1’ >> rename1 ‘_ = (rdy', r2)’ >>
  PairCases_on ‘r2’ >> rename1 ‘_ = (rdy', w2, hs2)’ >>
  ‘ehhist lfd lv ifds m w0 (SUC n) = h ++ [ssnap rdy' rs] ∧
   ehst lfd lv ifds m w0 (SUC n) = (w2, hs2)’
    by (qunabbrev_tac ‘h’ >> irule honestL1EPRefineTheory.ehround_step >> gvs[]) >>
  ‘st.nh < cbound + N’ by simp[] >>
  drule_all crel_round >> strip_tac >>
  simp[cstate_SNOC, hl_pairs_SNOC, cstep_def, asyncM3WorldTheory.ssnap_def] >>
  ‘LENGTH st.cs = N’ by fs[crel_def] >>
  ‘cacts a st (crdy h) = cacts_upto a st (crdy h) N’ by simp[cacts_upto_all] >>
  pop_assum (fn th => REWRITE_TAC [th] >> RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  ‘N < dimword (:64) ∧ (st.nh < cbound ⇒ st.nh + N + 1 < dimword (:64))’ by fs[cbound_def] >>
  qpat_x_assum ‘st.last = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qspecl_then [‘st’, ‘crdy h’, ‘hl_pairs m h’, ‘w’, ‘hs’, ‘lv’, ‘n’] mp_tac
    (Q.GENL [‘st0’, ‘rdy’, ‘ps’, ‘w’, ‘hs’, ‘lv’, ‘n’] acts_trans) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [‘N’, ‘rs’, ‘w1’, ‘hs1’] mp_tac) >> impl_tac >- simp[] >>
  strip_tac >> conj_tac >- (first_x_assum irule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  ‘hd ∉ crdy h’
    by (strip_tac >> qpat_x_assum ‘∀i. i < N ⇒ ctr _ _ _ _ _ _’ (qspec_then ‘i’ mp_tac) >>
        simp[ctr_def]) >>
  ‘MEM hd (chd (EL i st.cs))’ by simp[chd_def] >>
  qpat_x_assum ‘crel _ _ _ _ st _ _ _ _’ (fn th => assume_tac th >>
    strip_assume_tac (REWRITE_RULE [crel_def] th)) >>
  ‘MEM hd (MAP FST hs.tbl)’ by metis_tac[] >>
  ‘ALOOKUP hs1.tbl hd = ALOOKUP hs.tbl hd ∧ hstat (w1, hs1) hd = hstat (w, hs) hd’
    by (qpat_x_assum ‘∀hd. (∀i. i < N ∧ _ ⇒ _) ∧ _ ⇒ _’ irule >> simp[] >> rpt strip_tac >>
        ‘i' = i’ by (qpat_x_assum ‘∀i1 i2 hd. _ ⇒ i1 = i2’ irule >> simp[] >>
                     qexists_tac ‘hd’ >> simp[chd_def]) >>
        gvs[cact1_def]) >>
  drule_all crel_handle >> strip_tac >>
  drule_all hstat_eq >> strip_tac >>
  ‘∃s. hstat (w1, hs1) hd = SOME s’ by simp[] >>
  drule hstat_SOME >> strip_tac >>
  ‘MEM hd (ifds h)’
    by (simp[Abbr ‘ifds’, cifds_def, MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM]) >>
  drule_all poll_keep >> strip_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   Liveness: the argument
   ------------------------------------------------------------------------ *)

Theorem hstat_pair:
  hstat p hd = case ALOOKUP (SND p).tbl hd of SOME f => chan_status (FST p) f | NONE => NONE
Proof
  Cases_on ‘p’ >> simp[hstat_def]
QED

Theorem up_at_hstat:
  up_at lfd lv ifds m w0 n hd ⇔ hstat (ehst lfd lv ifds m w0 n) hd = SOME Up
Proof
  simp[up_at_def, hstat_pair] >> CASE_TAC >> simp[]
QED

Theorem cst_0:
  i < N ⇒ EL i (cst a N rqs lfd lv w0 0).cs = CIdle
Proof
  simp[ehhist_def, ehrounds_def, cstate_def, cinit_def, EL_REPLICATE]
QED

Theorem crel_pend:
  crel a N rqs lfd st rdyf ps w hs ∧ i < N ∧ EL i st.cs = CPend hd ⇒
  ∃s. hstat (w, hs) hd = SOME s ∧
      (s = Connecting ∧ MEM hd hs.settling ∧ hd ∉ rdyf i ∨
       (s = Up ∨ s = Refused) ∧ (MEM hd hs.settling ∨ hd ∈ rdyf i)) ∧
      hl_sent hd ps = [] ∧ ALOOKUP st.hlc hd = SOME i ∧ MEM hd (MAP FST hs.tbl) ∧
      ∃f. ALOOKUP hs.tbl hd = SOME f
Proof
  strip_tac >> ‘MEM hd (chd (EL i st.cs))’ by simp[chd_def] >>
  drule_all crel_handle >> strip_tac >> drule_all hstat_eq >> strip_tac >>
  ‘MEM hd (MAP FST hs.tbl)’ by (imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >> metis_tac[FST]) >>
  gvs[cok_def]
QED

Theorem crel_up:
  crel a N rqs lfd st rdyf ps w hs ∧ i < N ∧ EL i st.cs = CUp hd r ⇒
  hstat (w, hs) hd = SOME Up ∧ hl_sent hd ps ++ r = brequests (rqs i) ∧
  ALOOKUP st.hlc hd = SOME i
Proof
  strip_tac >> ‘MEM hd (chd (EL i st.cs))’ by simp[chd_def] >>
  drule_all crel_handle >> strip_tac >> drule_all hstat_eq >> strip_tac >>
  gvs[cok_def]
QED

Theorem crel_hlc_conn:
  crel a N rqs lfd st rdyf ps w hs ∧ ALOOKUP st.hlc hd = SOME i ⇒
  MEM hd (hl_conn_handles ps)
Proof
  rw[crel_def] >> imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >> metis_tac[FST]
QED

Overload cC[local] = “λa N rqs lfd lv w0 i n. EL i (cst a N rqs lfd lv w0 n).cs”
Overload cps[local] = “λa N rqs lfd lv w0 n. hl_pairs (cprog a N rqs) (cH a N rqs lfd lv w0 n)”

Theorem run_crel:
  client_world lfd c w0 ∧ N < cbound ⇒
  crel a N rqs lfd (cst a N rqs lfd lv w0 n) (K (crdy (cH a N rqs lfd lv w0 n)))
    (cps a N rqs lfd lv w0 n) (FST (cS a N rqs lfd lv w0 n)) (SND (cS a N rqs lfd lv w0 n))
Proof
  strip_tac >> drule_all cinv_crel >> simp[]
QED

(* An up connection: its handle is up, and it has sent all after one more round *)
Theorem run_up:
  client_world lfd c w0 ∧ N < cbound ∧ i < N ∧ cC a N rqs lfd lv w0 i n = CUp hd r ⇒
  up_at lfd lv (cifds a N rqs) (cprog a N rqs) w0 n hd ∧ clc a N rqs lfd lv w0 hd = i ∧
  hl_sent hd (cps a N rqs lfd lv w0 (SUC n)) = brequests (rqs i)
Proof
  strip_tac >> drule_all run_crel >> disch_then (qspecl_then [‘rqs’, ‘n’, ‘lv’, ‘a’] assume_tac) >>
  drule_all crel_up >> strip_tac >>
  ‘clc a N rqs lfd lv w0 hd = i’ by (irule clc_eq >> metis_tac[]) >>
  simp[up_at_hstat] >>
  qspecl_then [‘w0’, ‘rqs’, ‘n’, ‘lv’, ‘lfd’, ‘i’, ‘c’, ‘a’, ‘N’] mp_tac
    (Q.GENL [‘w0’, ‘rqs’, ‘n’, ‘lv’, ‘lfd’, ‘i’, ‘c’, ‘a’, ‘N’] cround_trans) >>
  simp[] >> strip_tac >> gvs[ctr_def]
QED

(* A pending connection that goes up or done: its handle was up *)
Theorem run_enter:
  client_world lfd c w0 ∧ N < cbound ∧ i < N ∧ cC a N rqs lfd lv w0 i n = CPend hd ∧
  cC a N rqs lfd lv w0 i (SUC n) ≠ CPend hd ∧ cC a N rqs lfd lv w0 i (SUC n) ≠ CIdle ⇒
  up_at lfd lv (cifds a N rqs) (cprog a N rqs) w0 n hd ∧ clc a N rqs lfd lv w0 hd = i ∧
  hl_sent hd (cps a N rqs lfd lv w0 (SUC n)) = [] ∧
  MEM hd (hl_conn_handles (cps a N rqs lfd lv w0 (SUC n))) ∧
  (cC a N rqs lfd lv w0 i (SUC n) = CDone ∧ hl_eof hd (cps a N rqs lfd lv w0 (SUC n)) ∨
   ∃r. cC a N rqs lfd lv w0 i (SUC n) = CUp hd r)
Proof
  strip_tac >> drule_all run_crel >> disch_then (qspecl_then [‘rqs’, ‘n’, ‘lv’, ‘a’] assume_tac) >>
  drule_all crel_pend >> strip_tac >>
  ‘clc a N rqs lfd lv w0 hd = i’ by (irule clc_eq >> metis_tac[]) >>
  drule_all crel_hlc_conn >> strip_tac >>
  qspecl_then [‘w0’, ‘rqs’, ‘n’, ‘lv’, ‘lfd’, ‘i’, ‘c’, ‘a’, ‘N’] mp_tac
    (Q.GENL [‘w0’, ‘rqs’, ‘n’, ‘lv’, ‘lfd’, ‘i’, ‘c’, ‘a’, ‘N’] cround_trans) >>
  simp[] >> strip_tac >> gvs[ctr_def, up_at_hstat] >> gvs[]
QED

Theorem LENGTH_distinct_le:
  ALL_DISTINCT l ∧ (∀x. MEM x l ⇒ MEM x l') ⇒ LENGTH l ≤ LENGTH l'
Proof
  strip_tac >> ‘LENGTH l = CARD (set l)’ by simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  ‘CARD (set l) ≤ CARD (set l')’ by (irule CARD_SUBSET >> simp[SUBSET_DEF]) >>
  ‘CARD (set l') ≤ LENGTH l'’ by simp[CARD_LIST_TO_SET] >> simp[]
QED

(* Out of handles: the guarantee's third disjunct *)
Theorem run_nh:
  client_world lfd c w0 ∧ N < cbound ∧ ¬((cst a N rqs lfd lv w0 n).nh < cbound) ⇒
  cbound ≤ LENGTH (hl_conn_handles (cps a N rqs lfd lv w0 n))
Proof
  strip_tac >> drule_all run_crel >> disch_then (qspecl_then [‘rqs’, ‘n’, ‘lv’, ‘a’] mp_tac) >>
  simp[crel_def] >> strip_tac >>
  ‘LENGTH (MAP FST (cst a N rqs lfd lv w0 n).hlc) ≤ LENGTH (hl_conn_handles (cps a N rqs lfd lv w0 n))’
    by (irule LENGTH_distinct_le >> simp[]) >> fs[]
QED

(* An idle connection, with handles to spare, connects *)
Theorem run_connect:
  client_world lfd c w0 ∧ N < cbound ∧ i < N ∧ cC a N rqs lfd lv w0 i n = CIdle ∧
  (cst a N rqs lfd lv w0 n).nh < cbound ⇒
  ∃p. MEM (EConnect p) (new_actions (log_of (cprog a N rqs)) (cH a N rqs lfd lv w0 n))
Proof
  strip_tac >> ‘cinv a N rqs lfd lv w0 n’ by metis_tac[cinv_all] >>
  pop_assum mp_tac >> simp[cinv_def] >> strip_tac >> simp[cprog_new_actions, MEM_cacts] >>
  ‘LENGTH (cst a N rqs lfd lv w0 n).cs = N’ by fs[crel_def] >>
  qexists_tac ‘a’ >> qexists_tac ‘i’ >> simp[cact1_def]
QED

(* The transitions, without the pairs *)
Theorem run_ctr:
  client_world lfd c w0 ∧ N < cbound ∧ i < N ⇒
  case cC a N rqs lfd lv w0 i n of
  | CIdle => cC a N rqs lfd lv w0 i (SUC n) = CIdle ∨ ∃hd. cC a N rqs lfd lv w0 i (SUC n) = CPend hd
  | CPend hd =>
      cC a N rqs lfd lv w0 i (SUC n) = CPend hd ∨
      cC a N rqs lfd lv w0 i (SUC n) = CIdle ∧
      hstat (cS a N rqs lfd lv w0 n) hd = SOME Refused ∨
      hstat (cS a N rqs lfd lv w0 n) hd ≠ SOME Refused ∧
      (cC a N rqs lfd lv w0 i (SUC n) = CDone ∨ ∃r. cC a N rqs lfd lv w0 i (SUC n) = CUp hd r)
  | CUp hd rest => cC a N rqs lfd lv w0 i (SUC n) = CDone ∨
                   ∃r. cC a N rqs lfd lv w0 i (SUC n) = CUp hd r
  | CDone => cC a N rqs lfd lv w0 i (SUC n) = CDone
Proof
  strip_tac >>
  qspecl_then [‘w0’, ‘rqs’, ‘n’, ‘lv’, ‘lfd’, ‘i’, ‘c’, ‘a’, ‘N’] mp_tac
    (Q.GENL [‘w0’, ‘rqs’, ‘n’, ‘lv’, ‘lfd’, ‘i’, ‘c’, ‘a’, ‘N’] cround_trans) >>
  simp[] >> strip_tac >>
  Cases_on ‘cC a N rqs lfd lv w0 i n’ >> gvs[ctr_def] >>
  Cases_on ‘c' ∈ crdy (cH a N rqs lfd lv w0 n)’ >> gvs[] >> metis_tac[]
QED
