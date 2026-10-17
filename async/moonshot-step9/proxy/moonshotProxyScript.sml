(*
  The moonshot's proxy (design/45 §2.2, step 9), as a computation on the
  endpoint handle layer, against proxyHLStmts (revision 3).

  The proxy accepts fronts on its listener lfd and gives each its own
  backend, a connect to address b (retried while it gets no socket).
  Pair i holds:
   - fh, fo: the front's handle, and whether it is open;
   - bh, bo, bup: the backend's handle (once connected), whether it is
     open, and whether it has answered a read (so it was not refused);
   - fq: bytes read from the front, not yet written to the backend;
   - bq: bytes read from the backend, not yet written to the front.
  Each round, in this order:
   - the Level of every open handle;
   - an accept (while handles last: two per pair, below cbound);
   - a connect for each pair without a backend;
   - the writes of fq and bq (the relay lags one round);
   - the reads, each behind the CREDIT GATE: a handle is read only if its
     partner's Level, answered in the last round, plus the bytes written to
     the partner in the last round and in this one, is ≤ hw.  The front is
     read only once its backend has answered a read; the backend's first
     read (after its settle report) tells Up from Refused.
  A closed or refused handle is no longer read or written (half-close and
  closing are owed: proxyHLStmts [R3]).

  As the client (moonshotClient), the computation is a fold over the
  history: each snapshot's results update the state, paired with the
  previous round's actions, and the state and the snapshot's ready handles
  give the next round's actions.
*)
Theory moonshotProxy
Ancestors
  proxyHLStmts moonshotClientSpec endpointHLModel asyncLevel1 asyncCore
Libs
  preamble

Datatype:
  pconn = <| fh : word64; fo : bool;
             bh : word64 option; bo : bool; bup : bool;
             fq : word8 list; bq : word8 list |>
End

Datatype:
  pst = <| pc : pconn list                (* pair i *)
         ; last : (num # eact) list       (* the last round's actions, with their pair *)
         ; lv : (word64 # num) list |>    (* the last round's Level answers *)
End

Definition pread_def:
  pread = 4096n
End

Definition pnew_def:
  pnew hd = <| fh := hd; fo := T; bh := NONE; bo := F; bup := F; fq := []; bq := [] |>
End

(* The open handles of a pair *)
Definition popen_def:
  popen p = (if p.fo then [p.fh] else []) ++
            (case p.bh of SOME c => if p.bo then [c] else [] | NONE => [])
End

(* Each pair's actions of one kind, tagged with the pair *)
Definition pall_def:
  pall (f : pconn -> eact list) ps =
    FLAT (GENLIST (λi. MAP (λx. (i, x)) (f (EL i ps))) (LENGTH ps))
End

Definition plevels_def:
  plevels p = MAP ELevel (popen p)
End

Definition pconnects_def:
  pconnects b p = if p.bh = NONE then [EConnect b] else []
End

Definition pwrites_def:
  pwrites p =
    (if p.fo ∧ p.bq ≠ [] then [EWrite p.fh p.bq] else []) ++
    (case p.bh of
     | SOME c => if p.bo ∧ p.fq ≠ [] then [EWrite c p.fq] else []
     | NONE => [])
End

(* The credit gate for reading h's partner g: g's Level from the last
   round, plus what the last round (lw) and this round (nw) write to g *)
Definition pgate_def:
  pgate hw lvs lw nw g ⇔
    case ALOOKUP lvs g of
    | SOME l => l + wreq g lw + wreq g nw ≤ hw
    | NONE => F
End

Definition preads_def:
  preads hw lvs lw nw (rdy : word64 set) p =
    case p.bh of
    | NONE => []
    | SOME c =>
        if p.fo ∧ p.bo then
          (if p.bup ∧ p.fh ∈ rdy ∧ pgate hw lvs lw nw c then [ERead p.fh pread] else []) ++
          (if c ∈ rdy ∧ pgate hw lvs lw nw p.fh then [ERead c pread] else [])
        else []
End

(* Round actions from state st with the ready handles rdy *)
Definition pacts_def:
  pacts lfd b hw st (rdy : word64 set) =
    let ws = pall pwrites st.pc in
      pall plevels st.pc ++
      (if 2 * LENGTH st.pc + 2 ≤ cbound then [(0, EAccept lfd)] else []) ++
      pall (pconnects b) st.pc ++
      ws ++
      pall (preads hw st.lv (MAP SND st.last) (MAP SND ws) rdy) st.pc
End

(* One result r of action x on pair p *)
Definition pres_def:
  pres p x r =
    case (x, r) of
    | (EConnect _, EConnected (SOME c)) => p with <| bh := SOME c; bo := T |>
    | (EWrite h _, EWrote k) =>
        if h = p.fh then p with bq := DROP k p.bq else p with fq := DROP k p.fq
    | (ERead h _, EGot (SOME [])) =>
        if h = p.fh then p with fo := F else p with <| bo := F; bup := T |>
    | (ERead h _, EGot (SOME d)) =>
        if h = p.fh then p with fq := p.fq ++ d else p with <| bq := p.bq ++ d; bup := T |>
    | (ERead h _, EGot NONE) => if h = p.fh then p else p with bup := T
    | (ERead h _, ERefused) => if h = p.fh then p with fo := F else p with bo := F
    | _ => p
End

(* The results of the last round's actions, in order *)
Definition pupd_def:
  pupd st [] rs = st ∧
  pupd st _ [] = st ∧
  pupd st ((i, x) :: xs) (r :: rs) =
    pupd (case (x, r) of
          | (ELevel h, ELvl l) => st with lv := (h, l) :: st.lv
          | (EAccept _, EAccepted (SOME hd)) => st with pc := st.pc ++ [pnew hd]
          | (EAccept _, _) => st
          | _ => st with pc := LUPDATE (pres (EL i st.pc) x r) i st.pc)
         xs rs
End

Definition pinit_def:
  pinit lfd b hw =
    let st = <| pc := []; last := []; lv := [] |> in
      st with last := pacts lfd b hw st ∅
End

Definition pstep_def:
  pstep lfd b hw st (s : (word64, eresp) snapshot) =
    let st1 = pupd (st with lv := []) st.last s.results in
      st1 with last := pacts lfd b hw st1 s.ready
End

Definition pstate_def:
  pstate lfd b hw h = FOLDL (pstep lfd b hw) (pinit lfd b hw) h
End

(* The computation: every round's actions so far; it never finishes *)
Definition pprog_def:
  pprog lfd b hw (h : (word64, eresp) snapshot list) =
    <| actions := FLAT (GENLIST (λk. MAP SND (pstate lfd b hw (TAKE k h)).last) (SUC (LENGTH h)));
       result := (NONE : unit option) |>
End

(* The interest: the listener and the open handles *)
Definition pifds_def:
  pifds lfd b hw h = lfd :: FLAT (MAP popen (pstate lfd b hw h).pc)
End

(* ------------------------------------------------------------------------
   The computation's rounds
   ------------------------------------------------------------------------ *)

Theorem pstate_SNOC:
  pstate lfd b hw (h ++ [s]) = pstep lfd b hw (pstate lfd b hw h) s
Proof
  simp[pstate_def, FOLDL_APPEND]
QED

Theorem pprog_actions_SNOC:
  (pprog lfd b hw (h ++ [s])).actions =
  (pprog lfd b hw h).actions ++ MAP SND (pstate lfd b hw (h ++ [s])).last
Proof
  simp[pprog_def] >>
  ‘SUC (LENGTH h + 1) = SUC (SUC (LENGTH h))’ by simp[] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC [GENLIST] >>
  ‘GENLIST (λk. MAP SND (pstate lfd b hw (TAKE k (h ++ [s]))).last) (LENGTH h) =
   GENLIST (λk. MAP SND (pstate lfd b hw (TAKE k h)).last) (LENGTH h)’
    by (irule GENLIST_CONG >> rw[] >> simp[TAKE_APPEND1]) >>
  pop_assum SUBST1_TAC >>
  simp[SNOC_APPEND, FLAT_APPEND, TAKE_LENGTH_ID_rwt, TAKE_APPEND1]
QED

(* The round polled with h emits the state's last actions *)
Theorem pprog_new_actions:
  new_actions (log_of (pprog lfd b hw)) h = MAP SND (pstate lfd b hw h).last
Proof
  Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_def, log_of_def, pprog_def, pstate_def] >>
  simp[new_actions_def, log_of_def, SNOC_APPEND, FRONT_APPEND, pprog_actions_SNOC] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED
