(*
  A reactive world for the event loop with actions (asyncCfReactLoop).

  The world is given generically by a state type 's and a step function:

     wd.step s acts = (rs, rdy, s')

  In one round the program hands the world all the actions it emitted in
  that round (acts, oldest first); the world answers with one response per
  action (rs, positionally), the round's readiness bytes (rdy, a fixed
  number wd.nready of them, read as the ready set `set rdy`), and its next
  state s'.  The state may contain anything, e.g. a schedule of future
  arrivals, so the world reacts to the actions it is given.

  On the FFI side this is a single FFI part with one call, `round`: the
  buffer holds the actions followed by wd.nready padding bytes, and comes
  back holding the responses followed by the readiness bytes.  The world
  state is stored in the FFI state through an injective encoding wd.enc.

  The snapshot sequence the world provides is defined by iterating the step
  function with the model's actions (rounds below), and the trace lemma
  says that the actions in the trace are the model's action log on that
  history.
*)
Theory asyncCfReactWorld
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel
  cfFFIType cfHeapsBase cfDiv ffi llist
Libs
  preamble

(* ------------------------------------------------------------------------
   Worlds
   ------------------------------------------------------------------------ *)

(* A reactive world: its step function, the number of readiness bytes per
   round, and an encoding of its state into CakeML's FFI state type. *)
Datatype:
  rworld = <| step : 's -> word8 list -> word8 list # word8 list # 's ;
              nready : num ;
              enc : 's -> ffi |>
End

(* A well-behaved world answers every action, gives nready readiness
   bytes, and its state encoding is injective. *)
Definition world_ok_def:
  world_ok wd ⇔
    (∀s acts. LENGTH (FST (wd.step s acts)) = LENGTH acts ∧
              LENGTH (FST (SND (wd.step s acts))) = wd.nready) ∧
    (∀s1 s2. wd.enc s1 = wd.enc s2 ⇒ s1 = s2)
End

(* The FFI function of the single call `round` *)
Definition round_update_def:
  round_update wd n conf bytes st =
    if n = «round» ∧ conf = [] ∧ wd.nready ≤ LENGTH bytes ∧ (∃s. st = wd.enc s)
    then
      let s = (@s. wd.enc s = st);
          r = wd.step s (TAKE (LENGTH bytes - wd.nready) bytes)
      in SOME (FFIreturn (FST r ++ FST (SND r)) (wd.enc (SND (SND r))))
    else NONE
End

(* RW wd s evs: the world wd in state s, with past events evs *)
Definition RW_def:
  RW wd s evs = one (FFI_part (wd.enc s) (round_update wd) [«round»] evs)
End

(* The I/O event of one round: the buffer went out as the actions plus
   padding, and came back as the responses plus the readiness bytes. *)
Definition round_event_def:
  round_event wd acts rs rdy =
    IO_event (ExtCall «round») []
      (ZIP (acts ++ REPLICATE wd.nready 0w, rs ++ rdy))
End

Theorem round_update_enc:
  world_ok wd ∧ LENGTH pad = wd.nready ⇒
  round_update wd «round» [] (acts ++ pad) (wd.enc s) =
    SOME (FFIreturn (FST (wd.step s acts) ++ FST (SND (wd.step s acts)))
                    (wd.enc (SND (SND (wd.step s acts)))))
Proof
  rw[round_update_def, world_ok_def] >- metis_tac[] >>
  ‘(@s'. wd.enc s' = wd.enc s) = s’ by (SELECT_ELIM_TAC >> metis_tac[]) >>
  simp[TAKE_APPEND1, TAKE_LENGTH_ID_rwt]
QED

(* ------------------------------------------------------------------------
   The snapshot sequence the world provides
   ------------------------------------------------------------------------ *)

(* The snapshot built from one round's answer *)
Definition wsnap_def:
  wsnap rs (rdy : word8 list) = <| ready := set rdy; now := 0; results := rs |>
End

(* wrounds wd m s0 n = (h, s): after n rounds of the loop running m in the
   world wd started in state s0, the history m has been polled with and the
   world's state.  Each round hands the world m's new actions. *)
Definition wrounds_def:
  wrounds wd m s0 0 = ([], s0) ∧
  wrounds wd m s0 (SUC n) =
    let (h, s) = wrounds wd m s0 n;
        r = wd.step s (new_actions (log_of m) h)
    in (h ++ [wsnap (FST r) (FST (SND r))], SND (SND r))
End

(* The history after n rounds *)
Definition whist_def:
  whist wd m s0 n = FST (wrounds wd m s0 n)
End

(* The I/O event of round n *)
Definition wround_event_def:
  wround_event wd m s0 n =
    let (h, s) = wrounds wd m s0 n;
        acts = new_actions (log_of m) h;
        r = wd.step s acts
    in round_event wd acts (FST r) (FST (SND r))
End

Theorem wrounds_SUC:
  wrounds wd m s0 (SUC n) =
    (FST (wrounds wd m s0 n) ++
       [wsnap (FST (wd.step (SND (wrounds wd m s0 n))
                       (new_actions (log_of m) (FST (wrounds wd m s0 n)))))
              (FST (SND (wd.step (SND (wrounds wd m s0 n))
                       (new_actions (log_of m) (FST (wrounds wd m s0 n))))))],
     SND (SND (wd.step (SND (wrounds wd m s0 n))
                (new_actions (log_of m) (FST (wrounds wd m s0 n))))))
Proof
  simp[wrounds_def] >> Cases_on ‘wrounds wd m s0 n’ >> simp[]
QED

Theorem wround_event_alt:
  wround_event wd m s0 n =
    round_event wd (new_actions (log_of m) (FST (wrounds wd m s0 n)))
      (FST (wd.step (SND (wrounds wd m s0 n))
              (new_actions (log_of m) (FST (wrounds wd m s0 n)))))
      (FST (SND (wd.step (SND (wrounds wd m s0 n))
              (new_actions (log_of m) (FST (wrounds wd m s0 n))))))
Proof
  simp[wround_event_def] >> Cases_on ‘wrounds wd m s0 n’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The actions recorded in a trace
   ------------------------------------------------------------------------ *)

(* The actions handed to the world in one event: the buffer's outgoing
   bytes, without the readiness padding *)
Definition wevent_actions_def:
  wevent_actions wd (IO_event (ExtCall n) conf bytes) =
    (if n = «round» ∧ conf = [] then
       TAKE (LENGTH bytes - wd.nready) (MAP FST bytes)
     else []) ∧
  wevent_actions wd _ = []
End

Definition wtrace_actions_def:
  wtrace_actions wd evs = FLAT (MAP (wevent_actions wd) evs)
End

Theorem wevent_actions_round_event:
  LENGTH rs = LENGTH acts ∧ LENGTH rdy = wd.nready ⇒
  wevent_actions wd (round_event wd acts rs rdy) = acts
Proof
  rw[round_event_def, wevent_actions_def, MAP_ZIP, TAKE_APPEND1,
     TAKE_LENGTH_ID_rwt]
QED

(* MAIN: the trace and the model agree, in any well-behaved reactive world.
   The actions handed to the world in the first n+1 rounds of the loop's
   trace are exactly the model's action log on the history the world
   generates (by iterating its step function with the model's actions). *)
Theorem wtrace_actions_rounds:
  world_ok wd ∧ wf m ⇒
  wtrace_actions wd (GENLIST (wround_event wd m s0) (SUC n)) =
  (m (whist wd m s0 n)).actions
Proof
  strip_tac >> Induct_on ‘n’
  >- (simp[wtrace_actions_def, wround_event_alt, wrounds_def, whist_def] >>
      DEP_REWRITE_TAC[wevent_actions_round_event] >>
      gvs[world_ok_def, new_actions_NIL, log_of_def]) >>
  ONCE_REWRITE_TAC[GENLIST] >>
  gvs[SNOC_APPEND, wtrace_actions_def, whist_def] >>
  simp[wround_event_alt] >>
  DEP_REWRITE_TAC[wevent_actions_round_event] >>
  conj_tac >- gvs[world_ok_def] >>
  simp[wrounds_SUC] >>
  qmatch_goalsub_abbrev_tac ‘new_actions _ (h ++ [s])’ >>
  ‘log_of m h ≼ log_of m (h ++ [s])’ by simp[log_of_def, wf_SNOC_actions] >>
  drule new_actions_prefix >> simp[log_of_def]
QED

(* ------------------------------------------------------------------------
   Lazy-list lemma for the trace (one event per round)
   ------------------------------------------------------------------------ *)

Theorem LGENLIST_shift[local]:
  LGENLIST (λi. f (i + k)) NONE = f k ::: LGENLIST (λi. f (i + (k + 1))) NONE
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
  simp[combinTheory.o_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

Theorem LGENLIST_singletons_shift[local]:
  LGENLIST (λi. [|e (i + k)|]) NONE =
  [|e k|] ::: LGENLIST (λi. [|e (i + (k + 1))|]) NONE
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
  simp[combinTheory.o_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

Theorem LFLATTEN_LGENLIST_singletons:
  LFLATTEN (LGENLIST (λi. [|e i|]) NONE) = LGENLIST e NONE
Proof
  simp[Once LLIST_BISIMULATION0] >>
  qexists_tac ‘λa b. ∃k. a = LFLATTEN (LGENLIST (λi. [|e (k + i)|]) NONE) ∧
                         b = LGENLIST (λi. e (k + i)) NONE’ >>
  rw[] >- (qexists_tac ‘0’ >> simp[ETA_AX]) >>
  ONCE_REWRITE_TAC[LGENLIST_shift] >> simp[] >>
  qexists_tac ‘LFLATTEN (LGENLIST (λi. [|e (i + (k + 1))|]) NONE)’ >>
  conj_tac
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_singletons_shift])) >>
      simp[]) >>
  qexists_tac ‘k + 1’ >> simp[] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_shift])) >> simp[]
QED

(* The first iteration of cfDiv's loop rule has no events of its own *)
Theorem LFLATTEN_LGENLIST_shift1:
  LFLATTEN (LGENLIST (fromList o (λi. if i = 0 then [] else [e (i - 1)])) NONE) =
  LGENLIST e NONE
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
  simp[combinTheory.o_DEF, LFLATTEN_LGENLIST_singletons]
QED
