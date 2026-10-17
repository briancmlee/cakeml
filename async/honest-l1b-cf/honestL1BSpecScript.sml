(*
  The CF specs of the blocking L1's CakeML code (honestL1BProg) against
  its model (honestL1BModel), on the PF code's specs (honestL1PFSpec).

  A blocking poll either returns (as the non-blocking one, with block
  flag 1) or waits for ever: then the program stops in that FFI call
  (POSTf, the poll's configuration and buffer).  The loop run_pfb either
  never sleeps (POSTd: its trace is the rounds' events) or sleeps in round
  n (POSTf: the events before the final poll).

  For a server that is never busy (bz = K F): the code's idle test is the
  model's with ¬bz h = T.

  MAIN: run_pfb_div_spec, run_pfb_sleep_spec.
*)
Theory honestL1BSpec
Ancestors
  ml_translator cfHeapsBase Word8ArrayProof mlstring
  honestL0 honestL0World honestL1Model honestL1PFModel honestL0Part
  honestL0Prog honestL0Proof honestL1PFProg ffiSpikeSocketFFI asyncM3Loop asyncM3World
  asyncM3Prog asyncM4Loop asyncM4LiveInterest asyncCfActProg asyncCfActModel asyncChoose honestL1PFInv cfDiv
  honestL1PFSpec honestL1BModel honestL1BPoll honestL1Inv honestL1BNoFail honestL1BProg
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib

val _ = translation_extends "honestL1BProg";
val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   The blocking poll
   ------------------------------------------------------------------------ *)

(* The let after a call that waits for ever is never reached: the call's
   POSTf is the let's *)
val postf_tac =
  simp[SEP_IMPPOSTv_inv_def, SEP_IMPPOSTe_POSTf_left, SEP_IMPPOSTd_POSTf_left,
       SEP_IMPPOSTf_def] >> rpt strip_tac >> xsimpl >> rw[] >>
  TRY (metis_tac[SEP_IMP_REFL]);

(* The part passes a reachable state's diverging call through *)
Theorem l0_next_div:
  l0_reach w0 w ∧ MEM n l0_names ∧
  l0_ffi_fn n conf bytes w = SOME FFIdiverge ⇒
  l0_next w0 n conf bytes (l0_enc w0 w) = SOME FFIdiverge
Proof
  strip_tac >> gvs[l0_next_def, l0_enc_def] >> fs[l0_reach_def]
QED

Theorem bytes_str_bytes[local]:
  MAP (n2w o ORD) (explode (bytes_str bs)) = bs : word8 list ∧
  strlen (bytes_str bs) = LENGTH bs
Proof
  simp[MAP_MAP_o, o_DEF] >>
  ‘∀b : word8. w2n b < 256’ by (gen_tac >> assume_tac (INST_TYPE [alpha |-> “:8”] w2n_lt) >> fs[]) >>
  simp[ORD_CHR] >> Induct_on ‘bs’ >> simp[]
QED

(* L0.poll, when the call waits for ever *)
Theorem L0_poll_div_spec:
  STRING_TYPE (bytes_str conf) confv ∧ STRING_TYPE (bytes_str bytes) bufv ∧
  l0_ffi_fn «sys_poll» conf bytes w = SOME FFIdiverge ⇒
  app (p:'ffi ffi_proj) L0_poll_v [confv; bufv] (L0_EV w0 w evs)
    (POSTf n. λc b. &(n = «sys_poll» ∧ c = conf ∧ b = bytes) * L0_EV w0 w evs *
                  SEP_EXISTS av. W8ARRAY av bytes)
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestL0Prog" "L0_poll_v_def") >>
  simp[L0_EV_def] >> xpull >>
  ‘MEM «sys_poll» l0_names’ by simp[l0_names_def] >>
  drule_all l0_next_div >> strip_tac >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY av (REPLICATE _ _)’ >>
  xlet ‘POSTv uv. W8ARRAY av bytes * one (FFI_part (l0_enc w0 w) (l0_next w0) l0_names evs)’
  >- (xapp >> xsimpl >> qexistsl [‘bytes_str bytes’, ‘LENGTH bytes’] >>
      simp[bytes_str_bytes, mlstringTheory.substring_def] >>
      ‘SEG (LENGTH bytes) 0 (MAP (CHR ∘ w2n) bytes) = MAP (CHR ∘ w2n) bytes’
        by metis_tac[SEG_LENGTH_ID, LENGTH_MAP] >>
      simp[] >> qspec_then ‘bytes’ mp_tac (Q.GEN ‘bs’ (cj 1 bytes_str_bytes)) >> simp[]) >>
  xlet ‘POSTf n. λc b. &(n = «sys_poll» ∧ c = conf ∧ b = bytes) *
          W8ARRAY av bytes * one (FFI_part (l0_enc w0 w) (l0_next w0) l0_names evs)’
  >- (xffi >> xsimpl >> gvs[STRING_TYPE_def] >>
      qexistsl [‘conf’, ‘emp’, ‘l0_enc w0 w’, ‘l0_next w0’, ‘l0_names’, ‘evs’] >>
      simp[] >> conj_tac >- EVAL_TAC >> xsimpl) >>
  postf_tac
QED

(* The blocking poll, when it returns *)
Theorem c_pollb_spec:
  LIST_TYPE (PAIR_TYPE WORD NUM) fes fesv ∧ sys_pollb fes w = SOME (INL (out, w', ev)) ⇒
  app (p:'ffi ffi_proj) c_pollb_v [fesv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestL1BProg" "c_pollb_v_def") >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &LIST_TYPE WORD ([] : word8 list) v * L0_EV w0 w evs’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xlet_auto >- xsimpl >>
  xlet ‘POSTv v. &LIST_TYPE WORD [1w : word8] v * L0_EV w0 w evs’
  >- (xcon >> xsimpl >> fs[LIST_TYPE_def]) >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev])’
  >- (xapp_spec L0_poll_spec >> xsimpl >>
      gvs[sys_pollb_def, pollb_conf_def, AllCaseEqs(), l0_do_buf_def, bytes_str_bytes_to_str] >>
      metis_tac[]) >>
  xapp >> xsimpl >> qexists_tac ‘bytes_str out’ >>
  simp[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str]
QED

(* The blocking poll, when it waits for ever *)
Theorem c_pollb_div_spec:
  LIST_TYPE (PAIR_TYPE WORD NUM) fes fesv ∧ sys_pollb fes w = SOME (INR cb) ⇒
  app (p:'ffi ffi_proj) c_pollb_v [fesv] (L0_EV w0 w evs)
    (POSTf n. λc b. &(n = «sys_poll» ∧ (c, b) = cb) * L0_EV w0 w evs * GC)
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestL1BProg" "c_pollb_v_def") >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &LIST_TYPE WORD ([] : word8 list) v * L0_EV w0 w evs’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xlet_auto >- xsimpl >>
  xlet ‘POSTv v. &LIST_TYPE WORD [1w : word8] v * L0_EV w0 w evs’
  >- (xcon >> xsimpl >> fs[LIST_TYPE_def]) >>
  rpt (xlet_auto >- xsimpl) >>
  gvs[sys_pollb_def, pollb_conf_def, AllCaseEqs()] >>
  xlet ‘POSTf n. λc b. &(n = «sys_poll» ∧ c = [1w] ∧ b = poll_buf fes) * L0_EV w0 w evs *
                     SEP_EXISTS av. W8ARRAY av (poll_buf fes)’
  >- (xapp_spec L0_poll_div_spec >> xsimpl >> gvs[bytes_str_bytes_to_str] >>
      fs[bytes_to_str_def]) >>
  postf_tac
QED

(* ------------------------------------------------------------------------
   The round's tail after its poll
   ------------------------------------------------------------------------ *)

Theorem pf_after_pevs:
  pf_after lfd hw hs ps fes (rv, w, pevs) =
    OPTION_MAP (λ(rdy, ws, log, evs). (rdy, ws, log, pevs ++ evs))
      (pf_after lfd hw hs ps fes (rv, w, []))
Proof
  simp[pf_after_def] >> every_case_tac >> simp[]
QED

Theorem pf_aftr_spec:
  pf_after lfd (pol_self hw) hs ps fes (rv, w, []) = SOME (rdy, (w', ps'), log, evs1) ∧
  WORD lfd lfdv ∧ NUM hw hwv ∧ LIST_TYPE WORD hs hsv ∧ L1P ps psv ∧
  LIST_TYPE (PAIR_TYPE WORD NUM) fes fesv ∧ LIST_TYPE (PAIR_TYPE WORD REV) rv rvv ⇒
  app (p:'ffi ffi_proj) pf_aftr_v [lfdv; hwv; hsv; psv; fesv; rvv] (L0_EV w0 w evs)
    (POSTv v. &(∃rdyv psv'. v = Conv NONE [rdyv; psv'] ∧
                            LIST_TYPE WORD rdy rdyv ∧ L1P ps' psv') *
              L0_EV w0 w' (evs ++ evs1))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "honestL1BProg" "pf_aftr_v_def") >>
  gvs[pf_after_def, AllCaseEqs()] >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &L1ST b2 v * L0_EV w0 w2 (evs ++ fevs)’
  >- (xapp_spec l1_flush_spec >> xsimpl >> gvs[l1p_b_def] >> metis_tac[]) >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &(∃psv' lv. v = Conv NONE [psv'; lv] ∧ L1P ps3' psv' ∧ LIST_TYPE FLOG log lv) *
                 L0_EV w0 w3 (evs ++ fevs ++ gevs)’
  >- (xapp_spec pf_fetch_spec >> xsimpl >> gvs[filter_in_def, set_b_def, GSYM pf_poll_set_hw] >>
      metis_tac[]) >>
  gvs[] >> xmatch >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &L1ST b4 v * L0_EV w0 w' (evs ++ fevs ++ gevs ++ cevs)’
  >- (xapp_spec l1_reap_spec >> xsimpl >> gvs[l1p_b_def, closing_of_def, stall_step_ob_def] >>
      metis_tac[]) >>
  rpt (xlet_auto >- xsimpl) >>
  xcon >> xsimpl >> gvs[end_round_def, stall_step_ob_def, l1p_b_def]
QED

(* The blocking tail: the blocking poll, then the tail after it *)
Theorem pf_tailb_spec:
  sys_pollb (pf_poll_set lfd (pol_self hw) ps hs) w = SOME (INL (out, w2, ev)) ∧
  pf_after lfd (pol_self hw) hs ps (pf_poll_set lfd (pol_self hw) ps hs)
    (poll_revents (pf_poll_set lfd (pol_self hw) ps hs) out, w2, [ev]) =
    SOME (rdy, (w', ps'), log, evs1) ∧
  WORD lfd lfdv ∧ NUM hw hwv ∧ LIST_TYPE WORD hs hsv ∧ L1P ps psv ⇒
  app (p:'ffi ffi_proj) pf_tailb_v [lfdv; hwv; hsv; psv] (L0_EV w0 w evs)
    (POSTv v. &(∃rdyv psv'. v = Conv NONE [rdyv; psv'] ∧
                            LIST_TYPE WORD rdy rdyv ∧ L1P ps' psv') *
              L0_EV w0 w' (evs ++ evs1))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "honestL1BProg" "pf_tailb_v_def") >>
  gvs[GSYM pf_poll_set_hw] >>
  xlet_auto >- xsimpl >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w2 (evs ++ [ev])’
  >- (xapp_spec c_pollb_spec >> xsimpl >> metis_tac[]) >>
  xlet_auto >- xsimpl >>
  qpat_x_assum ‘pf_after _ _ _ _ _ _ = _’ mp_tac >>
  simp[Once pf_after_pevs, PULL_EXISTS, FORALL_PROD] >> rpt strip_tac >> gvs[] >>
  rename1 ‘pf_after _ _ _ _ _ _ = SOME (rdy, (w', ps'), log, aevs)’ >>
  xapp_spec pf_aftr_spec >>
  qexistsl [‘emp’, ‘w0’, ‘w'’, ‘w2’, ‘rdy’, ‘ps'’, ‘aevs’, ‘evs ++ [ev]’] >>
  conj_tac
  >- (qexistsl [‘pf_poll_set_hw lfd hw ps hs’, ‘hs’, ‘hw’, ‘lfd’, ‘log’, ‘ps’,
                ‘poll_revents (pf_poll_set_hw lfd hw ps hs) out’] >> simp[]) >>
  xsimpl >> REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> xsimpl
QED

Theorem pf_tailb_div_spec:
  sys_pollb (pf_poll_set lfd (pol_self hw) ps hs) w = SOME (INR cb) ∧
  WORD lfd lfdv ∧ NUM hw hwv ∧ LIST_TYPE WORD hs hsv ∧ L1P ps psv ⇒
  app (p:'ffi ffi_proj) pf_tailb_v [lfdv; hwv; hsv; psv] (L0_EV w0 w evs)
    (POSTf n. λc b. &(n = «sys_poll» ∧ (c, b) = cb) * L0_EV w0 w evs * GC)
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "honestL1BProg" "pf_tailb_v_def") >>
  gvs[GSYM pf_poll_set_hw] >>
  xlet_auto >- xsimpl >>
  xlet ‘POSTf n. λc b. &(n = «sys_poll» ∧ (c, b) = cb) * L0_EV w0 w evs * GC’
  >- (xapp_spec c_pollb_div_spec >> xsimpl >> metis_tac[]) >>
  postf_tac
QED

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

(* The round's guard (honestL1PFSpec's guard_tac) *)
val guard_tac =
  xlet ‘POSTv v. &NUM (naccepts (m []).actions) v * L0_EV w0 w evs’
  >- (xapp_spec naccepts_spec >> xsimpl >> metis_tac[]) >>
  rpt (xlet_auto >- xsimpl);

(* After the tail: the snapshot to the server, and the next state *)
fun end_tac rs ee =
  gvs[] >> xmatch >> (xlet_auto >- xsimpl) >>
  xlet ‘POSTv wv. &SNAPSHOT SREADY SRESP (ssnap rdy ^rs) wv * L0_EV w0 w' ^ee’
  >- (xcon >> xsimpl >> simp[SNAPSHOT_def, ssnap_def, SREADY_def, NUM_def, INT_def] >>
      qexists_tac ‘rdy’ >> fs[map_num_def] >>
      qmatch_asmsub_abbrev_tac ‘LIST_TYPE NUM (MAP ff rdy)’ >>
      ‘ff = w2n’ by simp[Abbr‘ff’, FUN_EQ_THM] >> gvs[]) >>
  ‘app p Async_poll_v [Conv NONE [av; sv]; wv] emp
     (POSTv v. &COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended m [ssnap rdy ^rs]) v)’
    by (irule Async_poll_spec >> simp[]) >>
  xlet ‘POSTv cv'. &COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended m [ssnap rdy ^rs]) cv' *
                   L0_EV w0 w' ^ee’
  >- (qpat_x_assum ‘app _ Async_poll_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv fv. &LIST_TYPE NUM (MAP w2n (live_round fds (m []).actions ^rs)) fv *
                  L0_EV w0 w' ^ee’
  >- (xapp_spec live_round_spec >> xsimpl >> metis_tac[]) >>
  xcon >> xsimpl >> gvs[ssnap_def];

(* MAIN: a round that returns *)
Theorem step_pfb_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧ WORD lfd lfdv ∧ NUM hw hwv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ L1P ps psv ∧
  hdl_room lfd ps (naccepts (m []).actions) ∧
  bround lfd (pol_self hw) T fds (w, ps) (m []).actions = SOME (BRound snap (w', ps') log evs1) ⇒
  app (p:'ffi ffi_proj) step_pfb_v [Conv NONE [lfdv; hwv; fdsv; psv; cv]]
    (L0_EV w0 w evs)
    (POSTv v.
       &(∃fdsv' psv' cv'. v = Conv NONE [lfdv; hwv; fdsv'; psv'; cv'] ∧
           LIST_TYPE NUM (MAP w2n (live_round fds (m []).actions snap.results)) fdsv' ∧
           L1P ps' psv' ∧
           COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended m [snap]) cv') *
       L0_EV w0 w' (evs ++ evs1))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >>
  qpat_x_assum ‘bround _ _ _ _ _ _ = _’ mp_tac >> simp[bround_def] >>
  Cases_on ‘pacts lfd (w, ps) (m []).actions’ >> simp[] >>
  rename1 ‘pacts _ _ _ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs', w1, ps1)’ >> strip_tac >>
  xcf_with_def (fetch "honestL1BProg" "step_pfb_v_def") >> xmatch >> xmatch >>
  guard_tac >> xif >> qexists_tac ‘F’ >> simp[] >>
  xlet ‘POSTv v. &(∃psv' rsv. v = Conv NONE [psv'; rsv] ∧ L1P ps1 psv' ∧
                              LIST_TYPE SRESP rs rsv) * L0_EV w0 w1 (evs ++ evs')’
  >- (xapp_spec pacts_spec >> xsimpl >> qexistsl [‘(m []).actions’, ‘lfd’, ‘ps’] >> simp[]) >>
  gvs[] >> xmatch >> (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &BOOL ((m []).actions = [] ∧ pf_idle lfd (pol_self hw) ps1 fds) v *
                 L0_EV w0 w1 (evs ++ evs')’
  >- (Cases_on ‘(m []).actions’ >> gvs[LIST_TYPE_def] >> xmatch
      >- (xapp >> xsimpl >>
          gvs[map_w64_def, MAP_MAP_o, combinTheory.o_DEF, GSYM pf_idle_c] >>
          qexistsl [‘fds’, ‘ps’, ‘lfd’] >> simp[]) >>
      xcon >> xsimpl) >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >> gvs[]
  >- (xlet ‘POSTv v. &(∃rdyv psv'. v = Conv NONE [rdyv; psv'] ∧
                         LIST_TYPE WORD rdy rdyv ∧ L1P ps' psv') *
                 L0_EV w0 w' (evs ++ evs1)’
      >- (xif >> qexists_tac ‘T’ >> simp[] >>
          xapp_spec pf_tailb_spec >> xsimpl >>
          gvs[map_w64_def, MAP_MAP_o, combinTheory.o_DEF] >> metis_tac[]) >>
      end_tac “[] : sresp list” “evs ++ evs1 : io_event list”) >>
  xlet ‘POSTv v. &(∃rdyv psv'. v = Conv NONE [rdyv; psv'] ∧
                     LIST_TYPE WORD rdy rdyv ∧ L1P ps' psv') *
             L0_EV w0 w' (evs ++ evs' ++ tevs)’
  >- (xif >> qexists_tac ‘F’ >> simp[] >>
      xapp_spec pf_tail_spec >> xsimpl >>
      gvs[map_w64_def, MAP_MAP_o, combinTheory.o_DEF] >> metis_tac[]) >>
  end_tac “rs : sresp list” “evs ++ evs' ++ tevs : io_event list”
QED

(* MAIN: a round whose blocking poll waits for ever *)
Theorem step_pfb_sleep_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧ WORD lfd lfdv ∧ NUM hw hwv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ L1P ps psv ∧
  hdl_room lfd ps (naccepts (m []).actions) ∧
  bround lfd (pol_self hw) T fds (w, ps) (m []).actions = SOME (BAsleep evs1 cb) ⇒
  app (p:'ffi ffi_proj) step_pfb_v [Conv NONE [lfdv; hwv; fdsv; psv; cv]]
    (L0_EV w0 w evs)
    (POSTf n. λc b. &(n = «sys_poll» ∧ (c, b) = cb) *
                  (SEP_EXISTS w1. L0_EV w0 w1 (evs ++ evs1)) * GC)
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >>
  qpat_x_assum ‘bround _ _ _ _ _ _ = _’ mp_tac >> simp[bround_def] >>
  Cases_on ‘pacts lfd (w, ps) (m []).actions’ >> simp[] >>
  rename1 ‘pacts _ _ _ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs', w1, ps1)’ >> strip_tac >>
  xcf_with_def (fetch "honestL1BProg" "step_pfb_v_def") >> xmatch >> xmatch >>
  guard_tac >> xif >> qexists_tac ‘F’ >> simp[] >>
  xlet ‘POSTv v. &(∃psv' rsv. v = Conv NONE [psv'; rsv] ∧ L1P ps1 psv' ∧
                              LIST_TYPE SRESP rs rsv) * L0_EV w0 w1 (evs ++ evs')’
  >- (xapp_spec pacts_spec >> xsimpl >> qexistsl [‘(m []).actions’, ‘lfd’, ‘ps’] >> simp[]) >>
  gvs[] >> xmatch >> (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &BOOL ((m []).actions = [] ∧ pf_idle lfd (pol_self hw) ps1 fds) v *
                 L0_EV w0 w1 (evs ++ evs')’
  >- (Cases_on ‘(m []).actions’ >> gvs[LIST_TYPE_def] >> xmatch
      >- (xapp >> xsimpl >>
          gvs[map_w64_def, MAP_MAP_o, combinTheory.o_DEF, GSYM pf_idle_c] >>
          qexistsl [‘fds’, ‘ps’, ‘lfd’] >> simp[]) >>
      xcon >> xsimpl) >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >> gvs[] >>
  xlet ‘POSTf n. λc b. &(n = «sys_poll» ∧ (c, b) = cb) * L0_EV w0 w evs * GC’
  >- (xif >> qexists_tac ‘T’ >> simp[] >>
      xapp_spec pf_tailb_div_spec >>
      qexistsl [‘fds’, ‘hw’, ‘lfd’, ‘ps’] >>
      gvs[map_w64_def, MAP_MAP_o, combinTheory.o_DEF]) >>
  postf_tac
QED

(* Without room the step does nothing *)
Theorem step_pfb_stop_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧ WORD lfd lfdv ∧ L1P ps psv ∧
  ¬hdl_room lfd ps (naccepts (m []).actions) ⇒
  app (p:'ffi ffi_proj) step_pfb_v [Conv NONE [lfdv; hwv; fdsv; psv; cv]]
    (L0_EV w0 w evs)
    (POSTv v. &(v = Conv NONE [lfdv; hwv; fdsv; psv; cv]) * L0_EV w0 w evs)
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >>
  xcf_with_def (fetch "honestL1BProg" "step_pfb_v_def") >> xmatch >> xmatch >>
  guard_tac >> xif >> qexists_tac ‘T’ >> simp[] >> xvar >> xsimpl
QED

(* ------------------------------------------------------------------------
   The loop's rounds
   ------------------------------------------------------------------------ *)

(* The loop's rounds: brounds's for a server never busy (bz = K F), while
   the handle counter has room for the round's actions; then the loop
   stops (the state no longer changes), as the PF loop's (prounds_t) *)
Definition brounds_t_def:
  brounds_t lfd hw ifds m ws0 0 = SOME (BRun [] ws0 [] []) ∧
  brounds_t lfd hw ifds m ws0 (SUC n) =
    case brounds_t lfd hw ifds m ws0 n of
    | NONE => NONE
    | SOME (BSlept h evs cb) => SOME (BSlept h evs cb)
    | SOME (BRun h ws evs logs) =>
        if hdl_room lfd (SND ws) (naccepts (new_actions (log_of m) h)) then
          (case bround lfd (pol_self hw) T (ifds h) ws (new_actions (log_of m) h) of
           | NONE => NONE
           | SOME (BAsleep evs1 cb) => SOME (BSlept h (evs ++ evs1) cb)
           | SOME (BRound snap ws' log evs1) =>
               SOME (BRun (h ++ [snap]) ws' (evs ++ evs1) (logs ++ [log])))
        else SOME (BRun h ws evs logs)
End

(* What the server must do in every round it runs: pact_ok actions *)
Definition bt_ok_def:
  bt_ok lfd hw ifds m ws0 ⇔
    ∀n h ws evs logs. brounds_t lfd hw ifds m ws0 n = SOME (BRun h ws evs logs) ⇒
      EVERY (pact_ok lfd) (new_actions (log_of m) h)
End

Theorem bround_ok_keep[local]:
  l0_rely w ∧ psmall lfd ps ∧ EVERY (pact_ok lfd) acts ∧ hdl_room lfd ps (naccepts acts) ⇒
  ∃r. bround lfd hw idle hs (w, ps) acts = SOME r ∧
      ∀snap w' ps' log evs. r = BRound snap (w', ps') log evs ⇒ l0_rely w' ∧ psmall lfd ps'
Proof
  strip_tac >> ‘ps.b.nxt + naccepts acts < dimword (:64)’ by fs[hdl_room_def] >>
  drule_all pacts_ok >> strip_tac >>
  simp[bround_def] >> IF_CASES_TAC
  >- (‘∃r. sys_pollb (pf_poll_set lfd hw ps' hs) w' = SOME r ∧
           ∀out w'' ev. r = INL (out, w'', ev) ⇒
                        l0_rely w'' ∧ LENGTH out = LENGTH (poll_buf (pf_poll_set lfd hw ps' hs))’
        by (irule sys_pollb_some >> simp[]) >>
      simp[] >>
      Cases_on ‘r’ >> simp[] >> PairCases_on ‘x’ >> fs[] >>
      ‘EVERY (small o FST) (poll_revents (pf_poll_set lfd hw ps' hs) x0)’
        by (irule poll_revents_small >> simp[LENGTH_poll_buf] >>
            drule pf_poll_set_small >> disch_then (qspecl_then [‘hw’, ‘hs’] mp_tac) >>
            simp[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
      drule_all pf_after_ok >>
      disch_then (qspecl_then [‘[x2]’, ‘hw’, ‘hs’, ‘pf_poll_set lfd hw ps' hs’] strip_assume_tac) >>
      simp[])
  >> drule_all pf_tail_ok >> disch_then (qspecl_then [‘hw’, ‘hs’] strip_assume_tac) >> simp[]
QED

Theorem brounds_t_total:
  l0_rely w0 ∧ psmall lfd ps0 ∧ bt_ok lfd hw ifds m (w0, ps0) ⇒
  ∀n. ∃r. brounds_t lfd hw ifds m (w0, ps0) n = SOME r ∧
          ∀h w ps evs logs. r = BRun h (w, ps) evs logs ⇒ l0_rely w ∧ psmall lfd ps
Proof
  strip_tac >> Induct >- simp[brounds_t_def] >>
  gvs[] >> simp[brounds_t_def] >>
  Cases_on ‘r’ >> simp[] >> rename1 ‘BRun h ws evs logs’ >> PairCases_on ‘ws’ >> gvs[] >>
  IF_CASES_TAC >> simp[] >>
  qpat_x_assum ‘bt_ok _ _ _ _ _’ (mp_tac o REWRITE_RULE [bt_ok_def]) >>
  disch_then drule >> strip_tac >>
  ‘∃r. bround lfd (pol_self hw) T (ifds h) (ws0, ws1) (new_actions (log_of m) h) = SOME r ∧
       ∀snap w' ps' log evs. r = BRound snap (w', ps') log evs ⇒ l0_rely w' ∧ psmall lfd ps'’
    by (irule bround_ok_keep >> fs[]) >>
  simp[] >> Cases_on ‘r’ >> gvs[] >> PairCases_on ‘p’ >> gvs[]
QED

(* While every round so far had room, the guarded run is the model's run
   (honestL1BModel's brounds, for a server never busy) *)
Theorem brounds_t_brounds:
  ∀n. (∀i h ws evs logs. i < n ∧ brounds_t lfd hw ifds m ws0 i = SOME (BRun h ws evs logs) ⇒
                         hdl_room lfd (SND ws) (naccepts (new_actions (log_of m) h))) ⇒
      brounds_t lfd hw ifds m ws0 n = brounds lfd (pol_self hw) ifds (K F) m ws0 n
Proof
  Induct >> simp[brounds_t_def, brounds_def] >> strip_tac >>
  ‘brounds_t lfd hw ifds m ws0 n = brounds lfd (pol_self hw) ifds (K F) m ws0 n’
    by (first_x_assum irule >> rpt strip_tac >>
        metis_tac[DECIDE “i < n ⇒ i < SUC n”]) >>
  pop_assum (fn th => REWRITE_TAC [th] >> assume_tac th) >>
  Cases_on ‘brounds lfd (pol_self hw) ifds (K F) m ws0 n’ >> simp[] >>
  Cases_on ‘x’ >> simp[] >>
  first_x_assum (qspecl_then [‘n’, ‘l’, ‘p’, ‘l0’, ‘l1’] mp_tac) >> gvs[]
QED

(* The run after n rounds while it is running, and round n's events *)
Definition bt_run_def:
  bt_run lfd hw ifds m ws0 n =
    case brounds_t lfd hw ifds m ws0 n of
    | SOME (BRun h ws evs logs) => (h, ws, evs, logs)
    | _ => ARB
End

Definition bround_evs_def:
  bround_evs lfd hw ifds m ws0 n =
    DROP (LENGTH (FST (SND (SND (bt_run lfd hw ifds m ws0 n)))))
         (FST (SND (SND (bt_run lfd hw ifds m ws0 (SUC n)))))
End

(* The run never sleeps *)
Definition bt_awake_def:
  bt_awake lfd hw ifds m ws0 ⇔
    ∀n. ∃h ws evs logs. brounds_t lfd hw ifds m ws0 n = SOME (BRun h ws evs logs)
End

Theorem bt_run_0[simp]:
  bt_run lfd hw ifds m ws0 0 = ([], ws0, [], [])
Proof
  simp[bt_run_def, brounds_t_def]
QED

Theorem bt_run_SUC:
  bt_awake lfd hw ifds m ws0 ⇒
  if hdl_room lfd (SND (FST (SND (bt_run lfd hw ifds m ws0 n))))
       (naccepts (new_actions (log_of m) (FST (bt_run lfd hw ifds m ws0 n)))) then
    ∃snap ws' log evs1.
      bround lfd (pol_self hw) T (ifds (FST (bt_run lfd hw ifds m ws0 n)))
        (FST (SND (bt_run lfd hw ifds m ws0 n)))
        (new_actions (log_of m) (FST (bt_run lfd hw ifds m ws0 n))) =
        SOME (BRound snap ws' log evs1) ∧
      bt_run lfd hw ifds m ws0 (SUC n) =
        (FST (bt_run lfd hw ifds m ws0 n) ++ [snap], ws',
         FST (SND (SND (bt_run lfd hw ifds m ws0 n))) ++ evs1,
         SND (SND (SND (bt_run lfd hw ifds m ws0 n))) ++ [log]) ∧
      bround_evs lfd hw ifds m ws0 n = evs1
  else
    bt_run lfd hw ifds m ws0 (SUC n) = bt_run lfd hw ifds m ws0 n ∧
    bround_evs lfd hw ifds m ws0 n = []
Proof
  strip_tac >> fs[bt_awake_def] >>
  first_assum (qspec_then ‘n’ strip_assume_tac) >>
  first_x_assum (qspec_then ‘SUC n’ mp_tac) >>
  fs[bt_run_def, bround_evs_def, brounds_t_def] >>
  Cases_on ‘hdl_room lfd (SND ws) (naccepts (new_actions (log_of m) h))’ >> fs[] >>
  Cases_on ‘bround lfd (pol_self hw) T (ifds h) ws (new_actions (log_of m) h)’ >> fs[] >>
  rename1 ‘SOME b’ >> Cases_on ‘b’ >> fs[rich_listTheory.DROP_LENGTH_APPEND]
QED

(* ------------------------------------------------------------------------
   The loop
   ------------------------------------------------------------------------ *)

(* The loop's state at round i, as values *)
Definition bstv_def:
  bstv p A lfd hw fds0 m ws0 (lfdv, hwv) h ps stv ⇔
    ∃fdsv psv cv.
      stv = Conv NONE [lfdv; hwv; fdsv; psv; cv] ∧
      LIST_TYPE NUM (MAP w2n (live fds0 (log_of m) h)) fdsv ∧ L1P ps psv ∧
      COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended m h) cv
End

(* MAIN: the loop, if it never sleeps, never terminates, and its I/O trace
   is, round by round, the events of bround_evs *)
Theorem run_pfb_div_spec:
  limited_parts l0_names p ∧ wf m ∧ l0_reach w0 w ∧ psmall lfd ps0 ∧
  bt_ok lfd hw (live fds0 (log_of m)) m (w, ps0) ∧ bt_awake lfd hw (live fds0 (log_of m)) m (w, ps0) ∧
  WORD lfd lfdv ∧ NUM hw hwv ∧ LIST_TYPE NUM (MAP w2n fds0) fdsv ∧
  L1P ps0 psv ∧ COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ⇒
  app (p:'ffi ffi_proj) run_pfb_v [Conv NONE [lfdv; hwv; fdsv; psv; cv]]
    (L0_EV w0 w evs0)
    (POSTd io. io = LAPPEND (fromList evs0) (LFLATTEN (LGENLIST
       (λi. fromList (bround_evs lfd hw (live fds0 (log_of m)) m (w, ps0) i)) NONE)))
Proof
  strip_tac >>
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "run_pfb" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then evs0 else bround_evs lfd hw (live fds0 (log_of m)) m (w, ps0) (i - 1)’ >>
  qexists_tac ‘λi stv. ∃fdsv psv cv.
                 stv = Conv NONE [lfdv; hwv; fdsv; psv; cv] ∧
                 LIST_TYPE NUM (MAP w2n (live fds0 (log_of m)
                   (FST (bt_run lfd hw (live fds0 (log_of m)) m (w, ps0) i)))) fdsv ∧
                 L1P (SND (FST (SND (bt_run lfd hw (live fds0 (log_of m)) m (w, ps0) i)))) psv ∧
                 l0_reach w0 (FST (FST (SND (bt_run lfd hw (live fds0 (log_of m)) m (w, ps0) i)))) ∧
                 COMP p SACT A (SNAPSHOT SREADY SRESP)
                   (suspended m (FST (bt_run lfd hw (live fds0 (log_of m)) m (w, ps0) i))) cv’ >>
  qexists_tac ‘λi. l0_enc w0 (FST (FST (SND (bt_run lfd hw (live fds0 (log_of m)) m (w, ps0) i))))’ >>
  qexists_tac ‘l0_next w0’ >>
  simp[] >> rpt conj_tac
  >- (simp[L0_EV_def] >> xsimpl)
  >- ((* one iteration: a round (step_pfb_spec), or the stop (step_pfb_stop_spec) *)
      rpt strip_tac >> gvs[] >>
      drule bt_run_SUC >> disch_then (qspec_then ‘i’ assume_tac) >>
      qabbrev_tac ‘r = bt_run lfd hw (live fds0 (log_of m)) m (w, ps0) i’ >>
      PairCases_on ‘r’ >> gvs[] >>
      ‘(suspended m r0 []).actions = new_actions (log_of m) r0’
        by simp[suspended_first_poll] >>
      reverse (Cases_on ‘hdl_room lfd r2 (naccepts (new_actions (log_of m) r0))’) >> gvs[]
      >- (sg ‘app p step_pfb_v [Conv NONE [lfdv; hwv; fdsv'; psv'; cv']] (L0_EV w0 r1 [])
                (POSTv v. &(v = Conv NONE [lfdv; hwv; fdsv'; psv'; cv']) * L0_EV w0 r1 [])’
          >- (irule step_pfb_stop_spec >> simp[] >> metis_tac[]) >>
          gvs[L0_EV_def, SEP_CLAUSES] >>
          xlet ‘POSTv v. &(v = Conv NONE [lfdv; hwv; fdsv'; psv'; cv']) *
                         (one (FFI_part (l0_enc w0 r1) (l0_next w0) l0_names []) *
                          &l0_reach w0 r1)’
          >- (qpat_x_assum ‘app _ step_pfb_v _ _ _’ xapp_spec >> xsimpl) >>
          xvar >> xsimpl) >>
      PairCases_on ‘ws'’ >> gvs[] >>
      sg ‘app p step_pfb_v [Conv NONE [lfdv; hwv; fdsv'; psv'; cv']] (L0_EV w0 r1 [])
            (POSTv v.
               &(∃fdsv2 psv2 cv2. v = Conv NONE [lfdv; hwv; fdsv2; psv2; cv2] ∧
                   LIST_TYPE NUM (MAP w2n (live_round (live fds0 (log_of m) r0) (suspended m r0 []).actions snap.results)) fdsv2 ∧
                   L1P ws'1 psv2 ∧
                   COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended (suspended m r0) [snap]) cv2) *
               L0_EV w0 ws'0 ([] ++ bround_evs lfd hw (live fds0 (log_of m)) m (w,ps0) i))’
      >- (irule step_pfb_spec >> simp[] >> metis_tac[]) >>
      gvs[suspended_suspended_one, GSYM live_SNOC, L0_EV_def, SEP_CLAUSES] >>
      xlet ‘POSTv v.
              &(∃fdsv2 psv2 cv2. v = Conv NONE [lfdv; hwv; fdsv2; psv2; cv2] ∧
                  LIST_TYPE NUM (MAP w2n (live fds0 (log_of m) (r0 ++ [snap]))) fdsv2 ∧
                  L1P ws'1 psv2 ∧
                  COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended m (r0 ++ [snap])) cv2) *
              (one (FFI_part (l0_enc w0 ws'0) (l0_next w0) l0_names
                      (bround_evs lfd hw (live fds0 (log_of m)) m (w,ps0) i)) *
               &l0_reach w0 ws'0)’
      >- (qpat_x_assum ‘app _ step_pfb_v _ _ _’ xapp_spec >> xsimpl) >>
      xvar >> xsimpl >> rpt strip_tac >> gvs[] >> xsimpl)
  >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
     simp[combinTheory.o_DEF]
QED

(* MAIN: the loop, if its run sleeps, stops in the final blocking poll,
   with the events before it *)
Theorem run_pfb_sleep_spec:
  limited_parts l0_names p ∧ wf m ∧ l0_reach w0 w ∧ psmall lfd ps0 ∧
  bt_ok lfd hw (live fds0 (log_of m)) m (w, ps0) ∧
  brounds_t lfd hw (live fds0 (log_of m)) m (w, ps0) n = SOME (BSlept h evs cb) ∧
  WORD lfd lfdv ∧ NUM hw hwv ∧ LIST_TYPE NUM (MAP w2n fds0) fdsv ∧
  L1P ps0 psv ∧ COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ⇒
  app (p:'ffi ffi_proj) run_pfb_v [Conv NONE [lfdv; hwv; fdsv; psv; cv]]
    (L0_EV w0 w evs0)
    (POSTf nm. λc b. &(nm = «sys_poll» ∧ (c, b) = cb) *
                   (SEP_EXISTS w1. L0_EV w0 w1 (evs0 ++ evs)) * GC)
Proof
  strip_tac >>
  ‘∀k i hi wi psi evsi logsi stv.
     brounds_t lfd hw (live fds0 (log_of m)) m (w, ps0) i = SOME (BRun hi (wi, psi) evsi logsi) ∧
     brounds_t lfd hw (live fds0 (log_of m)) m (w, ps0) (i + k) = SOME (BSlept h evs cb) ∧
     (∃fdsv psv cv. stv = Conv NONE [lfdv; hwv; fdsv; psv; cv] ∧
        LIST_TYPE NUM (MAP w2n (live fds0 (log_of m) hi)) fdsv ∧ L1P psi psv ∧
        COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended m hi) cv) ⇒
     app p run_pfb_v [stv] (L0_EV w0 wi (evs0 ++ evsi))
       (POSTf nm. λc b. &(nm = «sys_poll» ∧ (c, b) = cb) *
                      (SEP_EXISTS w1. L0_EV w0 w1 (evs0 ++ evs)) * GC)’
    suffices_by
      (disch_then (qspecl_then [‘n’, ‘0’] mp_tac) >> simp[brounds_t_def] >>
       disch_then irule >> metis_tac[]) >>
  Induct >> rpt strip_tac >> gvs[] >>
  ‘(suspended m hi []).actions = new_actions (log_of m) hi’ by simp[suspended_first_poll] >>
  ‘∀v. COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended m hi) v ⇒ T’ by simp[] >>
  qpat_x_assum ‘brounds_t _ _ _ _ _ (i + SUC k) = _’ mp_tac >>
  simp[Once (DECIDE “i + SUC k = SUC i + k”)] >> strip_tac >>
  Cases_on ‘brounds_t lfd hw (live fds0 (log_of m)) m (w, ps0) (SUC i)’
  >- (‘∀j. brounds_t lfd hw (live fds0 (log_of m)) m (w, ps0) (SUC i + j) = NONE’
        by (Induct >> fs[ADD_CLAUSES, brounds_t_def]) >> gvs[]) >>
  rename1 ‘SOME r’ >>
  qpat_assum ‘brounds_t _ _ _ _ _ (SUC i) = _’ mp_tac >>
  ONCE_REWRITE_TAC [brounds_t_def] >>
  qpat_assum ‘brounds_t _ _ _ _ _ i = _’ (fn th => REWRITE_TAC [th]) >>
  simp[] >> IF_CASES_TAC >> simp[]
  >- ((* a round, or the sleep *)
      strip_tac >>
      Cases_on ‘bround lfd (pol_self hw) T (live fds0 (log_of m) hi) (wi, psi) (new_actions (log_of m) hi)’ >>
      gvs[] >> rename1 ‘bround _ _ _ _ _ _ = SOME bb’ >> Cases_on ‘bb’ >> gvs[]
      >- ((* a round: the step, then the loop from round i + 1 *)
          rename1 ‘bround _ _ _ _ _ _ = SOME (BRound snap ws' lg evs1)’ >> PairCases_on ‘ws'’ >>
          xcf_with_def (fetch "honestL1BProg" "run_pfb_v_def") >>
          xlet ‘POSTv v.
                  &(∃fdsv2 psv2 cv2. v = Conv NONE [lfdv; hwv; fdsv2; psv2; cv2] ∧
                      LIST_TYPE NUM (MAP w2n (live_round (live fds0 (log_of m) hi) (suspended m hi []).actions snap.results)) fdsv2 ∧
                      L1P ws'1 psv2 ∧
                      COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended (suspended m hi) [snap]) cv2) *
                  L0_EV w0 ws'0 (evs0 ++ evsi ++ evs1)’
          >- (xapp_spec step_pfb_spec >> xsimpl >> gvs[] >> metis_tac[]) >>
          gvs[suspended_suspended_one, GSYM live_SNOC] >>
          first_x_assum (qspecl_then [‘SUC i’] mp_tac) >> simp[] >>
          disch_then (qspec_then ‘Conv NONE [lfdv; hwv; fdsv2; psv2; cv2]’ mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          xapp >> xsimpl) >>
      (* the sleep *)
      xcf_with_def (fetch "honestL1BProg" "run_pfb_v_def") >>
      rename1 ‘bround _ _ _ _ _ _ = SOME (BAsleep sevs scb)’ >>
      ‘brounds_t lfd hw (live fds0 (log_of m)) m (w, ps0) (k + SUC i) = SOME (BSlept hi (evsi ++ sevs) scb)’
        by (qid_spec_tac ‘k’ >> Induct >> fs[ADD_CLAUSES, brounds_t_def]) >>
      gvs[] >>
      xlet ‘POSTf nm. λc b. &(nm = «sys_poll» ∧ (c, b) = cb) *
                          (SEP_EXISTS w1. L0_EV w0 w1 (evs0 ++ evsi ++ sevs)) * GC’
      >- (xapp_spec step_pfb_sleep_spec >> xsimpl >> gvs[] >> metis_tac[]) >>
      xsimpl) >>
  (* no room: the step does nothing, then the loop from round i + 1 *)
  strip_tac >> gvs[] >>
  xcf_with_def (fetch "honestL1BProg" "run_pfb_v_def") >>
  xlet ‘POSTv v. &(v = Conv NONE [lfdv; hwv; fdsv'; psv'; cv']) * L0_EV w0 wi (evs0 ++ evsi)’
  >- (xapp_spec step_pfb_stop_spec >>
      xsimpl >> metis_tac[]) >>
  first_x_assum (qspecl_then [‘SUC i’] mp_tac) >> simp[] >>
  disch_then (qspec_then ‘Conv NONE [lfdv; hwv; fdsv'; psv'; cv']’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> xapp >> xsimpl
QED
