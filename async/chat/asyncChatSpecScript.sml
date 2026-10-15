(*
  CF specs of the chat server (asyncChatProg): chat_server implements
  srelabel (chat_server lfd).

  - with_tap_spec (generic): for any store representation STORE, any
    CakeML tap implementing σ (TAP) and any CakeML step implementing δ
    (DELTA), with_tap implements the model's with_tap σ δ s0 m, if its
    argument implements m.  Proved by the depth-indexed technique
    (asyncM4Approx): the residual wt_res carries the store in its closure;
    with_tap_suspended (asyncWithTapStep) is the model's account of one
    poll.
  - the skeleton, the reader, the write loop, the writer and the handler,
    in the vocabulary Sock sact | Kv (fd, cquery);
  - chat_server_spec: the instance.
*)
Theory asyncChatSpec
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM4Approx asyncM3World asyncM3Prog asyncM3Loop
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4SockApprox
  asyncM4SockServer asyncWithStore asyncWithTap asyncWithTapStep
  asyncChatSW asyncChatModel asyncChatSockModel asyncChatProg
  ml_translator mlstring std_prelude
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncChatProg"

val eq_string_v_thm =
  MATCH_MP (DISCH_ALL (fetch "mlbasicsProg" "eq_v_thm"))
           (EqualityType_NUM_BOOL |> CONJUNCTS |> el 6);

(* ------------------------------------------------------------------------
   The vocabulary: Sock a | Kv q, and SockR r | KvR b
   ------------------------------------------------------------------------ *)

local
  val env = get_env (get_ml_prog_state ())
  fun stamp_of c =
    EVAL “nsLookup (^env).c (Short ^c)” |> concl |> rhs
    |> optionSyntax.dest_some |> pairSyntax.dest_pair |> snd
in
  val sock_stamp = stamp_of “«Sock»”
  val kv_stamp = stamp_of “«Kv»”
  val sockr_stamp = stamp_of “«Sockr»”
  val kvr_stamp = stamp_of “«Kvr»”
end

Definition KACT_def:
  KACT ACT QRY (Sock a) v = (∃av. v = Conv (SOME ^sock_stamp) [av] ∧ ACT a av) ∧
  KACT ACT QRY (Kv q) v = (∃qv. v = Conv (SOME ^kv_stamp) [qv] ∧ QRY q qv)
End

Definition KRES_def:
  KRES RES ANS (SockR r) v = (∃rv. v = Conv (SOME ^sockr_stamp) [rv] ∧ RES r rv) ∧
  KRES RES ANS (KvR b) v = (∃bv. v = Conv (SOME ^kvr_stamp) [bv] ∧ ANS b bv)
End

Overload CQRY = “PAIR_TYPE NUM ASYNCCHATMODEL_CQUERY_TYPE”
Overload CANS = “ASYNCCHATMODEL_CANSWER_TYPE”
Overload CSACT = “KACT SACT CQRY”
Overload CSRESP = “KRES SRESP CANS”
Overload CSSNAP = “SNAPSHOT SREADY CSRESP”

(* DELTA p δ STORE QRY ANS deltav: deltav implements the query step δ *)
Definition DELTA_def:
  DELTA (p:'ffi ffi_proj) δ STORE QRY ANS deltav ⇔
    ∀s sv q qv. STORE s sv ∧ QRY q qv ⇒
      app p deltav [sv; qv] emp
        (POSTv v. &(∃bv sv'. v = Conv NONE [bv; sv'] ∧ ANS (FST (δ s q)) bv ∧
                             STORE (SND (δ s q)) sv'))
End

(* TAP p σ STORE ACT RES sigmav: sigmav implements the tap σ *)
Definition TAP_def:
  TAP (p:'ffi ffi_proj) σ STORE ACT RES sigmav ⇔
    ∀s sv a av r rv. STORE s sv ∧ ACT a av ∧ RES r rv ⇒
      app p sigmav [sv; av; rv] emp (POSTv v. &STORE (σ s a r) v)
End

(* ------------------------------------------------------------------------
   with_tap
   ------------------------------------------------------------------------ *)

Theorem wt_run_spec:
  ∀acts actsv st stv rs rsv.
    TAP p σ STORE ACT RES sigmav ∧ DELTA p δ STORE QRY ANS deltav ∧
    LIST_TYPE (KACT ACT QRY) acts actsv ∧ STORE st stv ∧ LIST_TYPE RES rs rsv ⇒
    app (p:'ffi ffi_proj) wt_run_v [sigmav; deltav; stv; actsv; rsv] emp
      (POSTv v. &(∃bsv st2v. v = Conv NONE [bsv; st2v] ∧
                   LIST_TYPE ANS (FST (run_tap σ δ st acts rs)) bsv ∧
                   STORE (SND (run_tap σ δ st acts rs)) st2v))
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "asyncChatProg" "wt_run_v_def") >>
  gvs[LIST_TYPE_def] >> xmatch
  >- (rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl >>
      simp[run_tap_def, LIST_TYPE_def]) >>
  Cases_on ‘h’ >> gvs[KACT_def] >> xmatch
  >- (Cases_on ‘rs’ >> gvs[LIST_TYPE_def] >> xmatch
      >- (xlet ‘POSTv nv. &LIST_TYPE RES [] nv’
          >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
          xapp >> xsimpl >> qexistsl [‘st’, ‘[]’] >> simp[run_tap_def]) >>
      rename1 ‘RES r rv’ >>
      xlet ‘POSTv sv'. &STORE (σ st a r) sv'’
      >- (gvs[TAP_def] >> xapp >> xsimpl >> metis_tac[]) >>
      xapp >> xsimpl >> qexistsl [‘σ st a r’, ‘t’] >> simp[run_tap_def]) >>
  rename1 ‘QRY q qv’ >>
  xlet ‘POSTv v. &(∃bv sv'. v = Conv NONE [bv; sv'] ∧ ANS (FST (δ st q)) bv ∧
                            STORE (SND (δ st q)) sv')’
  >- (gvs[DELTA_def] >> xapp >> simp[]) >>
  gvs[] >> xmatch >>
  xlet ‘POSTv v. &(∃bsv st2v. v = Conv NONE [bsv; st2v] ∧
                   LIST_TYPE ANS (FST (run_tap σ δ (SND (δ st q)) acts rs)) bsv ∧
                   STORE (SND (run_tap σ δ (SND (δ st q)) acts rs)) st2v)’
  >- (xapp >> xsimpl >> qexistsl [‘SND (δ st q)’, ‘rs’] >> simp[]) >>
  gvs[] >> xmatch >> rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl >>
  simp[run_tap_def] >> rpt (pairarg_tac >> gvs[]) >> fs[LIST_TYPE_def]
QED

Theorem wt_merge_spec:
  ∀acts actsv rs rsv ans ansv.
    LIST_TYPE (KACT ACT QRY) acts actsv ∧ LIST_TYPE RES rs rsv ∧
    LIST_TYPE ANS ans ansv ⇒
    app (p:'ffi ffi_proj) wt_merge_v [actsv; rsv; ansv] emp
      (POSTv v. &LIST_TYPE (KRES RES ANS) (merge acts rs ans) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "asyncChatProg" "wt_merge_v_def") >>
  gvs[LIST_TYPE_def] >> xmatch
  >- (xcon >> xsimpl >> simp[merge_def, LIST_TYPE_def]) >>
  Cases_on ‘h’ >> gvs[KACT_def] >> xmatch
  >- (Cases_on ‘rs’ >> gvs[LIST_TYPE_def] >> xmatch
      >- (xcon >> xsimpl >> simp[merge_def, LIST_TYPE_def]) >>
      xlet ‘POSTv v. &LIST_TYPE (KRES RES ANS) (merge acts t ans) v’
      >- (xapp >> simp[] >> metis_tac[]) >>
      xlet ‘POSTv v. &KRES RES ANS (SockR h) v’
      >- (xcon >> xsimpl >> simp[KRES_def]) >>
      xcon >> xsimpl >> simp[merge_def, LIST_TYPE_def]) >>
  Cases_on ‘ans’ >> gvs[LIST_TYPE_def] >> xmatch
  >- (xcon >> xsimpl >> simp[merge_def, LIST_TYPE_def]) >>
  xlet ‘POSTv v. &LIST_TYPE (KRES RES ANS) (merge acts rs t) v’
  >- (xapp >> simp[] >> metis_tac[]) >>
  xlet ‘POSTv v. &KRES RES ANS (KvR h) v’
  >- (xcon >> xsimpl >> simp[KRES_def]) >>
  xcon >> xsimpl >> simp[merge_def, LIST_TYPE_def]
QED

Theorem wt_socks_spec:
  ∀acts actsv.
    LIST_TYPE (KACT ACT QRY) acts actsv ⇒
    app (p:'ffi ffi_proj) wt_socks_v [actsv] emp
      (POSTv v. &LIST_TYPE ACT (socks acts) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "asyncChatProg" "wt_socks_v_def") >>
  gvs[LIST_TYPE_def] >> xmatch
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  Cases_on ‘h’ >> gvs[KACT_def] >> xmatch
  >- (xlet ‘POSTv v. &LIST_TYPE ACT (socks acts) v’ >- (xapp >> simp[]) >>
      xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xapp >> simp[]
QED

(* MAIN (helper): the residual, up to depth n *)
Theorem wt_res_spec_d:
  ∀n m sv st stv actsv.
    TAP p σ STORE ACT RES sigmav ∧ DELTA p δ STORE QRY ANS deltav ∧ wf m ∧
    STEPA p (KACT ACT QRY) A (SNAPSHOT READY (KRES RES ANS)) m sv ∧
    STORE st stv ∧ LIST_TYPE (KACT ACT QRY) (m []).actions actsv ⇒
    app (p:'ffi ffi_proj) wt_res_v [sigmav; deltav; stv; actsv; sv] emp
      (POSTv v. &STEPAd p ACT A (SNAPSHOT READY RES) n (with_tap σ δ st m) v)
Proof
  completeInduct_on ‘n’ >> rpt strip_tac >>
  xcf_with_def (fetch "asyncChatProg" "wt_res_v_def") >>
  qpat_x_assum ‘STEPA _ _ _ _ m sv’ (strip_assume_tac o ONCE_REWRITE_RULE [STEPA_cases]) >>
  gvs[]
  >- ((* finished *)
      xmatch >> xcon >> xsimpl >>
      simp[with_tap_finished, STEPAd_finished]) >>
  (* pending: the closure *)
  xmatch >> xfun ‘f’ >> xcon >> xsimpl >>
  Cases_on ‘n’ >> simp[STEPAd_def, with_tap_first] >>
  rename1 ‘STEPAd _ _ _ _ n’ >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
  gvs[SNAPSHOT_def] >> xmatch >>
  qabbrev_tac ‘bs = FST (first_tap σ δ st m w)’ >>
  qabbrev_tac ‘st2 = SND (first_tap σ δ st m w)’ >>
  xlet ‘POSTv v. &(∃bsv st2v. v = Conv NONE [bsv; st2v] ∧ LIST_TYPE ANS bs bsv ∧
                              STORE st2 st2v)’
  >- (‘app p wt_run_v [sigmav; deltav; stv; actsv; resv] emp
         (POSTv v. &(∃bsv st2v. v = Conv NONE [bsv; st2v] ∧
            LIST_TYPE ANS (FST (run_tap σ δ st (m []).actions w.results)) bsv ∧
            STORE (SND (run_tap σ δ st (m []).actions w.results)) st2v))’
        by (irule wt_run_spec >> simp[] >> metis_tac[]) >>
      qpat_x_assum ‘app _ wt_run_v _ _ _’ xapp_spec >> xsimpl >>
      simp[Abbr ‘bs’, Abbr ‘st2’, first_tap_def]) >>
  gvs[] >> xmatch >>
  xlet ‘POSTv v. &LIST_TYPE (KRES RES ANS) (merge (m []).actions w.results bs) v’
  >- (xapp_spec wt_merge_spec >> simp[] >> metis_tac[]) >>
  qabbrev_tac ‘w' = merged (m []).actions bs w’ >>
  xlet ‘POSTv v. &SNAPSHOT READY (KRES RES ANS) w' v’
  >- (xcon >> xsimpl >> simp[SNAPSHOT_def, Abbr ‘w'’, merged_def]) >>
  qpat_x_assum ‘∀w wv. _ ⇒ returns _ _ _ _’ (qspecl_then [‘w'’, ‘v'’] mp_tac) >>
  impl_tac >- fs[SNAPSHOT_def] >> strip_tac >>
  xlet ‘POSTv v. &POLL_RESULT (KACT ACT QRY) (STEPA p (KACT ACT QRY) A
                    (SNAPSHOT READY (KRES RES ANS))) (suspended m [w']) v’
  >- (gvs[returns_def] >> xapp >> simp[]) >>
  gvs[POLL_RESULT_def] >> xmatch >>
  xlet ‘POSTv v. &STEPAd p ACT A (SNAPSHOT READY RES) n
                    (with_tap σ δ st2 (suspended m [w'])) v’
  >- (first_x_assum (qspec_then ‘n’ mp_tac) >> simp[] >>
      disch_then (qspecl_then [‘suspended m [w']’, ‘sv’, ‘st2’, ‘st2v’, ‘av’] mp_tac) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[wf_suspended]) >>
      strip_tac >> qpat_x_assum ‘app _ wt_res_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv v. &LIST_TYPE ACT (socks (suspended m [w'] []).actions) v’
  >- (xapp_spec wt_socks_spec >> xsimpl >> first_assum (irule_at Any)) >>
  ‘suspended (with_tap σ δ st m) [w] = with_tap σ δ st2 (suspended m [w'])’
    by (simp[Abbr ‘w'’, Abbr ‘bs’, Abbr ‘st2’] >> irule with_tap_suspended >>
        first_assum ACCEPT_TAC) >>
  xcon >> xsimpl >> ASM_REWRITE_TAC[with_tap_first]
QED

(* MAIN: with_tap implements the model's with_tap *)
Theorem with_tap_spec:
  TAP p σ STORE ACT RES sigmav ∧ DELTA p δ STORE QRY ANS deltav ∧
  wf m ∧ STORE s0 stv ∧
  COMP p (KACT ACT QRY) A (SNAPSHOT READY (KRES RES ANS)) m cv ⇒
  app (p:'ffi ffi_proj) with_tap_v [sigmav; deltav; stv; cv] emp
    (POSTv v. &COMP p ACT A (SNAPSHOT READY RES) (with_tap σ δ s0 m) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >> gen_tac >>
  xcf_with_def (fetch "asyncChatProg" "with_tap_v_def") >>
  gvs[COMP_def, POLL_RESULT_def] >> xmatch >>
  xlet ‘POSTv v. &STEPAd p ACT A (SNAPSHOT READY RES) n (with_tap σ δ s0 m) v’
  >- (xapp_spec wt_res_spec_d >> simp[] >> metis_tac[]) >>
  xlet ‘POSTv v. &LIST_TYPE ACT (socks (m []).actions) v’
  >- (xapp_spec wt_socks_spec >> xsimpl >> first_assum (irule_at Any)) >>
  xcon >> xsimpl >> simp[COMPd_def, POLL_RESULT_def, with_tap_first]
QED

(* ------------------------------------------------------------------------
   The hub in CakeML
   ------------------------------------------------------------------------ *)

Overload CSTORE = “ASYNCCHATMODEL_CSTORE_TYPE”

Theorem bytes_str_chars[local]:
  bytes_str (MAP (n2w o ORD) s : word8 list) = implode s
Proof
  AP_TERM_TAC >> Induct_on ‘s’ >> simp[] >> rpt strip_tac >>
  ‘ORD h < 256’ by simp[ORD_BOUND] >> simp[CHR_ORD]
QED

Theorem explode_bytes_str[local]:
  explode (bytes_str bs) = MAP (CHR o w2n) bs
Proof
  simp[mlstringTheory.explode_implode]
QED

(* MAIN: the CakeML tap implements chat_tap_s *)
Theorem chat_tap_s_TAP:
  TAP (p:'ffi ffi_proj) chat_tap_s CSTORE SACT SRESP chat_tap_s_v
Proof
  rw[TAP_def] >> xcf "chat_tap_s" (get_ml_prog_state ()) >>
  Cases_on ‘a’ >> Cases_on ‘r’ >> gvs[SACT_def, SRESP_def] >>
  TRY (rename1 ‘OPTION_MAP _ ro’ >> Cases_on ‘ro’) >> gvs[OPTION_TYPE_def] >>
  rpt xmatch >>
  (* the cases that leave the store unchanged *)
  TRY (xvar >> xsimpl >>
       rw[chat_tap_s_def, unsfa_def, sfr_def, chat_tap_def] >> NO_TAC) >>
  (* an accepted connection *)
  TRY (simp[chat_tap_s_def, unsfa_def, sfr_def, tap_accept_thm,
            GSYM tap_accept_t_def] >>
       xlet ‘POSTv tv. &PAIR_TYPE CSTORE NUM (s, w2n x) tv’
       >- (xcon >> xsimpl >> fs[PAIR_TYPE_def]) >>
       xapp >> xsimpl >> qexists_tac ‘(s, w2n x)’ >> fs[] >> NO_TAC) >>
  (* a read with data, or EOF *)
  rename1 ‘STRING_TYPE (bytes_str bs) sv'’ >>
  xlet ‘POSTv bv. &BOOL (bs = []) bv’
  >- (xapp_spec eq_string_v_thm >> xsimpl >>
      qexists_tac ‘bytes_str bs’ >> simp[] >>
      Cases_on ‘bs’ >> simp[]) >>
  xif
  >- (xvar >> xsimpl >> gvs[chat_tap_s_def, unsfa_def, sfr_def, chat_tap_def]) >>
  xlet ‘POSTv cv. &LIST_TYPE CHAR (MAP (CHR o w2n) bs) cv’
  >- (xapp >> xsimpl >> qexists_tac ‘bytes_str bs’ >> fs[explode_bytes_str]) >>
  simp[chat_tap_s_def, unsfa_def, sfr_def, tap_read_thm, GSYM tap_read_t_def] >>
  xlet ‘POSTv tv. &PAIR_TYPE NUM (LIST_TYPE CHAR) (w2n c, MAP (CHR o w2n) bs) tv’
  >- (xcon >> xsimpl >> simp[PAIR_TYPE_def]) >>
  xlet ‘POSTv tv. &PAIR_TYPE CSTORE (PAIR_TYPE NUM (LIST_TYPE CHAR))
                     (s, w2n c, MAP (CHR o w2n) bs) tv’
  >- (xcon >> xsimpl >> fs[PAIR_TYPE_def]) >>
  xapp >> xsimpl >> qexists_tac ‘(s, w2n c, MAP (CHR o w2n) bs)’ >> fs[]
QED

(* MAIN: the translated query step implements chat_delta *)
Theorem delta3_DELTA:
  DELTA (p:'ffi ffi_proj) chat_delta CSTORE CQRY CANS delta3_v
Proof
  rw[DELTA_def, GSYM delta2_thm] >> xcf "delta3" (get_ml_prog_state ()) >>
  xlet ‘POSTv tv. &PAIR_TYPE CSTORE CQRY (s, q) tv’
  >- (xcon >> xsimpl >> simp[PAIR_TYPE_def]) >>
  xapp >> xsimpl >> qexists_tac ‘(s, q)’ >> simp[delta2_t_def] >>
  Cases_on ‘delta2 s q’ >> rw[] >> fs[PAIR_TYPE_def]
QED

(* ------------------------------------------------------------------------
   The skeleton and the handler
   ------------------------------------------------------------------------ *)

Theorem csreadable_spec:
  NUM fd fdv ⇒
  app (p:'ffi ffi_proj) sreadable_v [fdv] emp
    (POSTv v. &COMP p ACT UNIT_TYPE (SNAPSHOT SREADY R) (sreadable fd) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "asyncM4SockServer" "sreadable_v_def") >>
  xfun ‘f’ >> simp[sreadable_def] >>
  ‘∀w wv. SNAPSHOT SREADY R w wv ⇒
     returns p f [wv]
       (OPTION_TYPE UNIT_TYPE
          (if ∃c. c ∈ w.ready ∧ w2n c = fd then SOME () else NONE))’
    by (rpt strip_tac >> simp[returns_def] >>
        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
        gvs[SNAPSHOT_def, SREADY_def] >> xmatch >>
        xlet ‘POSTv bv. &BOOL (MEM fd (MAP w2n fds)) bv’
        >- (xapp >> metis_tac[]) >>
        xif >> rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl >>
        gvs[MEM_MAP] >> rw[OPTION_TYPE_def] >> fs[UNIT_TYPE_def] >>
        metis_tac[]) >>
  ‘app p Async_wait_v [f] emp
     (POSTv v. &COMP p ACT UNIT_TYPE (SNAPSHOT SREADY R)
        (wait (λs. if ∃c. c ∈ s.ready ∧ w2n c = fd then SOME () else NONE)) v)’
    by (irule Async_wait_spec >> simp[]) >>
  qpat_x_assum ‘app _ Async_wait_v _ _ _’ xapp_spec >> xsimpl
QED

(* return (), at any depth *)
val return_unit_tac =
  xlet ‘POSTv uv. &UNIT_TYPE () uv’ >- (xcon >> xsimpl) >>
  ‘app p Async_return_v [uv] emp
     (POSTv v. &COMP p CSACT UNIT_TYPE CSSNAP (return ()) v)’
    by (irule Async_return_spec >> simp[]) >>
  qpat_x_assum ‘app _ Async_return_v _ _ _’ xapp_spec >> xsimpl >>
  simp[COMP_IMP_COMPd];

(* emit a, for a CakeML action value av *)
fun emit_tac a =
  ‘app p Async_emit_v [av] emp
     (POSTv v. &COMP p CSACT CSRESP CSSNAP (emit ^a) v)’
    by (irule Async_emit_spec >> simp[]) >>
  qpat_x_assum ‘app _ Async_emit_v _ _ _’ xapp_spec >> xsimpl;

Theorem Async_bind_guarded_spec_any[local]:
  wf m ∧ (m []).result = NONE ∧ COMP p ACT A (SNAPSHOT READY R) m mv ∧
  (0 < n ⇒
   ∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPd p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) (n - 1) (g x))) ⇒
  app (p:'ffi ffi_proj) Async_bind_v [mv; gv] emp
    (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B (SNAPSHOT READY R) n
                (bind m g) v)
Proof
  Cases_on ‘n’ >> rpt strip_tac
  >- (irule Async_bind_guarded_spec_0 >> simp[] >> metis_tac[COMP_IMP_COMPd])
  >> irule Async_bind_guarded_spec_d >> gs[] >> qexists_tac ‘A’ >>
  simp[COMP_IMP_COMPd]
QED

(* CHANDLER p h hv: hv implements the handler h, on every connection *)
Definition CHANDLER_def:
  CHANDLER (p:'ffi ffi_proj) h hv ⇔
    (∀fd. wf (h fd)) ∧
    ∀fd fdv. NUM fd fdv ∧ fd < dimword(:64) ⇒
      app p hv [fdv] emp (POSTv v. &COMP p CSACT UNIT_TYPE CSSNAP (krelabel (h fd)) v)
End

(* MAIN (helper): the skeleton, up to depth n *)
Theorem kcserver_with_spec_d:
  ∀n lfd lfdv.
    CHANDLER p h hv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
    app (p:'ffi ffi_proj) cserver_with_v [hv; lfdv] emp
      (POSTv v. &COMPd p CSACT UNIT_TYPE CSSNAP n (krelabel (cserver_with h lfd)) v)
Proof
  completeInduct_on ‘n’ >> rpt strip_tac >>
  xcf_with_def (fetch "asyncChatProg" "cserver_with_v_def") >>
  simp_tac std_ss [Once kcserver_with_unfold] >>
  xfun ‘k1’ >>
  xlet ‘POSTv r. &COMP p CSACT UNIT_TYPE CSSNAP (sreadable lfd) r’
  >- (xapp_spec csreadable_spec >> xsimpl >> fs[]) >>
  qmatch_goalsub_abbrev_tac ‘bind (sreadable lfd) G’ >>
  ‘0 < n ⇒ ∀x xv. UNIT_TYPE x xv ⇒
          returns p k1 [xv] (COMPd p CSACT UNIT_TYPE CSSNAP (n - 1) (G x))’
    by (rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
        first_x_assum (qspec_then ‘n - 1’ mp_tac) >> simp[] >> strip_tac >>
        qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
        xfun ‘k2’ >>
        xlet ‘POSTv av0. &SACT (Accept (n2w lfd)) av0’
        >- (xcon >> xsimpl >> gs[SACT_def]) >>
        xlet ‘POSTv av. &CSACT (Sock (Accept (n2w lfd))) av’
        >- (xcon >> xsimpl >> simp[KACT_def]) >>
        xlet ‘POSTv ev. &COMP p CSACT CSRESP CSSNAP (emit (Sock (Accept (n2w lfd)))) ev’
        >- emit_tac “Sock (Accept (n2w lfd)) : (sact, num # cquery) kact” >>
        qmatch_goalsub_abbrev_tac ‘bind (emit _) G2’ >>
        ‘∀res resv. CSRESP res resv ⇒
           returns p k2 [resv] (COMPd p CSACT UNIT_TYPE CSSNAP (n - 1) (G2 res))’
          by (rpt strip_tac >> simp[returns_def, Abbr ‘G2’] >>
              qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
              Cases_on ‘res’ >> gvs[KRES_def]
              >- (rename1 ‘SRESP r0 rv’ >>
                  Cases_on ‘r0’ >> gvs[SRESP_def]
                  >~ [‘TypeStamp «Accepted» _’]
                  >- (rename1 ‘OPTION_MAP _ ro’ >> Cases_on ‘ro’ >>
                      gvs[OPTION_TYPE_def] >> xmatch
                      >- (xapp >> fs[])
                      >> rename1 ‘NUM (w2n c) cv’ >>
                      ‘∀fd. wf (h fd)’ by fs[CHANDLER_def] >>
                      xlet ‘POSTv sv. &COMPd p CSACT UNIT_TYPE CSSNAP (n - 1)
                                        (krelabel (cserver_with h lfd)) sv’
                      >- (xapp >> fs[]) >>
                      xlet ‘POSTv hv'. &COMP p CSACT UNIT_TYPE CSSNAP
                                         (krelabel (h (w2n c))) hv'’
                      >- (‘app p hv [cv] emp
                             (POSTv v. &COMP p CSACT UNIT_TYPE CSSNAP (krelabel (h (w2n c))) v)’
                            by (gvs[CHANDLER_def] >> first_x_assum irule >> simp[] >>
                                qspec_then ‘c’ assume_tac w2n_lt >> fs[]) >>
                          qpat_x_assum ‘app _ hv _ _ _’ xapp_spec >> xsimpl) >>
                      ‘app p async_both_v [hv'; sv] emp
                         (POSTv v. &COMPd p CSACT (PAIR_TYPE UNIT_TYPE UNIT_TYPE)
                                     CSSNAP (n - 1) (both (krelabel (h (w2n c)))
                                                    (krelabel (cserver_with h lfd))) v)’
                        by (irule async_both_spec_d >>
                            simp[wf_relabel, wf_cserver_with, COMP_IMP_COMPd]) >>
                      xlet ‘POSTv bv. &COMPd p CSACT (PAIR_TYPE UNIT_TYPE UNIT_TYPE)
                                        CSSNAP (n - 1) (both (krelabel (h (w2n c)))
                                                       (krelabel (cserver_with h lfd))) bv’
                      >- (qpat_x_assum ‘app _ async_both_v _ _ _’ xapp_spec >> xsimpl) >>
                      xfun ‘f’ >>
                      ‘app p async_map_v [f; bv] emp
                         (POSTv v. &COMPd p CSACT UNIT_TYPE CSSNAP (n - 1)
                                     (map (λp. ()) (both (krelabel (h (w2n c)))
                                                         (krelabel (cserver_with h lfd)))) v)’
                        by (irule async_map_spec_d >>
                            simp[wf_both, wf_relabel, wf_cserver_with] >>
                            qexists_tac ‘PAIR_TYPE UNIT_TYPE UNIT_TYPE’ >> simp[] >>
                            rpt strip_tac >> simp[returns_def] >>
                            qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
                            xcon >> xsimpl) >>
                      qpat_x_assum ‘app _ async_map_v _ _ _’ xapp_spec >> xsimpl) >>
                  xmatch >> xapp >> fs[]) >>
              xmatch >> xapp >> fs[]) >>
        ‘app p Async_bind_v [ev; k2] emp
           (POSTv v. &COMPd p CSACT UNIT_TYPE CSSNAP (n - 1)
                       (bind (emit (Sock (Accept (n2w lfd)))) G2) v)’
          by (irule Async_bind_spec_d >> simp[wf_emit] >>
              qexists_tac ‘CSRESP’ >> simp[COMP_IMP_COMPd] >> metis_tac[]) >>
        qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p Async_bind_v [r; k1] emp
     (POSTv v. &COMPd p CSACT UNIT_TYPE CSSNAP n (bind (sreadable lfd) G) v)’
    by (irule Async_bind_guarded_spec_any >> simp[wf_sreadable, sreadable_NIL] >>
        metis_tac[]) >>
  qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl
QED

Theorem kcserver_with_spec:
  CHANDLER p h hv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) cserver_with_v [hv; lfdv] emp
    (POSTv v. &COMP p CSACT UNIT_TYPE CSSNAP (krelabel (cserver_with h lfd)) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >>
  metis_tac[kcserver_with_spec_d]
QED

(* MAIN (helper): the reader, up to depth n *)
Theorem creader_spec_d:
  ∀n fd fdv.
    NUM fd fdv ∧ fd < dimword(:64) ⇒
    app (p:'ffi ffi_proj) creader_v [fdv] emp
      (POSTv v. &COMPd p CSACT UNIT_TYPE CSSNAP n (krelabel (reader fd)) v)
Proof
  completeInduct_on ‘n’ >> rpt strip_tac >>
  xcf_with_def (fetch "asyncChatProg" "creader_v_def") >>
  simp_tac std_ss [Once kreader_unfold] >>
  xfun ‘k1’ >>
  xlet ‘POSTv r. &COMP p CSACT UNIT_TYPE CSSNAP (sreadable fd) r’
  >- (xapp_spec csreadable_spec >> xsimpl >> fs[]) >>
  qmatch_goalsub_abbrev_tac ‘bind (sreadable fd) G’ >>
  ‘0 < n ⇒ ∀x xv. UNIT_TYPE x xv ⇒
     returns p k1 [xv] (COMPd p CSACT UNIT_TYPE CSSNAP (n - 1) (G x))’
    by (rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
        first_x_assum (qspec_then ‘n - 1’ mp_tac) >> simp[] >> strip_tac >>
        qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
        xfun ‘k2’ >>
        xlet ‘POSTv av0. &SACT (Read (n2w fd) bufsz) av0’
        >- (xcon >> xsimpl >> gs[SACT_def, bufsz_def, NUM_def, INT_def]) >>
        xlet ‘POSTv av. &CSACT (Sock (Read (n2w fd) bufsz)) av’
        >- (xcon >> xsimpl >> simp[KACT_def]) >>
        xlet ‘POSTv ev. &COMP p CSACT CSRESP CSSNAP (emit (Sock (Read (n2w fd) bufsz))) ev’
        >- emit_tac “Sock (Read (n2w fd) bufsz) : (sact, num # cquery) kact” >>
        qmatch_goalsub_abbrev_tac ‘bind (emit _) G2’ >>
        ‘∀res resv. CSRESP res resv ⇒
           returns p k2 [resv]
             (COMPd p CSACT UNIT_TYPE CSSNAP (n - 1) (G2 res))’
          by (rpt strip_tac >> simp[returns_def, Abbr ‘G2’] >>
              qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
              Cases_on ‘res’ >> gvs[KRES_def]
              >- (rename1 ‘SRESP r0 rv’ >> Cases_on ‘r0’ >> gvs[SRESP_def]
                  >~ [‘TypeStamp «Got» _’]
                  >- (rename1 ‘OPTION_MAP _ ro’ >> Cases_on ‘ro’ >>
                      gvs[OPTION_TYPE_def] >> xmatch
                      >- (xapp >> simp[])
                      >> rename1 ‘STRING_TYPE (bytes_str bs) sv’ >>
                      xlet ‘POSTv bv. &BOOL (bs = []) bv’
                      >- (xapp_spec eq_string_v_thm >> xsimpl >>
                          qexists_tac ‘bytes_str bs’ >> simp[] >>
                          Cases_on ‘bs’ >> simp[]) >>
                      xif
                      >- (gvs[] >> return_unit_tac) >>
                      xapp >> simp[]) >>
                  xmatch >> xapp >> simp[]) >>
              xmatch >> xapp >> simp[]) >>
        ‘app p Async_bind_v [ev; k2] emp
           (POSTv v. &COMPd p CSACT UNIT_TYPE CSSNAP (n - 1)
                       (bind (emit (Sock (Read (n2w fd) bufsz))) G2) v)’
          by (irule Async_bind_spec_d >> simp[wf_emit] >>
              qexists_tac ‘CSRESP’ >> simp[COMP_IMP_COMPd] >> metis_tac[]) >>
        qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p Async_bind_v [r; k1] emp
     (POSTv v. &COMPd p CSACT UNIT_TYPE CSSNAP n (bind (sreadable fd) G) v)’
    by (irule Async_bind_guarded_spec_any >> simp[wf_sreadable, sreadable_NIL] >>
        metis_tac[]) >>
  qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl
QED

(* MAIN (helper): the write loop, up to depth n *)
Theorem cwloop_spec_d:
  ∀n i iv fd fdv.
    NUM fd fdv ∧ fd < dimword(:64) ∧ NUM i iv ⇒
    app (p:'ffi ffi_proj) cwloop_v [fdv; iv] emp
      (POSTv v. &COMPd p CSACT UNIT_TYPE CSSNAP n (krelabel (wloop (fd, i))) v)
Proof
  completeInduct_on ‘n’ >> rpt strip_tac >>
  xcf_with_def (fetch "asyncChatProg" "cwloop_v_def") >>
  simp_tac std_ss [Once kwloop_unfold] >>
  xfun ‘k1’ >>
  xlet ‘POSTv qv0. &ASYNCCHATMODEL_CQUERY_TYPE (Fetch i) qv0’
  >- (xcon >> xsimpl >> fs[ASYNCCHATMODEL_CQUERY_TYPE_def]) >>
  xlet ‘POSTv qv. &CQRY (fd, Fetch i) qv’
  >- (xcon >> xsimpl >> fs[PAIR_TYPE_def]) >>
  xlet ‘POSTv av. &CSACT (Kv (fd, Fetch i)) av’
  >- (xcon >> xsimpl >> fs[KACT_def]) >>
  xlet ‘POSTv ev. &COMP p CSACT CSRESP CSSNAP (emit (Kv (fd, Fetch i))) ev’
  >- emit_tac “Kv (fd, Fetch i) : (sact, num # cquery) kact” >>
  qmatch_goalsub_abbrev_tac ‘bind (emit _) G’ >>
  ‘app p Async_bind_v [ev; k1] emp
     (POSTv v. &COMPd p CSACT UNIT_TYPE CSSNAP n (bind (emit (Kv (fd, Fetch i))) G) v)’
    by (irule Async_bind_guarded_spec_any >> simp[wf_emit, emit_needs_snapshot] >>
        qexists_tac ‘CSRESP’ >> rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
        qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
        Cases_on ‘x’ >> gvs[KRES_def] >> xmatch >>
        TRY (return_unit_tac >> NO_TAC) >>
        rename1 ‘CANS ans ansv’ >>
        Cases_on ‘ans’ >> gvs[ASYNCCHATMODEL_CANSWER_TYPE_def] >> xmatch >>
        TRY (return_unit_tac >> NO_TAC) >>
        rename1 ‘LIST_TYPE CHAR s sv’ >>
        Cases_on ‘s’ >> gvs[LIST_TYPE_def] >> xmatch
        >- (first_x_assum (qspec_then ‘n - 1’ mp_tac) >> simp[] >> strip_tac >>
            xapp >> simp[]) >>
        rename1 ‘CHAR c cv’ >> rename1 ‘LIST_TYPE CHAR cs csv’ >>
        ‘LIST_TYPE CHAR (c :: cs) (Conv (SOME (TypeStamp «::» 1)) [cv; csv])’
          by simp[LIST_TYPE_def] >>
        xfun ‘k2’ >>
        xlet ‘POSTv tv. &STRING_TYPE (implode (c :: cs)) tv’
        >- (xapp >> simp[LIST_TYPE_def] >> metis_tac[]) >>
        qabbrev_tac ‘bs = MAP ((n2w : num -> word8) o ORD) (c :: cs)’ >>
        xlet ‘POSTv av0. &SACT (Write (n2w fd) bs) av0’
        >- (xcon >> xsimpl >> gs[SACT_def, Abbr ‘bs’, bytes_str_chars]) >>
        qpat_x_assum ‘CSACT (Kv _) av’ kall_tac >>
        xlet ‘POSTv av. &CSACT (Sock (Write (n2w fd) bs)) av’
        >- (xcon >> xsimpl >> fs[KACT_def]) >>
        xlet ‘POSTv ev2. &COMP p CSACT CSRESP CSSNAP (emit (Sock (Write (n2w fd) bs))) ev2’
        >- emit_tac “Sock (Write (n2w fd) bs) : (sact, num # cquery) kact” >>
        ‘app p Async_bind_v [ev2; k2] emp
           (POSTv v. &COMPd p CSACT UNIT_TYPE CSSNAP (n - 1)
               (bind (emit (Sock (Write (n2w fd) bs)))
                     (λw. krelabel (wloop (fd, i + LENGTH (c :: cs))))) v)’
          by (irule Async_bind_guarded_spec_any >> simp[wf_emit, emit_needs_snapshot] >>
              qexists_tac ‘CSRESP’ >> rpt strip_tac >> simp[returns_def] >>
              qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
              xlet ‘POSTv lv. &NUM (LENGTH (c :: cs)) lv’
              >- (xapp >> xsimpl >> first_assum (irule_at Any) >>
                  simp[fetch "asyncChatProg" "clen_def"]) >>
              xlet ‘POSTv jv. &NUM (i + LENGTH (c :: cs)) jv’
              >- (xapp >> xsimpl >> gs[NUM_def] >>
                  rpt (first_assum (irule_at Any)) >>
                  simp[integerTheory.INT_ADD]) >>
              first_x_assum (qspec_then ‘n - 1 - 1’ mp_tac) >> simp[] >>
              strip_tac >> xapp >> simp[]) >>
        qpat_x_assum ‘app _ Async_bind_v [ev2; _] _ _’ xapp_spec >> xsimpl >>
        simp[Abbr ‘bs’]) >>
  qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl
QED

Theorem cwloop_spec:
  NUM fd fdv ∧ fd < dimword(:64) ∧ NUM i iv ⇒
  app (p:'ffi ffi_proj) cwloop_v [fdv; iv] emp
    (POSTv v. &COMP p CSACT UNIT_TYPE CSSNAP (krelabel (wloop (fd, i))) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[cwloop_spec_d]
QED

Theorem creader_spec:
  NUM fd fdv ∧ fd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) creader_v [fdv] emp
    (POSTv v. &COMP p CSACT UNIT_TYPE CSSNAP (krelabel (reader fd)) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[creader_spec_d]
QED

(* MAIN: the writer *)
Theorem cwriter_spec:
  NUM fd fdv ∧ fd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) cwriter_v [fdv] emp
    (POSTv v. &COMP p CSACT UNIT_TYPE CSSNAP (krelabel (writer fd)) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >> gen_tac >>
  xcf_with_def (fetch "asyncChatProg" "cwriter_v_def") >>
  simp_tac std_ss [kwriter_unfold] >>
  xfun ‘k1’ >>
  xlet ‘POSTv qv0. &ASYNCCHATMODEL_CQUERY_TYPE Start qv0’
  >- (xcon >> xsimpl >> fs[ASYNCCHATMODEL_CQUERY_TYPE_def]) >>
  xlet ‘POSTv qv. &CQRY (fd, Start) qv’
  >- (xcon >> xsimpl >> fs[PAIR_TYPE_def]) >>
  xlet ‘POSTv av. &CSACT (Kv (fd, Start)) av’
  >- (xcon >> xsimpl >> fs[KACT_def]) >>
  xlet ‘POSTv ev. &COMP p CSACT CSRESP CSSNAP (emit (Kv (fd, Start))) ev’
  >- emit_tac “Kv (fd, Start) : (sact, num # cquery) kact” >>
  qmatch_goalsub_abbrev_tac ‘bind (emit _) G’ >>
  ‘app p Async_bind_v [ev; k1] emp
     (POSTv v. &COMPd p CSACT UNIT_TYPE CSSNAP n (bind (emit (Kv (fd, Start))) G) v)’
    by (irule Async_bind_guarded_spec_any >> simp[wf_emit, emit_needs_snapshot] >>
        qexists_tac ‘CSRESP’ >> rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
        qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
        Cases_on ‘x’ >> gvs[KRES_def] >> xmatch >>
        TRY (return_unit_tac >> NO_TAC) >>
        rename1 ‘CANS ans ansv’ >>
        Cases_on ‘ans’ >> gvs[ASYNCCHATMODEL_CANSWER_TYPE_def] >> xmatch >>
        TRY (return_unit_tac >> NO_TAC) >>
        rename1 ‘NUM j jv’ >>
        ‘app p cwloop_v [fdv; jv] emp
           (POSTv v. &COMP p CSACT UNIT_TYPE CSSNAP (krelabel (wloop (fd, j))) v)’
          by (irule cwloop_spec >> simp[]) >>
        qpat_x_assum ‘app _ cwloop_v _ _ _’ xapp_spec >> xsimpl >>
        simp[COMP_IMP_COMPd]) >>
  qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl
QED

(* MAIN: the handler *)
Theorem chandler_spec:
  NUM fd fdv ∧ fd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) chandler_v [fdv] emp
    (POSTv v. &COMP p CSACT UNIT_TYPE CSSNAP (krelabel (chat_handler fd)) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >> gen_tac >>
  xcf_with_def (fetch "asyncChatProg" "chandler_v_def") >>
  simp_tac std_ss [kchat_handler_unfold] >>
  xlet ‘POSTv wv. &COMP p CSACT UNIT_TYPE CSSNAP (krelabel (writer fd)) wv’
  >- (xapp_spec cwriter_spec >> simp[]) >>
  xlet ‘POSTv rv. &COMP p CSACT UNIT_TYPE CSSNAP (krelabel (reader fd)) rv’
  >- (xapp_spec creader_spec >> simp[]) >>
  ‘app p async_both_v [rv; wv] emp
     (POSTv v. &COMPd p CSACT (PAIR_TYPE UNIT_TYPE UNIT_TYPE) CSSNAP n
                 (both (krelabel (reader fd)) (krelabel (writer fd))) v)’
    by (irule async_both_spec_d >>
        simp[wf_relabel, wf_reader, wf_writer, COMP_IMP_COMPd]) >>
  xlet ‘POSTv bv. &COMPd p CSACT (PAIR_TYPE UNIT_TYPE UNIT_TYPE) CSSNAP n
                    (both (krelabel (reader fd)) (krelabel (writer fd))) bv’
  >- (qpat_x_assum ‘app _ async_both_v _ _ _’ xapp_spec >> xsimpl) >>
  xfun ‘f’ >>
  ‘app p async_map_v [f; bv] emp
     (POSTv v. &COMPd p CSACT UNIT_TYPE CSSNAP n
                 (map (λp. ()) (both (krelabel (reader fd)) (krelabel (writer fd)))) v)’
    by (irule async_map_spec_d >>
        simp[wf_both, wf_relabel, wf_reader, wf_writer] >>
        qexists_tac ‘PAIR_TYPE UNIT_TYPE UNIT_TYPE’ >> simp[] >>
        rpt strip_tac >> simp[returns_def] >>
        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
        xcon >> xsimpl) >>
  qpat_x_assum ‘app _ async_map_v _ _ _’ xapp_spec >> xsimpl
QED

(* MAIN: the chat server implements the model's chat_server, in the socket
   vocabulary *)
Theorem chat_server_spec:
  NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) chat_server_v [lfdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (chat_server lfd)) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "asyncChatProg" "chat_server_v_def") >>
  simp[srelabel_chat_server] >>
  xlet ‘POSTv cv. &COMP p CSACT UNIT_TYPE CSSNAP (krelabel (chat_inner lfd)) cv’
  >- (simp[chat_inner_def] >> xapp_spec kcserver_with_spec >> simp[] >>
      simp[CHANDLER_def, wf_chat_handler] >> rpt strip_tac >>
      xapp_spec chandler_spec >> simp[]) >>
  ‘app p with_tap_v [chat_tap_s_v; delta3_v; empty_store_v; cv] emp
     (POSTv v. &COMP p SACT UNIT_TYPE SSNAP
                 (with_tap chat_tap_s chat_delta empty_store
                    (krelabel (chat_inner lfd))) v)’
    by (irule with_tap_spec >> simp[wf_kchat_inner] >>
        irule_at Any chat_tap_s_TAP >> irule_at Any delta3_DELTA >>
        irule_at Any (fetch "asyncChatProg" "empty_store_v_thm") >>
        first_assum (irule_at Any)) >>
  qpat_x_assum ‘app _ with_tap_v _ _ _’ xapp_spec >> xsimpl
QED
