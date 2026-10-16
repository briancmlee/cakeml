(*
  CF specs of the GC chat server (asyncChatGCProg): gc_server implements
  srelabel (gc_server lfd).  Only the hub is new: the tap and the query
  step (gc_tap_s_TAP, gdelta3_DELTA); with_tap, the skeleton and the
  handler are asyncChatSpec's.
*)
Theory asyncChatGCSpec
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM4Approx asyncM3World asyncM3Prog asyncM3Loop
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4SockApprox
  asyncM4SockServer asyncWithStore asyncWithTap asyncWithTapStep
  asyncChatSW asyncChatModel asyncChatSockModel asyncChatProg asyncChatSpec
  asyncChatGC asyncChatGCProg ml_translator mlstring std_prelude
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncChatGCProg"

val eq_string_v_thm =
  MATCH_MP (DISCH_ALL (fetch "mlbasicsProg" "eq_v_thm"))
           (EqualityType_NUM_BOOL |> CONJUNCTS |> el 6);

(* ------------------------------------------------------------------------
   The GC server in the socket vocabulary (model)
   ------------------------------------------------------------------------ *)

Definition gc_tap_s_def:
  gc_tap_s st a r = gc_tap st (unsfa a) (sfr r)
End

Theorem n2w_MOD64[local]:
  (n2w (n MOD 18446744073709551616) : word64) = n2w n
Proof
  ONCE_REWRITE_TAC[GSYM wordsTheory.n2w_mod] >> simp[]
QED

Theorem gc_tap_s_sfa:
  gc_tap_s st (sfa a) r = gc_tap st a (sfr r)
Proof
  Cases_on ‘a’ >> simp[gc_tap_s_def, sfa_def, unsfa_def] >>
  simp[gc_tap_def, gc_tap0_def] >> every_case_tac >> simp[n2w_MOD64]
QED

Theorem srelabel_gc_server:
  srelabel (gc_server lfd) =
  with_tap gc_tap_s gc_delta empty_gstore (krelabel (chat_inner lfd))
Proof
  simp[gc_server_def] >> irule relabel_with_tap >> simp[gc_tap_s_sfa]
QED

Theorem wf_sgc_server:
  wf (srelabel (gc_server lfd))
Proof
  simp[srelabel_gc_server] >> irule wf_with_tap >> simp[wf_kchat_inner]
QED

(* The socket-level tap, case by case *)
Theorem gc_tap_s_eqs:
  gc_tap_s st (Read c n) (Got (SOME bs)) =
    (if bs = [] then gcollect st else gtap_read st (w2n c) (MAP (CHR o w2n) bs)) ∧
  gc_tap_s st (Accept l) (Accepted (SOME c)) = gtap_accept st (w2n c) ∧
  gc_tap_s st (Read c n) (Got NONE) = gcollect st ∧
  gc_tap_s st (Read c n) (Accepted ao) = gcollect st ∧
  gc_tap_s st (Read c n) Wrote = gcollect st ∧
  gc_tap_s st (Accept l) (Accepted NONE) = gcollect st ∧
  gc_tap_s st (Accept l) (Got go) = gcollect st ∧
  gc_tap_s st (Accept l) Wrote = gcollect st ∧
  gc_tap_s st (Write c bs') r = gcollect st
Proof
  conj_tac
  >- (rw[gc_tap_s_def, unsfa_def, sfr_def, gtap_read_thm] >>
      irule gtap_other_thm >> simp[]) >>
  conj_tac >- simp[gc_tap_s_def, unsfa_def, sfr_def, gtap_accept_thm] >>
  rpt conj_tac >>
  TRY (Cases_on ‘ao’) >> TRY (Cases_on ‘go’) >>
  TRY (Cases_on ‘r’ >> TRY (rename1 ‘Got oo’ >> Cases_on ‘oo’) >>
       TRY (rename1 ‘Accepted oa’ >> Cases_on ‘oa’)) >>
  simp[gc_tap_s_def, unsfa_def, sfr_def] >>
  rw[] >> irule gtap_other_thm >> simp[]
QED

(* ------------------------------------------------------------------------
   The hub in CakeML
   ------------------------------------------------------------------------ *)

Overload GSTORE = “ASYNCCHATGC_GSTORE_TYPE”

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

(* MAIN: the CakeML tap implements gc_tap_s *)
Theorem gc_tap_s_TAP:
  TAP (p:'ffi ffi_proj) gc_tap_s GSTORE SACT SRESP gc_tap_s_v
Proof
  rw[TAP_def] >> xcf "gc_tap_s" (get_ml_prog_state ()) >>
  Cases_on ‘a’ >> Cases_on ‘r’ >> gvs[SACT_def, SRESP_def] >>
  TRY (rename1 ‘OPTION_MAP _ ro’ >> Cases_on ‘ro’) >> gvs[OPTION_TYPE_def] >>
  rpt xmatch >>
  (* the cases that only collect *)
  TRY (simp[gc_tap_s_eqs] >> xapp >> xsimpl >> qexists_tac ‘s’ >> simp[] >> NO_TAC) >>
  (* an accepted connection *)
  TRY (simp[gc_tap_s_eqs, GSYM gtap_accept_t_def] >>
       xlet ‘POSTv tv. &PAIR_TYPE GSTORE NUM (s, w2n x) tv’
       >- (xcon >> xsimpl >> fs[PAIR_TYPE_def]) >>
       xapp >> xsimpl >> qexists_tac ‘(s, w2n x)’ >> fs[] >> NO_TAC) >>
  (* a read with data, or EOF *)
  rename1 ‘STRING_TYPE (bytes_str bs) sv'’ >>
  xlet ‘POSTv bv. &BOOL (bs = []) bv’
  >- (xapp_spec eq_string_v_thm >> xsimpl >>
      qexists_tac ‘bytes_str bs’ >> simp[] >>
      Cases_on ‘bs’ >> simp[]) >>
  xif
  >- (simp[gc_tap_s_eqs] >> xapp >> xsimpl >> qexists_tac ‘s’ >> simp[]) >>
  xlet ‘POSTv cv. &LIST_TYPE CHAR (MAP (CHR o w2n) bs) cv’
  >- (xapp >> xsimpl >> qexists_tac ‘bytes_str bs’ >> fs[explode_bytes_str]) >>
  simp[gc_tap_s_eqs, GSYM gtap_read_t_def] >>
  xlet ‘POSTv tv. &PAIR_TYPE NUM (LIST_TYPE CHAR) (w2n c, MAP (CHR o w2n) bs) tv’
  >- (xcon >> xsimpl >> simp[PAIR_TYPE_def]) >>
  xlet ‘POSTv tv. &PAIR_TYPE GSTORE (PAIR_TYPE NUM (LIST_TYPE CHAR))
                     (s, w2n c, MAP (CHR o w2n) bs) tv’
  >- (xcon >> xsimpl >> fs[PAIR_TYPE_def]) >>
  xapp >> xsimpl >> qexists_tac ‘(s, w2n c, MAP (CHR o w2n) bs)’ >> fs[]
QED

(* MAIN: the translated query step implements gc_delta *)
Theorem gdelta3_DELTA:
  DELTA (p:'ffi ffi_proj) gc_delta GSTORE CQRY CANS gdelta3_v
Proof
  rw[DELTA_def, GSYM gdelta2_thm] >> xcf "gdelta3" (get_ml_prog_state ()) >>
  xlet ‘POSTv tv. &PAIR_TYPE GSTORE CQRY (s, q) tv’
  >- (xcon >> xsimpl >> simp[PAIR_TYPE_def]) >>
  xapp >> xsimpl >> qexists_tac ‘(s, q)’ >> simp[gdelta2_t_def] >>
  Cases_on ‘gdelta2 s q’ >> rw[] >> fs[PAIR_TYPE_def]
QED

(* MAIN: the GC chat server implements the model's gc_server, in the socket
   vocabulary *)
Theorem gc_server_spec:
  NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) gc_server_v [lfdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (gc_server lfd)) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "asyncChatGCProg" "gc_server_v_def") >>
  simp[srelabel_gc_server] >>
  xlet ‘POSTv cv. &COMP p CSACT UNIT_TYPE CSSNAP (krelabel (chat_inner lfd)) cv’
  >- (simp[chat_inner_def] >> xapp_spec kcserver_with_spec >> simp[] >>
      simp[CHANDLER_def, wf_chat_handler] >> rpt strip_tac >>
      xapp_spec chandler_spec >> simp[]) >>
  ‘app p with_tap_v [gc_tap_s_v; gdelta3_v; empty_gstore_v; cv] emp
     (POSTv v. &COMP p SACT UNIT_TYPE SSNAP
                 (with_tap gc_tap_s gc_delta empty_gstore
                    (krelabel (chat_inner lfd))) v)’
    by (irule with_tap_spec >> simp[wf_kchat_inner] >>
        irule_at Any gc_tap_s_TAP >> irule_at Any gdelta3_DELTA >>
        irule_at Any (fetch "asyncChatGCProg" "empty_gstore_v_thm") >>
        first_assum (irule_at Any)) >>
  qpat_x_assum ‘app _ with_tap_v _ _ _’ xapp_spec >> xsimpl
QED
