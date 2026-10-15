(*
  Option C §2.3, model side: the declared interest of the Level 2 protocol
  server is finite at every history (so the loop's select set, the sorted
  list of it, covers it: asyncOCSel), and relabelling to sockets keeps
  quietness.

  finite2 c: c declares finitely many events after every history.  It holds
  of the primitives, is preserved by the combinators and by guarded
  recursion (finite2_fix2, as wf2_fix2), and by relabelling with sie.
*)
Theory asyncOCFinite
Ancestors
  pair list rich_list arithmetic option pred_set words
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncLoop2 asyncServer
  asyncM3World asyncM4Relabel asyncM4RelabelDist asyncM4SockModel
  asyncServerV asyncProto asyncProtoV asyncProtoV2 asyncOCRelabel
  asyncOCProtoModel
Libs
  BasicProvers wordsLib

Definition finite2_def:
  finite2 c ⇔ ∀h. FINITE (c.interest h)
End

Theorem finite2_return2:
  finite2 (return2 x)
Proof
  simp[finite2_def, return2_def]
QED

Theorem finite2_emit2:
  finite2 (emit2 a)
Proof
  simp[finite2_def, emit2_def]
QED

Theorem finite2_wait_on:
  finite2 (wait_on e p)
Proof
  simp[finite2_def, wait_on_def]
QED

Theorem finite2_map2:
  finite2 c ⇒ finite2 (map2 f c)
Proof
  simp[finite2_def, map2_def]
QED

Theorem finite2_bind2:
  finite2 c ∧ (∀x. finite2 (f x)) ⇒ finite2 (bind2 c f)
Proof
  rw[finite2_def, bind2_def, bind_interest_def] >> CASE_TAC >> simp[]
QED

Theorem finite2_waiting_on[local]:
  finite2 c ⇒ FINITE (waiting_on c h)
Proof
  rw[finite2_def, waiting_on_def]
QED

Theorem finite2_both2:
  finite2 c1 ∧ finite2 c2 ⇒ finite2 (both2 c1 c2)
Proof
  rw[] >> simp[finite2_def, both2_def] >> metis_tac[finite2_waiting_on]
QED

Theorem finite2_fix2:
  contractive2 body2 ∧ (∀R. (∀p. finite2 (R p)) ⇒ ∀p. finite2 (body2 R p)) ⇒
  ∀p. finite2 (fix2 body2 p)
Proof
  rw[contractive2_lift, fix2_def]
  >> ‘∀p. (λF. finite2 (unpack F)) (fix (lift_body body2) p)’ suffices_by simp[]
  >> irule fix_preserves >> simp[]
  >> rpt conj_tac
  >> TRY (rw[closed_def, finite2_def, unpack_def] >>
          first_x_assum (qspec_then ‘LENGTH h + 1’ strip_assume_tac) >>
          gvs[agree_below_def, finite2_def, unpack_def] >> NO_TAC)
  >- (qexists_tac ‘pack never2’ >> simp[finite2_def, never2_def])
  >> simp[lift_body_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem sie_FINITE:
  FINITE E ⇒ FINITE (sie E)
Proof
  rw[sie_def] >>
  ‘{c : word64 | Readable (w2n c) ∈ E} ⊆
   IMAGE n2w {fd | Readable fd ∈ E}’
    by (rw[SUBSET_DEF] >> qexists_tac ‘w2n x’ >> simp[]) >>
  irule SUBSET_FINITE >> first_x_assum (irule_at Any) >>
  irule IMAGE_FINITE >>
  ‘{fd | Readable fd ∈ E} = IMAGE (λe. case e of Readable fd => fd) E ∩
                               {fd | Readable fd ∈ E}’
    by (rw[EXTENSION] >> eq_tac >> rw[] >> qexists_tac ‘Readable x’ >> simp[]) >>
  pop_assum SUBST1_TAC >> irule FINITE_INTER >> simp[]
QED

Theorem finite2_srelabel2:
  finite2 c ⇒ finite2 (srelabel2 c)
Proof
  rw[finite2_def, relabel2_def] >> irule sie_FINITE >> simp[]
QED

(* ------------------------------------------------------------------------
   The protocol server
   ------------------------------------------------------------------------ *)

Theorem finite2_proto_handler_v2:
  finite2 (proto_handler_v2 V P ansq fin p)
Proof
  simp[proto_handler_v2_def] >> irule finite2_fix2 >>
  simp[proto_body_v2_contractive] >> rw[] >>
  PairCases_on ‘p’ >> simp[proto_body_v2_def] >> CASE_TAC >>
  simp[finite2_return2]
  >- (CASE_TAC >> irule finite2_bind2 >> simp[finite2_emit2] >> rw[] >>
      irule finite2_bind2 >> simp[finite2_emit2])
  >> irule finite2_bind2 >> simp[finite2_wait_on] >> rw[] >>
  irule finite2_bind2 >> simp[finite2_emit2] >> rw[] >>
  rpt CASE_TAC >> simp[finite2_return2]
QED

Theorem finite2_server_v2:
  (∀fd. finite2 (h2 fd)) ⇒ finite2 (server_v2 V h2 lfd)
Proof
  strip_tac >> simp[server_v2_def] >> irule finite2_fix2 >>
  simp[server_v_body2_contractive] >> rw[server_v_body2_def] >>
  irule finite2_bind2 >> simp[finite2_wait_on] >> rw[] >>
  irule finite2_bind2 >> simp[finite2_emit2] >> rw[] >> CASE_TAC >> simp[] >>
  irule finite2_map2 >> irule finite2_both2 >> simp[]
QED

(* MAIN: the protocol server declares finitely many events, after every
   history, in the socket vocabulary too *)
Theorem finite2_sproto_server_v2:
  finite2 (srelabel2 (proto_server_v2 V P ansq fin lfd))
Proof
  irule finite2_srelabel2 >> simp[proto_server_v2_def] >>
  irule finite2_server_v2 >> simp[finite2_proto_handler_v2]
QED

(* ------------------------------------------------------------------------
   Relabelling keeps quietness (as asyncM4LiveEcho's quiet_secho)
   ------------------------------------------------------------------------ *)

(* MAIN *)
Theorem quiet_srelabel2:
  quiet c ⇒ quiet (srelabel2 c)
Proof
  rw[quiet_def] >>
  first_x_assum (qspecl_then [‘MAP sfs h’, ‘sfs s’, ‘MAP sfs h'’] mp_tac) >>
  (impl_tac
   >- (gvs[relabel2_def, relabel_def, new_actions_relabel, snap_map_def, sfe_def,
           sie_def, IN_DISJOINT] >> rw[] >> metis_tac[])) >>
  rw[] >> gvs[relabel2_def, relabel_def]
QED

Theorem wf2_srelabel2:
  wf2 c ⇒ wf2 (srelabel2 c)
Proof
  rw[wf2_def, quiet_srelabel2] >> simp[relabel2_def, wf_relabel]
QED
