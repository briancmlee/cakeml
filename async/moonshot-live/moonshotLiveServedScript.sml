(*
  Moonshot liveness, N8 part 2: chain_served_claim PROVED, the data chain of
  one logical connection as pure glue.  The client's requests flow client →
  kernel → proxy → kernel → KV, the replies flow back, each hop either
  progressing or (for a kernel hop) its receiving end lost; a loss before
  the client is served is the excuse X.
*)
Theory moonshotLiveServed
Ancestors
  moonshotLiveDeliver moonshotLiveChain moonshotLiveDrains moonshotLiveStmts l0sysFair l0sys
  l0sysCausal
Libs
  preamble

Theorem ev_ext_step:
  ev_ext m f g ∧ m ≤ n ∧ p ≼ f n ⇒ ∃n'. n ≤ n' ∧ p ≼ g n'
Proof
  rw[ev_ext_def] >> first_x_assum drule >> strip_tac >>
  qexists_tac ‘n'’ >> metis_tac[IS_PREFIX_TRANS]
QED

Theorem ev_ext_unless_step:
  ev_ext_unless m B f g ∧ m ≤ n ∧ p ≼ f n ⇒ ∃n'. n ≤ n' ∧ (p ≼ g n' ∨ B n')
Proof
  rw[ev_ext_unless_def] >> first_x_assum drule >> strip_tac >>
  qexists_tac ‘n'’ >> metis_tac[IS_PREFIX_TRANS]
QED

Theorem chain_served:
  chain_served_claim
Proof
  simp[chain_served_claim_def] >> rpt gen_tac >> Cases_on ‘X’ >> simp[] >> strip_tac >>
  (* all four directions drain (N8 part 1) *)
  ‘sys_drains ss (px, ja) ∧ sys_drains ss (kv, jk) ∧ sys_drains ss (px, jb) ∧
   sys_drains ss (cl, jc)’ by
    (qspecl_then [‘ps’, ‘ss’, ‘rs’, ‘m’, ‘cl’, ‘jc’, ‘px’, ‘ja’, ‘jb’, ‘kv’, ‘jk’, ‘F’]
       mp_tac (Q.GENL [‘ps’, ‘ss’, ‘rs’, ‘m’, ‘cl’, ‘jc’, ‘px’, ‘ja’, ‘jb’, ‘kv’, ‘jk’, ‘X’]
                 moonshot_chain_drains) >> simp[]) >>
  fs[] >>
  ‘kinv (ss m)’ by metis_tac[irun_kinv] >>
  ‘(ss m).peer (px, ja) = SOME (cl, jc) ∧ (ss m).peer (kv, jk) = SOME (px, jb)’ by
    metis_tac[kinv_peer_end] >>
  (* the four kernel hops *)
  ‘ev_ext_unless m (lost ss (px, ja)) (sent_at ss (cl, jc)) (dlv_at ss (px, ja)) ∧
   ev_ext_unless m (lost ss (kv, jk)) (sent_at ss (px, jb)) (dlv_at ss (kv, jk)) ∧
   ev_ext_unless m (lost ss (px, jb)) (sent_at ss (kv, jk)) (dlv_at ss (px, jb)) ∧
   ev_ext_unless m (lost ss (cl, jc)) (sent_at ss (px, ja)) (dlv_at ss (cl, jc))’ by
    metis_tac[sys_delivers] >>
  (* a lost chain end before the client is served is excluded *)
  ‘∀n e. MEM e [(cl, jc); (px, ja); (px, jb); (kv, jk)] ∧ lost ss e n ⇒
         served_by rs cl jep rq n’ by
    (qx_genl_tac [‘t’, ‘e’] >> strip_tac >>
     qpat_x_assum ‘∀n e. _ ∨ _ ∨ _’ (qspecl_then [‘t’, ‘e’] mp_tac) >> fs[]) >>
  (* requests *)
  rename1 ‘brequests rq ≼ sent_at ss (cl, jc) n1’ >>
  ‘∃n2. n1 ≤ n2 ∧ (brequests rq ≼ dlv_at ss (px, ja) n2 ∨ lost ss (px, ja) n2)’ by
    (qspecl_then [‘m’, ‘lost ss (px, ja)’, ‘sent_at ss (cl, jc)’, ‘dlv_at ss (px, ja)’, ‘n1’,
                  ‘brequests rq’] mp_tac (Q.GENL [‘m’, ‘B’, ‘f’, ‘g’, ‘n’, ‘p’] ev_ext_unless_step) >>
     fs[]) >>
  TRY (qexists_tac ‘n2’ >> first_x_assum irule >> simp[] >> qexists_tac ‘(px, ja)’ >> simp[] >>
       NO_TAC) >>
  ‘∃n3. n2 ≤ n3 ∧ brequests rq ≼ sent_at ss (px, jb) n3’ by
    (irule ev_ext_step >> qexistsl_tac [‘dlv_at ss (px, ja)’, ‘m’] >> simp[]) >>
  ‘∃n4. n3 ≤ n4 ∧ (brequests rq ≼ dlv_at ss (kv, jk) n4 ∨ lost ss (kv, jk) n4)’ by
    (qspecl_then [‘m’, ‘lost ss (kv, jk)’, ‘sent_at ss (px, jb)’, ‘dlv_at ss (kv, jk)’, ‘n3’,
                  ‘brequests rq’] mp_tac (Q.GENL [‘m’, ‘B’, ‘f’, ‘g’, ‘n’, ‘p’] ev_ext_unless_step) >>
     fs[]) >>
  TRY (qexists_tac ‘n4’ >> first_x_assum irule >> simp[] >> qexists_tac ‘(kv, jk)’ >> simp[] >>
       NO_TAC) >>
  (* KV answers *)
  ‘∃n5 ans. n4 ≤ n5 ∧ LENGTH ans = LENGTH rq ∧ reply_bytes ans ≼ sent_at ss (kv, jk) n5’ by
    (qpat_x_assum ‘kv_answers _ _ _ _’ mp_tac >> rw[kv_answers_def] >>
     first_x_assum irule >> simp[]) >>
  (* replies *)
  ‘∃n6. n5 ≤ n6 ∧ (reply_bytes ans ≼ dlv_at ss (px, jb) n6 ∨ lost ss (px, jb) n6)’ by
    (qspecl_then [‘m’, ‘lost ss (px, jb)’, ‘sent_at ss (kv, jk)’, ‘dlv_at ss (px, jb)’, ‘n5’,
                  ‘reply_bytes ans’] mp_tac (Q.GENL [‘m’, ‘B’, ‘f’, ‘g’, ‘n’, ‘p’] ev_ext_unless_step) >>
     fs[]) >>
  TRY (qexists_tac ‘n6’ >> first_x_assum irule >> simp[] >> qexists_tac ‘(px, jb)’ >> simp[] >>
       NO_TAC) >>
  ‘∃n7. n6 ≤ n7 ∧ reply_bytes ans ≼ sent_at ss (px, ja) n7’ by
    (irule ev_ext_step >> qexistsl_tac [‘dlv_at ss (px, jb)’, ‘m’] >> simp[]) >>
  ‘∃n8. n7 ≤ n8 ∧ (reply_bytes ans ≼ dlv_at ss (cl, jc) n8 ∨ lost ss (cl, jc) n8)’ by
    (qspecl_then [‘m’, ‘lost ss (cl, jc)’, ‘sent_at ss (px, ja)’, ‘dlv_at ss (cl, jc)’, ‘n7’,
                  ‘reply_bytes ans’] mp_tac (Q.GENL [‘m’, ‘B’, ‘f’, ‘g’, ‘n’, ‘p’] ev_ext_unless_step) >>
     fs[]) >>
  TRY (qexists_tac ‘n8’ >> first_x_assum irule >> simp[] >> qexists_tac ‘(cl, jc)’ >> simp[] >>
       NO_TAC) >>
  ‘∃n9. n8 ≤ n9 ∧ reply_bytes ans ≼ l0_ep_recvd jep (ptr rs cl n9)’ by
    (qspecl_then [‘m’, ‘dlv_at ss (cl, jc)’, ‘λn. l0_ep_recvd jep (ptr rs cl n)’, ‘n8’,
                  ‘reply_bytes ans’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘g’, ‘n’, ‘p’] ev_ext_step) >> simp[]) >>
  qexists_tac ‘n9’ >> simp[served_by_def] >> metis_tac[]
QED
