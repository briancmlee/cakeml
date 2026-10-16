(*
  World facts for liveness, along the event loop's run (socket model).

   - quiet_rounds_s: while the program does not read connection c, c's
     unread data only grows (arrivals append to it), and no read of c is
     performed;
   - grounds_eof: once a read of c has returned end-of-file, c's peer has
     closed and c has nothing left to read, from then on.
*)
Theory echoLiveWorld
Ancestors
  pair list rich_list arithmetic option llist alist
  socketWorld socketFair loopPollWorld loopRounds
  loopRoundsTrans echoLiveSched
Libs
  preamble

(* Some action reads c *)
Definition reads_c_def:
  reads_c c acts ⇔ ∃k. MEM (Read c k) acts
End

(* ------------------------------------------------------------------------
   One connection, as the world changes
   ------------------------------------------------------------------------ *)

Theorem sock_do_conn:
  sock_do s a = SOME (r, s') ∧ ALOOKUP s.conns c = SOME cn ⇒
  ∃cn'. ALOOKUP s'.conns c = SOME cn' ∧ cn'.peer_closed = cn.peer_closed ∧
        ((∀k. a ≠ Read c k) ⇒ cn'.incoming = cn.incoming) ∧
        (∀k. a = Read c k ⇒ cn'.incoming = DROP k cn.incoming ∧
                            (r = Got (SOME []) ⇒ cn.incoming = [] ∧ cn.peer_closed))
Proof
  Cases_on ‘a’ >> rw[sock_do_def]
  >> gvs[sock_accept_def, sock_read_def, sock_write_def, AllCaseEqs(),
         AFUPDKEY_ALOOKUP]
  >> rpt (CASE_TAC >> gvs[]) >> rw[] >> gvs[]
  >> Cases_on ‘c = c'’ >> gvs[] >> Cases_on ‘cn.incoming’ >> gvs[]
QED

Theorem sock_acts_conn:
  ∀acts s rs evs s' cn.
    sock_acts s acts = SOME (rs, evs, s') ∧ ALOOKUP s.conns c = SOME cn ⇒
    ∃cn'. ALOOKUP s'.conns c = SOME cn' ∧ cn'.peer_closed = cn.peer_closed ∧
          (¬reads_c c acts ⇒ cn'.incoming = cn.incoming) ∧
          (cn.peer_closed ∧ cn.incoming = [] ⇒ cn'.incoming = []) ∧
          (MEM (Read c k, Got (SOME [])) (ZIP (acts, rs)) ⇒ cn.peer_closed)
Proof
  Induct >> rw[sock_acts_def] >> gvs[AllCaseEqs()]
  >> drule_all sock_do_conn >> strip_tac
  >> first_x_assum drule_all >> strip_tac >> simp[]
  >> gvs[reads_c_def] >> rw[] >> gvs[]
  >> Cases_on ‘∃k. h = Read c k’ >> gvs[] >> metis_tac[]
QED

(* A read that returned end-of-file leaves c closed and empty, for the
   rest of the round's actions *)
Theorem sock_acts_eof:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ∧
    MEM (Read c k, Got (SOME [])) (ZIP (acts, rs)) ⇒
    ∃cn'. ALOOKUP s'.conns c = SOME cn' ∧ cn'.peer_closed ∧ cn'.incoming = []
Proof
  Induct >> rw[sock_acts_def] >> gvs[AllCaseEqs()]
  >- (‘∃cn. ALOOKUP s.conns c = SOME cn’
        by gvs[sock_do_def, sock_read_def, AllCaseEqs()]
      >> drule_all sock_do_conn >> strip_tac >> gvs[]
      >> drule_all sock_acts_conn >> strip_tac >> gvs[])
  >> first_x_assum drule_all >> simp[]
QED

Theorem deliver1_conn_s:
  ALOOKUP s.conns c = SOME cn ⇒
  ∃cn'. ALOOKUP (deliver1 s a).conns c = SOME cn' ∧
        cn.incoming ≼ cn'.incoming ∧
        (cn.peer_closed ⇒ cn'.peer_closed ∧ cn'.incoming = cn.incoming)
Proof
  Cases_on ‘a’ >> rw[deliver1_def, AFUPDKEY_ALOOKUP, is_conn_def] >> rw[] >> gvs[]
QED

Theorem deliver_conn_s:
  ∀as s cn. ALOOKUP s.conns c = SOME cn ⇒
    ∃cn'. ALOOKUP (FOLDL deliver1 s as).conns c = SOME cn' ∧
          cn.incoming ≼ cn'.incoming ∧
          (cn.peer_closed ⇒ cn'.peer_closed ∧ cn'.incoming = cn.incoming)
Proof
  Induct >> simp[] >> rpt strip_tac
  >> drule deliver1_conn_s >> disch_then (qspec_then ‘h’ strip_assume_tac)
  >> first_x_assum drule >> strip_tac >> simp[]
  >> metis_tac[IS_PREFIX_TRANS]
QED

(* Time passing: c's unread data only grows; once c's peer has closed,
   nothing changes *)
Theorem tick_conn_s:
  ALOOKUP s.conns c = SOME cn ⇒
  ∃cn'. ALOOKUP (tick s).conns c = SOME cn' ∧
        cn.incoming ≼ cn'.incoming ∧
        (cn.peer_closed ⇒ cn'.peer_closed ∧ cn'.incoming = cn.incoming)
Proof
  rw[tick_def] >> CASE_TAC >> simp[deliver_def]
  >> irule deliver_conn_s >> simp[]
QED

(* ------------------------------------------------------------------------
   Along the run
   ------------------------------------------------------------------------ *)

Theorem round_conn_s:
  grun_ok ifds m s0 ∧ ALOOKUP (gstate ifds m s0 n).conns c = SOME cn ⇒
  ∃cn'. ALOOKUP (gstate ifds m s0 (SUC n)).conns c = SOME cn' ∧
        (¬reads_c c (gacts ifds m s0 n) ⇒ cn.incoming ≼ cn'.incoming) ∧
        (cn.peer_closed ∧ cn.incoming = [] ⇒ cn'.peer_closed ∧ cn'.incoming = []) ∧
        (∀k. MEM (Read c k, Got (SOME [])) (ZIP (gacts ifds m s0 n, gres ifds m s0 n)) ⇒
             cn'.peer_closed ∧ cn'.incoming = [])
Proof
  strip_tac >> drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac)
  >> drule_all sock_acts_conn >> disch_then (qspec_then ‘ARB’ strip_assume_tac)
  >> rename1 ‘ALOOKUP s'.conns c = SOME cn1’
  >> ‘gmid ifds m s0 n = s'’ by simp[gmid_def, sock_acts_tot_def]
  >> simp[gstate_SUC]
  >> qspecl_then [‘s'’, ‘cn1’] mp_tac (Q.GENL [‘s’, ‘cn’] tick_conn_s)
  >> simp[] >> strip_tac >> qexists_tac ‘cn'’ >> simp[]
  >> rw[] >> gvs[]
  >> drule_all sock_acts_eof >> strip_tac >> gvs[]
QED

(* MAIN: once a read of c has returned end-of-file, c's peer has closed and
   c has nothing left to read *)
Theorem grounds_eof:
  grun_ok ifds m s0 ⇒
  ∀n. MEM (Read c k, Got (SOME [])) (gperf ifds m s0 n) ⇒
      ∃cn. ALOOKUP (gstate ifds m s0 n).conns c = SOME cn ∧
           cn.peer_closed ∧ cn.incoming = []
Proof
  strip_tac >> Induct >- simp[gperf_def]
  >> rw[gperf_SUC]
  >- (first_x_assum drule >> strip_tac
      >> drule_all round_conn_s >> strip_tac
      >> qexists_tac ‘cn'’ >> gvs[])
  >> drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac)
  >> drule_all sock_acts_eof >> strip_tac
  >> ‘gmid ifds m s0 n = s'’ by simp[gmid_def, sock_acts_tot_def]
  >> simp[gstate_SUC] >> drule tick_conn_s >> strip_tac >> gvs[]
QED

(* MAIN: while the program does not read c, c's unread data only grows,
   and no read of c is performed *)
Theorem quiet_rounds_s:
  grun_ok ifds m s0 ⇒
  ∀d cn. ALOOKUP (gstate ifds m s0 n).conns c = SOME cn ∧
         (∀i. i < d ⇒ ¬reads_c c (gacts ifds m s0 (n + i))) ⇒
         ∃cn'. ALOOKUP (gstate ifds m s0 (n + d)).conns c = SOME cn' ∧
               cn.incoming ≼ cn'.incoming ∧
               ∀k r. MEM (Read c k, r) (gperf ifds m s0 (n + d)) ⇒
                     MEM (Read c k, r) (gperf ifds m s0 n)
Proof
  strip_tac >> Induct >- simp[]
  >> rpt strip_tac
  >> first_x_assum drule >> impl_tac >- simp[] >> strip_tac
  >> ‘¬reads_c c (gacts ifds m s0 (n + d))’ by simp[]
  >> drule_all round_conn_s >> strip_tac
  >> ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC
  >> qexists_tac ‘cn''’ >> simp[]
  >> conj_tac >- metis_tac[IS_PREFIX_TRANS]
  >> rw[gperf_SUC] >> gvs[reads_c_def]
  >> ‘LENGTH (gacts ifds m s0 (d + n)) = LENGTH (gres ifds m s0 (d + n))’
       by simp[LENGTH_gres]
  >> qspecl_then [‘(gacts ifds m s0 (d + n), gres ifds m s0 (d + n))’, ‘(Read c k, r)’]
       mp_tac (Q.GENL [‘ps’, ‘p’] MEM_ZIP_MEM_MAP)
  >> simp[] >> strip_tac
  >> qpat_x_assum ‘∀i. i < SUC d ⇒ _’ (qspec_then ‘d’ mp_tac) >> gvs[]
QED
