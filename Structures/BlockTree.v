From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From LibraChain
Require Import SeqFacts Chains HashSign Blocks.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A formalization of a block forests *)

(************************************************************)
(******************* <parameters> ***************************)
(************************************************************)
Section Forests.

Variable Hash : ordType.
Variables (PublicKey: Type) (Signature: eqType) (Address: hashType PublicKey).

Parameters (Command NodeTime: Type).

(* The Block Data (w/o signatures) *)
Notation BDataType := (BlockData Hash Signature Address Command NodeTime).

Variable hashB: BDataType -> Hash.
Hypothesis inj_hashB: injective hashB.

Variable verifB: Hash -> PublicKey -> Signature -> bool.

(* Block Type : block data with signatures *)
Notation BType := (BlockType inj_hashB verifB).
Notation QC := (QuorumCert Hash Signature (Phant Address)).

Implicit Type b: BType.

Notation "# b" := (hashB b) (at level 20).

Parameter peers : seq Address.
Parameter GenesisBlock : BType.

Definition genesis_round := (round (block_data GenesisBlock)).

(* In fact, it's a forest, as it also keeps orphan blocks *)
Definition BlockTree := union_map Hash BType.

Implicit Type bt : BlockTree.

Definition qc_of b := (proof (block_data b)).
Definition qc_hash b := (block_hash (qc_vote_data (qc_of b))).

Definition btHasBlock bt b :=
  (#b \in dom bt) && (find (#b) bt == Some b).

Notation "b ∈ bt" := (btHasBlock bt b) (at level 70).
Notation "b ∉ bt" := (~~ btHasBlock bt b) (at level 70).

Definition btExtend bt b :=
  (* We only add fresh blocks which qc is in bt *)
  if #b \in dom bt then
    if find (#b) bt == Some b then
      bt
  (* A hash collision makes the blocktree undefined *)
    else um_undef
  else
      (#b \\-> b \+ bt).

Definition Blockchain := seq BType.
Definition parent (b1 b2: BType) := #b1 == qc_hash b2.
Definition chained (bc: seq BType):= path parent GenesisBlock bc.

(************************************************************)

Definition bcLast (bc : Blockchain) := last GenesisBlock bc.

Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.

Definition has_init_block (bt : BlockTree) :=
  find (# GenesisBlock) bt = Some GenesisBlock.

Lemma has_init_block_free bt hb :
  has_init_block bt -> # GenesisBlock != hb ->
  has_init_block (free hb bt).
Proof. move=>Ib /eqP Ng; rewrite/has_init_block findF; case: ifP=>/eqP//=. Qed.

Definition validH (bt : BlockTree) :=
  forall h b, find h bt = Some b -> h = hashB b.

Lemma validH_free bt b :
  validH bt -> validH (free (# b) bt).
Proof. by move=>Vh h c; rewrite findF;case: ifP=>//_ /Vh. Qed.

Lemma validH_undef : validH um_undef.
Proof. by rewrite/validH=>h b; rewrite find_undef. Qed.

Record ConsensusState := mkConsensusState {
  last_vote_round: nat;
  preferred_block_round: nat;
}.

Definition consensusstate2nats (cs: ConsensusState) :=
  let: mkConsensusState lvr pvr := cs in (lvr, pvr).

Definition nats2consensusstate (nats: nat * nat) :=
  let: (lvr, pbr) := nats in mkConsensusState lvr pbr.

Lemma can_cs_nats: ssrfun.cancel consensusstate2nats nats2consensusstate.
Proof. by move => []. Qed.

Definition cs_eqMixin := CanEqMixin can_cs_nats.
Canonical cs_eqType := EqType _ cs_eqMixin.

Definition genesis_state := mkConsensusState genesis_round genesis_round.

Implicit Type state: ConsensusState.

Definition update state (qc: QC) :=
  let: round := (block_round (qc_vote_data qc)) in
  if (round > preferred_block_round state) then
    mkConsensusState (last_vote_round state) (round)
  else
    state.

Lemma update_eq_lvr state qc :
  last_vote_round (update state qc) = last_vote_round state.
Proof.
rewrite /update.
by case (block_round (qc_vote_data qc) > preferred_block_round state).
Qed.

Lemma update_pbr_geq state qc :
  preferred_block_round state <= preferred_block_round (update state qc).
Proof.
rewrite /update.
case H: (block_round (qc_vote_data qc) > preferred_block_round state) => //.
by move/ltnW: H => ->.
Qed.

Lemma update_qc_gt state qc :
  block_round (qc_vote_data qc) <= preferred_block_round (update state qc).
Proof.
rewrite /update; case H: (preferred_block_round state < (block_round (qc_vote_data qc))) => //.
by rewrite leqNgt H.
Qed.

Lemma update_pbr_P state qc:
  reflect (preferred_block_round (update state qc) = block_round (qc_vote_data qc))
          (preferred_block_round state <= block_round (qc_vote_data qc)).
Proof.
apply: (iffP idP); rewrite /update;
case H: (block_round (qc_vote_data qc) > preferred_block_round state);
rewrite leq_eqVlt H ?orbF ?orbT //; move/eqP=> //.
Qed.

Lemma update_maxn state qc:
  update state qc = mkConsensusState (last_vote_round state) (maxn (preferred_block_round state) (block_round (qc_vote_data qc))).
Proof.
rewrite /update /maxn; case: ((preferred_block_round state) < (block_round (qc_vote_data qc))) => //=.
by case state.
Qed.

Definition votable state b :=
  let: (rd, lvr, pbr) :=
     ((round b),
     (last_vote_round state),
     (preferred_block_round state)) in [&& rd > lvr & rd >= pbr].

Lemma votable_updateP state b:
  reflect (votable (update state (qc_of b)) b)
  (votable state b && (round b >= block_round (qc_vote_data (qc_of b)))).
Proof.
  apply: (iffP andP); rewrite /votable update_eq_lvr.
- rewrite /update; case (preferred_block_round state < block_round (qc_vote_data (qc_of b)));
  by move=> [H1 H2]; move/andP: H1=> [-> H1] //; rewrite ltnW //.
- move/andP => [->] //= H.
  apply/andP; rewrite (leq_trans (update_pbr_geq _ _) H) //=.
  by apply: (leq_trans (update_qc_gt state _)).
Qed.

Lemma votable_update_round_geq state b:
  (votable (update state (qc_of b)) b) =
  (votable state b && (round b >= block_round (qc_vote_data (qc_of b)))).
Proof.
by apply/(sameP idP); apply: votable_updateP.
Qed.

Definition voting_rule state (b: BType) :=
  let after_update := update state (qc_of b) in
  if votable (after_update) b then
    let newState :=
        mkConsensusState (round b) (preferred_block_round after_update)
    in
    (newState, true)
  else (after_update, false).

Definition voted_on state b := (voting_rule state b).2.

Lemma voted_on_votable state b:
  voted_on state b = votable (update state (qc_of b)) b.
Proof.
rewrite /voted_on /voting_rule.
by case: (votable (update state (qc_of b)) b) => //.
Qed.

Lemma voted_br_gt_qcr state b:
  voted_on state b = true ->
  round b >= block_round (qc_vote_data (qc_of b)).
Proof.
rewrite /voted_on /voting_rule.
case H: (votable (update state (qc_of b)) b).
- by move/votable_updateP: H; move/andP => [_ ->].
- by rewrite /update; case (preferred_block_round state < _).
Qed.

Lemma ineq_voted_on state b:
  (voted_on state b) = [&& (round b > last_vote_round state),
                         (round b >= preferred_block_round state) &
                         (round b >= block_round (qc_vote_data (qc_of b)))].
Proof.
by rewrite voted_on_votable votable_update_round_geq /votable -andbA.
Qed.


Lemma vote_genesis_N: voted_on genesis_state GenesisBlock = false.
Proof.
by rewrite voted_on_votable /votable update_eq_lvr /= /genesis_round ltnn.
Qed.

Definition next_state state b := (voting_rule state b).1.

Lemma next_state_pbr_update state b :
  preferred_block_round (next_state state b) = preferred_block_round (update state (qc_of b)).
Proof.
by rewrite /next_state /voting_rule; case (votable (update state (qc_of b)) b).
Qed.

Lemma next_state_pbr_geq state b:
  preferred_block_round state <= preferred_block_round (next_state state b).
Proof.
by rewrite next_state_pbr_update update_pbr_geq.
Qed.

Lemma next_state_lvr_voted state b :
  reflect (last_vote_round state < last_vote_round (next_state state b)) (voted_on state b).
Proof.
rewrite /next_state /voting_rule -voted_on_votable; apply: (iffP idP).
- move=>H; rewrite (H)=>//=; move:H; rewrite ineq_voted_on.
  by move/andP=>[-> _].
- by case: (voted_on state b); rewrite // update_eq_lvr ltnn.
Qed.

Lemma next_state_lvr_round state b:
  voted_on state b -> last_vote_round (next_state state b) = round b.
Proof.
by rewrite voted_on_votable /next_state /voting_rule=>-> /=.
Qed.

Lemma next_state_lvr_static state b:
  ~~ voted_on state b -> last_vote_round (next_state state b) = last_vote_round state.
Proof.
rewrite voted_on_votable /next_state /voting_rule.
by move/negbTE=>->; rewrite update_eq_lvr.
Qed.


Lemma next_state_lvr_if state b:
  next_state state b =
  let: pbr:= preferred_block_round (update state (qc_of b)) in
     if (voted_on state b) then
       mkConsensusState (round b) pbr
     else
       mkConsensusState (last_vote_round state) pbr.
Proof.
rewrite /next_state /voting_rule -voted_on_votable /=; case H: (voted_on state b)=> //=.
by rewrite update_maxn /=.
Qed.

Lemma next_state_lvr_leq state b:
  last_vote_round state <= last_vote_round (next_state state b).
Proof.
case H: (voted_on state b).
- by rewrite leq_eqVlt; move/next_state_lvr_voted: H=>->; rewrite orbT.
- by rewrite /next_state /voting_rule -voted_on_votable H update_eq_lvr.
Qed.

Lemma next_state_maxn state b:
  (next_state state b) =
  let: u_pbr := (maxn (preferred_block_round state) (block_round (qc_vote_data (qc_of b)))) in
  mkConsensusState (if (round b) >= maxn ((last_vote_round state).+1) u_pbr then round b else last_vote_round state) u_pbr.
Proof.
rewrite /next_state /voting_rule update_maxn.
set pbr:= (maxn (preferred_block_round state) (block_round (qc_vote_data (qc_of b)))).
rewrite /votable /= -geq_max.
by case H: (maxn (last_vote_round state).+1 pbr <= round b).
Qed.

Lemma pbr_next_stateC state b c:
  preferred_block_round (next_state (next_state state b) c) =
  preferred_block_round (next_state (next_state state c) b).
Proof.
rewrite (next_state_maxn (next_state state c) b) next_state_maxn /=.
by rewrite !next_state_maxn /= maxnAC.
Qed.

Lemma voting_next_voted state b :
  voting_rule state b = (next_state state b, voted_on state b).
Proof.
by apply surjective_pairing.
Qed.

Lemma voting_next_N state b: voted_on (next_state state b) b = false.
Proof.
rewrite voted_on_votable votable_update_round_geq /votable.
rewrite {1}/next_state /voting_rule.
case H:(votable (update state (qc_of b)) b) => /=; first by rewrite ltnn.
rewrite /votable -next_state_pbr_update in H.
by rewrite H andFb.
Qed.

Lemma voting_update_progress state qc x:
  voted_on (update state qc) x -> voted_on state x.
Proof.
rewrite 2!ineq_voted_on update_maxn /= geq_max.
by move/andP=>[->]; move/andP =>[H ->]; move/andP: H=>[-> _].
Qed.

Lemma voting_progress state b x:
  voted_on (next_state state b) x -> voted_on state x.
Proof.
rewrite 2!ineq_voted_on; move/andP=> [Hlvr]; move/andP=> [Hpbr Hbr].
rewrite (leq_ltn_trans (next_state_lvr_leq _ _) Hlvr).
by rewrite (leq_trans (next_state_pbr_geq _ _) Hpbr) /=.
Qed.

Lemma voting_gt state b x:
  voted_on (next_state state b) x ->
  ~~ voted_on state b || (round b < round x).
Proof.
move=> H; move: (H); rewrite ineq_voted_on; move/andP=> [Hlvr _].
case I: (voted_on state b)=> //.
by rewrite (next_state_lvr_round I) in Hlvr.
Qed.

Lemma voted_on_update state b x:
  ~~ voted_on state b ->
  voted_on (next_state state b) x = voted_on (update state (qc_of b)) x.
Proof.
rewrite next_state_lvr_if; move/negbTE=>->.
by rewrite update_maxn.
Qed.

Lemma pbr_update_next state b x:
  preferred_block_round (update (next_state state b) (qc_of x)) =
  preferred_block_round (update (update state (qc_of b)) (qc_of x)).
Proof.
by rewrite next_state_maxn !update_maxn /=.
Qed.

Lemma voted_next_update state b x:
  voted_on (next_state state b) x ->
  voted_on (update state (qc_of b)) x.
Proof.
move=> H; move/voting_progress: (H); rewrite ineq_voted_on; move/andP=> [Hs _].
move: H; rewrite ineq_voted_on next_state_pbr_update.
move/andP=>[Hlvr]; move/andP=> [H1 H2].
by rewrite ineq_voted_on update_eq_lvr Hs H1 H2.
Qed.

Lemma next_stateC state b c:
  next_state (next_state state b) c =
  if (~~ voted_on state b || ((round b < round c) && (block_round (qc_vote_data (qc_of c)) <= round c))) then
    next_state (update state (qc_of b)) c
  else
    (update (next_state state b) (qc_of c)).
Proof.
rewrite next_state_lvr_if [next_state (update _ _)_]next_state_lvr_if .
case H: (~~ voted_on state b).
- move/idP: (H); move/voted_on_update=> ->.
  by rewrite pbr_update_next (next_state_lvr_static H) update_eq_lvr.
move/negPn: H=> H; case I: (voted_on (next_state state b) c).
- move/idP: (I); move/voting_gt; rewrite H /= ltnNge; move/negbTE =>->.
  move/idP: (I); move/voted_next_update=>->; rewrite pbr_update_next /=.
  by move/idP: I; move/voting_progress; move/voted_br_gt_qcr=>->.
move/negbT: (I); rewrite ineq_voted_on negb_and.
rewrite (next_state_lvr_round H) next_state_pbr_update.
rewrite ineq_voted_on; move/orP=>[|].
- by move/negbTE=>->/=; rewrite update_maxn (next_state_lvr_round H) /=.
move/negbTE=>->; rewrite andbF orFb update_eq_lvr pbr_update_next.
case J: (round b < round c);
last by rewrite !update_maxn (next_state_lvr_round H) next_state_pbr_update !update_maxn /=.
move/negbT: (I); rewrite voted_on_votable /votable.
move: (H); rewrite ineq_voted_on; move/andP=> [Hlvr]; move/andP=> [Hpbr Hbr].
rewrite update_maxn (next_state_lvr_round H) J andTb; move/idP: J=> J/=.
rewrite next_state_maxn /= maxnAC geq_max.
rewrite [block_round (qc_vote_data (qc_of b)) <= _]leq_eqVlt (leq_ltn_trans Hbr J) orbT andbT.
rewrite geq_max leq_eqVlt (leq_ltn_trans Hpbr J) orbT andTb; move/negbTE=>-> /=.
by rewrite !update_maxn /= maxnAC.
Qed.

Lemma next_state_updateC state qc x:
  voted_on (update state qc) x ->
  next_state (update state (qc)) x =
  update (next_state state x) qc.
Proof.
move => H; rewrite /next_state /voting_rule -2!voted_on_votable H.
by move/voting_update_progress: H=> -> /=; rewrite !update_maxn /= maxnAC.
Qed.

Lemma voted_on_maxn state b:
  (voted_on state b) =
  (round b >= maxn
               (maxn ((last_vote_round state).+1) (preferred_block_round state))
               (block_round (qc_vote_data (qc_of b)))).
Proof.
by rewrite !geq_max -andbA ineq_voted_on.
Qed.

Lemma voting_push_right state b c x:
  voted_on (next_state (next_state state b) c) x ->
  voted_on (next_state (next_state state c) b) x.
Proof.
rewrite 2!ineq_voted_on.
move/andP=> [Hlvr]; move/andP => [Hpbr]; move: (Hpbr).
rewrite pbr_next_stateC =>[-> ->]/=.
move: Hlvr; rewrite andbT.
repeat rewrite [next_state (next_state _ _) _]next_state_lvr_if [last_vote_round (if _ then _ else _)]fun_if /=.
case Hc: (voted_on (next_state state b) c).
- move/idP: (Hc); move/voting_progress;
  rewrite {2}[next_state state c]next_state_lvr_if=>-> /= Hcx.
  case Hb: (voted_on (next_state state c) b); last by [].
  move/voting_gt: (Hc); move/voting_progress: Hb=>->/= H.
  apply: (ltn_trans H Hcx).
rewrite next_state_lvr_if fun_if /=.
case Hb: (voted_on (next_state state c) b); first by move/voting_progress: (Hb)=>->.
rewrite /= next_state_lvr_if [last_vote_round (if _ then _ else _)]fun_if /=.
case Hbb: (voted_on state b); case Hcc: (voted_on state c) => //.
- move/negbT: Hc; rewrite ineq_voted_on.
  rewrite negb_and (next_state_lvr_round Hbb) (voted_br_gt_qcr Hcc).
  rewrite andbT next_state_pbr_update -leqNgt -ltnNge.
  move/idP: (Hbb); rewrite voted_on_votable /votable; move/andP=>[_ Hpbr2].
  move/orP=>[|]; first by apply leq_ltn_trans.
  by move=> Hpb Hbx; apply/(leq_trans Hpb)/(leq_trans Hpbr2)/ltnW.
- move/idP: Hbb; rewrite ineq_voted_on; move/andP=>[H _].
  by apply ltn_trans.
move => _; move/negbT: (Hc); rewrite ineq_voted_on.
move/negbT: (Hbb); move/next_state_lvr_static=>->.
rewrite negb_and (voted_br_gt_qcr Hcc) andbT.
move: (Hcc); rewrite ineq_voted_on; move/andP=> [-> _] /=.
rewrite -ltnNge=> Hpbr2; move: Hpbr.
rewrite next_state_pbr_update update_maxn /=.
move/(leq_trans (leq_maxl (preferred_block_round (next_state state b)) (block_round (qc_vote_data (qc_of c))))).
by move/(leq_trans Hpbr2).
Qed.

Implicit Type bseq: seq BType.

(* node_processing is a slight modification on a scanleft of the voting rules
over a seq of block *)
Fixpoint process_aux state bseq res :=
  if bseq is x::s then
    let: (new_state, vote) := (voting_rule state x) in
    process_aux new_state s ((state, vote) :: res)
  else
    (state, rev res).

Definition node_processing state bseq := process_aux state bseq [::].

Lemma size_process_aux state bseq res: size (process_aux state bseq res).2 = size bseq + size res.
Proof.
elim:bseq res state => [|x xs IHs] res state.
- by rewrite size_rev add0n.
- by rewrite /= voting_next_voted IHs /= addSnnS.
Qed.

Lemma size_processing state bseq : size (node_processing state bseq).2 = size bseq.
Proof.
by rewrite /node_processing size_process_aux addn0.
Qed.

Lemma processing_aux_state_res_irrel state bseq rs1 rs2:
  (process_aux state bseq rs1).1 = (process_aux state bseq rs2).1.
Proof.
elim: bseq state rs1 rs2 => [|b bs IHb] state rs1 rs2 //=; rewrite voting_next_voted.
by apply:IHb.
Qed.

Lemma processing_aux_rcons state bseq r rs:
  (process_aux state bseq (rcons rs r)).2 =
  r :: (process_aux state bseq rs).2.
Proof.
elim: bseq r rs state =>[| b bs IHb] r rs state => /=.
- by rewrite rev_rcons.
- by rewrite voting_next_voted -IHb -rcons_cons.
Qed.

Lemma processing_aux_rev state bseq res:
  (process_aux state bseq res).2 =
  rev res ++ (process_aux state bseq [::]).2.
Proof.
move: res bseq state; apply: last_ind=> [|rs r IHr] bseq state.
- by [].
- by rewrite processing_aux_rcons IHr rev_rcons.
Qed.

Lemma processing_aux_cons state b bs:
  (process_aux state (b::bs) [::]).2 =
  (state, voted_on state b) :: (process_aux (next_state state b) bs [::]).2.
Proof.
rewrite /= voting_next_voted -[[:: (state, voted_on _ _)]]cat0s cats1.
by rewrite processing_aux_rcons.
Qed.

Lemma processing_aux_cons2 state b bs:
  (process_aux state (b::bs) [::]) =
  let: (f_state, vbs) := (process_aux (next_state state b) bs [::]) in
  (f_state, (state, voted_on state b) ::vbs).
Proof.
rewrite /= voting_next_voted -[[:: (state, voted_on _ _)]]cat0s cats1.
rewrite [process_aux _ bs [::]]surjective_pairing -processing_aux_cons /=.
rewrite (processing_aux_state_res_irrel _ _ [::] [:: (state, voted_on state b)]).
by rewrite voting_next_voted -surjective_pairing.
Qed.

Lemma node_processing_cons state b bs:
  (node_processing state (b::bs)).2 =
  (state, voted_on state b) :: (node_processing (next_state state b) bs).2.
Proof.
by rewrite processing_aux_cons.
Qed.

Lemma node_processing_cons2 state b bs:
  (node_processing state (b::bs)) =
  let: (final_state, bsvotes) := node_processing (next_state state b) bs in
  (final_state, (state, voted_on state b)::bsvotes).
Proof.
by  rewrite /node_processing processing_aux_cons2.
Qed.

Lemma node_processing_cons1 state b bs:
  (node_processing state (b::bs)).1 =
  (node_processing (next_state state b) bs).1.
Proof.
case: bs state b=>[|x s ]=>state b; rewrite node_processing_cons2 //=.
by rewrite [node_processing _ _]surjective_pairing /=.
Qed.

Lemma node_processing_cat_cps state bs1 bs2 :
  (node_processing state (bs1 ++ bs2)) =
  let: (state1, seq1) := (node_processing state bs1) in
  let: (state2, seq2) := (node_processing state1 bs2) in
  (state2, seq1 ++ seq2).
Proof.
elim: bs1 state =>[| b bs IHb] state /=.
- by rewrite {2}[node_processing _ _]surjective_pairing -surjective_pairing.
rewrite 2!node_processing_cons2 IHb [node_processing (next_state _ _) _]surjective_pairing /=.
by rewrite [node_processing _  _]surjective_pairing.
Qed.

Lemma node_processing_rcons state bs b:
  (next_state (node_processing state bs).1 b) =
  (node_processing state (rcons bs b)).1.
Proof.
rewrite -cats1 node_processing_cat_cps /=.
rewrite {2}[node_processing _ _]surjective_pairing /=.
rewrite [node_processing _ [::b]]surjective_pairing /=.
by rewrite node_processing_cons1 /=.
Qed.

Lemma voting_progress_seq state bs b:
  voted_on (node_processing state bs).1 b -> voted_on state b.
Proof.
elim: bs state b => [|x s IHs] state b //=.
rewrite node_processing_cons1.
move/IHs; apply voting_progress.
Qed.

Definition comparator state1 :=
  maxn (last_vote_round state1).+1 (preferred_block_round state1).

Definition state_compare state1 state2 :=
  comparator state1 <= comparator state2.

Delimit Scope state_scope with STATE.
Open Scope state_scope.

Notation "state1 <% state2" := (state_compare state1 state2) (at level 40) :state_scope.

Lemma voting_comparator state x:
  (voted_on state x) ->
  (comparator (next_state state x) = (round x).+1).
Proof.
rewrite next_state_lvr_if fun_if /comparator /= =>H.
rewrite H; apply/maxn_idPl; move/idP:H; rewrite voted_on_votable.
by move/andP=>[_ H]; apply ltnW; rewrite ltnS.
Qed.

Lemma voting_gt_compare state1 state2 x:
  state1 <% state2 -> voted_on state2 x -> voted_on state1 x.
Proof.
move=> H; rewrite 2!voted_on_maxn; apply leq_trans.
rewrite geq_max leq_maxr leq_max andbT.
by apply/orP; left.
Qed.

Lemma voting_next_gt state x:
  state <% (next_state state x).
Proof.
rewrite next_state_lvr_if.
case Hx:(voted_on state x); rewrite /state_compare /=.
- move/idP: Hx; rewrite voted_on_maxn.
  rewrite leq_max geq_max; move/andP=> [H _].
  by apply/orP; left; apply ltnW.
rewrite update_maxn /= leq_max 2!geq_max ltnS leqnn andTb.
rewrite leq_maxl andbT leq_max.
case I: (last_vote_round state < preferred_block_round state);
first by rewrite orTb orbT.
move/negbT: I; rewrite ltnNge; move/negPn=> H.
by rewrite orFb; apply/orP; left; apply ltnW.
Qed.

Lemma voting_next_inner state1 state2 x:
  state1 <% state2 ->
  (next_state state1 x) <% (next_state state2 x).
Proof.
move => H12.
case H2: (voted_on state2 x).
- rewrite /state_compare (voting_comparator H2).
  move/(voting_gt_compare H12): H2; move/voting_comparator=>->.
  by apply: ltnSn.
case H1: (voted_on state1 x).
- rewrite /state_compare (voting_comparator H1).
  rewrite /comparator; move/negbT: (H2); rewrite voted_on_votable.
  rewrite /votable /= next_state_pbr_update next_state_lvr_if H2 /=.
  rewrite negb_and -leqNgt -ltnNge leq_max.
  move/orP=>[|->]; last by rewrite orbT.
  by rewrite update_maxn /= ltnS =>->.
rewrite 2!next_state_lvr_if H1 H2.
move: H12; rewrite /state_compare /comparator 2!update_maxn /=.
rewrite !maxnA=>H12; rewrite geq_max leq_max H12 orTb andTb.
by rewrite leq_max leqnn orbT.
Qed.

Definition voted_in_processing state bseq :=
  mask (unzip2 (node_processing state bseq).2) bseq.

Lemma voted_in_processing_cat_cps state bs1 bs2:
  (voted_in_processing state (bs1 ++ bs2)) =
  let: b1 := (voted_in_processing state bs1) in
  let: b2 := (voted_in_processing (node_processing state bs1).1 bs2) in
  b1 ++ b2.
Proof.
rewrite /voted_in_processing node_processing_cat_cps /=.
rewrite 2![node_processing _ _]surjective_pairing /=.
rewrite -mask_cat; last by rewrite size_map size_processing.
by rewrite -map_cat /unzip2.
Qed.

Lemma voted_in_processing_cons state b bs:
  (voted_in_processing state (b::bs)) =
  (nseq (voted_on state b) b ++ (voted_in_processing (next_state state b) bs)).
Proof.
by rewrite /voted_in_processing node_processing_cons mask_cons.
Qed.

(* THis should be strenghtened to take the above into account *)
Lemma voted_in_processing_idx state bseq b:
  uniq bseq ->
  (b \in (voted_in_processing state bseq)) =
  (voted_on (nth state (unzip1 (node_processing state bseq).2) (index b bseq) ) b && (b \in bseq)).
Proof.
elim: bseq b state =>[| bb bbs IHbb] b state Huniq /=.
- by rewrite in_nil andbF.
rewrite /voted_in_processing node_processing_cons /unzip2 /unzip1 map_cons.
case H: (bb == b).
- move: Huniq; move/eqP: H=> ->/=; rewrite in_cons eqxx orTb andbT.
  case H2: (voted_on state b); first by rewrite in_cons eqxx orTb.
  move/andP=>[H _]; move: H; apply: contraNF; exact: mem_mask.
rewrite mask_cons mem_cat mem_nseq in_cons eq_sym H andbF 2!orFb.
move: Huniq; rewrite cons_uniq; move/andP => [_ Huniq].
rewrite map_cons -/unzip1 (IHbb _ _ Huniq) /=.
case Hbbs: (b \in bbs); first rewrite 2!andbT; last by rewrite 2!andbF.
move/idP: Hbbs; rewrite -index_mem.
move: (size_processing (next_state state bb) bbs)=><-.
rewrite -(size_map fst) -/unzip1=> Hsize; apply/eqP.
by rewrite (nth_in_default_irrel (next_state state bb) state Hsize).
Qed.


Definition node_aggregator bseq :=
  (foldl (fun stateNvote => voting_rule stateNvote.1) (genesis_state,false) bseq).1.


Definition commit_rule state (qc: QC)(bround: nat) :=
  let: potential_commit_round := (parent_block_round (qc_vote_data qc)) in
  if (potential_commit_round.+1 == (block_round (qc_vote_data qc))) &&
        ((block_round (qc_vote_data qc)).+1 == bround) then
    Some(potential_commit_round)
  else None.

End Forests.
