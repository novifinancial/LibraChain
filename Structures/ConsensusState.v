From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path choice.
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
Section State.

Variable Hash : countType.
Variables (PublicKey: countType) (Signature: countType) (Address: hashType PublicKey).

Variables (Command NodeTime: countType).

(* The Block Data (w/o signatures) *)
Notation BDataType := (BlockData Hash Signature Address Command NodeTime).

Variable hashB: BDataType -> Hash.
Hypothesis inj_hashB: injective hashB.

Variable verifB: Hash -> PublicKey -> Signature -> bool.

(* Block Type : block data with signatures *)
Notation BType := (BlockType inj_hashB verifB).
Notation QC := (QuorumCert Hash Signature (Phant Address)).

Implicit Type b: BDataType.

Parameter GenesisBlock : BDataType.

Definition genesis_round := (round GenesisBlock).

Definition qc_of b := (proof b).

Definition qc_hash b := (block_hash (qc_vote_data (qc_of b))).
Definition qc_round b := (block_round (qc_vote_data (qc_of b))).
Definition qc_parent_round b := (parent_block_round (qc_vote_data (qc_of b))).

Definition parent b1 b2 := (hashB b1 == qc_hash b2) && (round b1 == qc_round b2).

Lemma rounds_transitive:
  transitive (fun b1 b2 => (round b1) < (round b2)).
Proof.
by move=> b1 b2 b3; apply ltn_trans.
Qed.

Lemma rounds_irreflexive:
  irreflexive (fun b1 b2 => (round b1) < (round b2)).
Proof. by move=> b; rewrite ltnn. Qed.

(************************************************************)
(** Consensus State                                        **)
(************************************************************)

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
Definition cs_choiceMixin := CanChoiceMixin can_cs_nats.
Canonical cs_choiceType := ChoiceType _ cs_choiceMixin.
Definition cs_countMixin := CanCountMixin can_cs_nats.
Canonical cs_countType := CountType _ cs_countMixin.

Definition genesis_state := mkConsensusState genesis_round genesis_round.

Implicit Type state: ConsensusState.

Definition update state (qc: QC) :=
  let: round := (parent_block_round (qc_vote_data qc)) in
  if (round > preferred_block_round state) then
    mkConsensusState (last_vote_round state) (round)
  else
    state.

Lemma update_eq_lvr state qc :
  last_vote_round (update state qc) = last_vote_round state.
Proof.
rewrite /update.
by case (parent_block_round (qc_vote_data qc) > preferred_block_round state).
Qed.

Lemma update_pbr_geq state qc :
  preferred_block_round state <= preferred_block_round (update state qc).
Proof.
rewrite /update.
case H: (parent_block_round (qc_vote_data qc) > preferred_block_round state) => //.
by move/ltnW: H => ->.
Qed.

Lemma update_qc_gt state qc :
  parent_block_round (qc_vote_data qc) <= preferred_block_round (update state qc).
Proof.
rewrite /update; case H: (preferred_block_round state < (parent_block_round (qc_vote_data qc))) => //.
by rewrite leqNgt H.
Qed.

Lemma update_pbr_P state qc:
  reflect (preferred_block_round (update state qc) = parent_block_round (qc_vote_data qc))
          (preferred_block_round state <= parent_block_round (qc_vote_data qc)).
Proof.
apply: (iffP idP); rewrite /update;
case H: (parent_block_round (qc_vote_data qc) > preferred_block_round state);
rewrite leq_eqVlt H ?orbF ?orbT //; move/eqP=> //.
Qed.

Lemma update_maxn state qc:
  update state qc =
  mkConsensusState (last_vote_round state)
                   (maxn (preferred_block_round state) (parent_block_round (qc_vote_data qc))).
Proof.
rewrite /update /maxn; case: ((preferred_block_round state) < (parent_block_round (qc_vote_data qc))) => //=.
by case state.
Qed.

(************************************************************)
(** Voting after update with the QC                        **)
(************************************************************)

Definition votable state b :=
  let: (rd, qcr, lvr, pbr) :=
     ((round b), (qc_round b),
     (last_vote_round state),
     (preferred_block_round state)) in [&& rd > lvr & qcr >= pbr].

Lemma votable_updateP state b:
  reflect (votable (update state (qc_of b)) b)
  (votable state b && (qc_round b >= qc_parent_round b)).
Proof.
  apply: (iffP andP); rewrite /votable update_eq_lvr.
- rewrite /update; case (preferred_block_round state < parent_block_round (qc_vote_data (qc_of b)));
  move=> [H1 H2]; move/andP: H1=> [-> H1] //; rewrite ltnW //.
- move/andP => [->] //= H.
  apply/andP; rewrite (leq_trans (update_pbr_geq _ _) H) //=.
  by apply: (leq_trans (update_qc_gt state _)).
Qed.

Lemma votable_update_round_geq state b:
  (votable (update state (qc_of b)) b) =
  (votable state b && (qc_round b >= qc_parent_round b)).
Proof.
by apply/(sameP idP); apply: votable_updateP.
Qed.

Definition voting_rule state (b: BDataType) :=
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
  qc_round b >= qc_parent_round b.
Proof.
rewrite /voted_on /voting_rule.
case H: (votable (update state (qc_of b)) b).
- by move/votable_updateP: H; move/andP => [_ ->].
- by rewrite /update; case (preferred_block_round state < _).
Qed.

Lemma ineq_voted_on state b:
  (voted_on state b) = [&& (round b > last_vote_round state),
                         (qc_round b >= preferred_block_round state) &
                         (qc_round b >= qc_parent_round b)].
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
  let: u_pbr := (maxn (preferred_block_round state) (qc_parent_round b)) in
  mkConsensusState
    (if (round b >= (last_vote_round state).+1) && (qc_round b >= u_pbr) then round b else last_vote_round state)
    u_pbr.
Proof.
rewrite /next_state /voting_rule update_maxn.
set pbr:= (maxn (preferred_block_round state) (qc_parent_round b)).
rewrite /votable /=.
by case H: ((last_vote_round state < round b) && (pbr <= qc_round b)).
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

Lemma non_voted_on_update state b x:
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
  (round b >=  (last_vote_round state).+1) && (qc_round b >= maxn (preferred_block_round state)
               (qc_parent_round b)).
Proof.
by rewrite !geq_max  ineq_voted_on.
Qed.

(************************************************************)
(** Voting in Sequence                                     **)
(************************************************************)

Implicit Type bseq: seq BDataType.

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

(************************************************************)
(** Consensus State Comparators                            **)
(************************************************************)

Definition comparator state1 :=
  ((last_vote_round state1).+1, (preferred_block_round state1)).

Definition state_compare state1 state2 :=
  ((comparator state1).1 <= (comparator state2).1) && ((comparator state1).2 <= (comparator state2).2).

Delimit Scope state_scope with STATE.
Open Scope state_scope.

Notation "state1 <% state2" := (state_compare state1 state2) (at level 40) :state_scope.

Lemma comparators_transitive:
  transitive state_compare.
Proof.
move => s2 s1 s3 H12 H23; move/andP: H12=> [H12fst H12snd].
move/andP: H23=> [H23fst H23snd]; rewrite /state_compare (leq_trans H12fst H23fst).
by rewrite (leq_trans H12snd).
Qed.

Lemma voting_comparator state x:
  (voted_on state x) ->
  (comparator (next_state state x) = ((round x).+1, (maxn (comparator state).2 (qc_parent_round x)))).
Proof.
rewrite next_state_lvr_if fun_if /comparator /= =>H.
by rewrite H update_maxn /= maxnC.
Qed.

Lemma non_voting_comparator state x:
  ~~ voted_on state x ->
  comparator (next_state state x) = ((comparator state).1, (maxn (comparator state).2 (qc_parent_round x))).
Proof.
move=>Hnv; rewrite next_state_lvr_if; move/negbTE: (Hnv)=>->.
by rewrite /comparator update_maxn /=.
Qed.

Lemma voting_comparator_eq state b:
    (voted_on state b) =
    ((comparator state).1 <= round b) && ((comparator state).2 <= (qc_round b)) && ((qc_parent_round b) <= qc_round b).
Proof.
by  rewrite /comparator ineq_voted_on /= andbA.
Qed.

Lemma voting_gt_compare state1 state2 x:
  state1 <% state2 -> voted_on state2 x -> voted_on state1 x.
Proof.
move=> H; rewrite 2!voted_on_maxn.
move/andP=> [Hlv2 Hpr2]; move/andP: H=> [Hlv12 Hpr12].
rewrite (leq_trans Hlv12 Hlv2) /=; move:Hpr2; rewrite 2!geq_max.
by move/andP=> [Hpr2 ->]; rewrite (leq_trans Hpr12 Hpr2).
Qed.

Lemma voting_next_gt state x:
  state <% (next_state state x).
Proof.
rewrite next_state_lvr_if.
case Hx:(voted_on state x); rewrite /state_compare /=.
- move/idP: Hx; rewrite voted_on_maxn.
  rewrite geq_max; move/andP=> [Hlv Hpr].
  by rewrite update_maxn /= leq_max leqnn orTb andbT ltnW.
rewrite update_maxn /=. ltnS leqnn andTb.
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

Lemma node_processing_sorted state bs:
  sorted (fun s1 s2 => (comparator s1) <= (comparator s2)) (unzip1 (node_processing state bs).2).
Proof.
move: state; elim: bs=>[| b bs IHb] state //.
rewrite node_processing_cons; move:(IHb (next_state state b)); rewrite /path /sorted /=.
case H: (unzip1 (node_processing (next_state state b) bs).2) =>// [x xs].
rewrite /path -/(path _ _ _)=>-> /=; move:H; case bs=> [|y ys]//=.
rewrite andbT node_processing_cons /=; move/eqP; rewrite eqseq_cons.
by move/andP=>[/eqP<- _]; apply: voting_next_gt.
Qed.

Lemma node_processing_head state bs:
  unzip1 (node_processing state bs).2 = (if bs is x::xs then state :: unzip1 (node_processing (next_state state x) xs).2 else [::]).
Proof.
by case: bs=> [|x xs]//=; rewrite node_processing_cons /=.
Qed.

Lemma node_processing_last s0 state bs b:
  last s0 (unzip1 (node_processing state (rcons bs b)).2) = (node_processing state bs).1.
Proof.
elim: bs state s0 =>[| x s IHs] state s0 //=; first by rewrite node_processing_cons.
rewrite node_processing_cons node_processing_cons1 /unzip1 map_cons /= -/unzip1.
by rewrite (IHs (next_state state x)).
Qed.

(************************************************************)
(** Sequence of elements which a node voted on             **)
(************************************************************)

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

Lemma comparatorC state b c:
  comparator (next_state (next_state state b) c) =
  comparator (next_state (next_state state c) b).
Proof.
rewrite next_state_maxn maxnA -/(comparator (next_state _ _)).
rewrite [next_state (next_state _ _) _]next_state_maxn maxnA.
rewrite -/(comparator (next_state _ _)) 2!geq_max 2!next_state_pbr_update 2!update_maxn /=.
rewrite 2![comparator {|last_vote_round := _; preferred_block_round:= _|}]/comparator /= maxnAC.
case Hc: (voted_on state c); [rewrite (next_state_lvr_round Hc) (voting_comparator Hc) (voted_br_gt_qcr Hc) andbT
  | move/negbT/next_state_lvr_static: (Hc)=>->; rewrite (non_voting_comparator (negbT Hc)) geq_max];
case Hb: (voted_on state b); [ rewrite (next_state_lvr_round Hb) (voting_comparator Hb) (voted_br_gt_qcr Hb) andbT
  | move/negbT/next_state_lvr_static: (Hb)=>->; rewrite (non_voting_comparator (negbT Hb)) geq_max
  | rewrite (next_state_lvr_round Hb) (voting_comparator Hb) (voted_br_gt_qcr Hb) andbT
  | move/negbT/next_state_lvr_static: (Hb)=>->; rewrite (non_voting_comparator (negbT Hb)) geq_max].
- case Hbc: (round b == round c); first by move/eqP: Hbc; move=><-; rewrite ltnn.
  by move/negbT: (Hbc); rewrite neq_ltn; move/orP=>[Hltn|Hltn]; rewrite Hltn /=; move: Hltn; rewrite ltnNge leq_eqVlt;
  [rewrite eq_sym|]; rewrite Hbc orFb; move/negbTE=>->/=.
- move: (Hc); rewrite voting_comparator_eq; move/andP=>[Hcpc Hbrc] /=.
  rewrite Hcpc; move/negbT: (Hb); rewrite voting_comparator_eq negb_and.
  case Hbrb: ((qc_round b) <= round b); [rewrite orbF andbT andTb -ltnNge => Hcpb | rewrite andbF andTb => _ ].
  - by rewrite ltnNge; move/ltnW: (leq_trans Hcpb Hcpc)=> Hbc; rewrite Hbc (leq_trans Hbrb Hbc) /=.
  move/negbT: Hbrb; rewrite -ltnNge=> Hbrb; case Hqbc: (block_round (qc_vote_data (qc_of b)) <= round c); first by [].
  move/negbT: Hqbc; rewrite -ltnNge=> Hqbc; rewrite [maxn (round c).+1 _]maxnCA; move/maxn_idPr: (Hqbc)=>->.
  rewrite 2!maxnA -/(comparator state) maxnAC; move/ltnW: (leq_ltn_trans Hcpc Hqbc); move/maxn_idPr=>->.
  move: (leq_maxr (last_vote_round state).+1 (preferred_block_round state)); rewrite -/(comparator state)=> Hprcsc.
  by rewrite maxnAC; move: (leq_ltn_trans (leq_trans Hprcsc Hcpc) Hqbc); move/ltnW/maxn_idPr=>->.
- move: (Hb); rewrite voting_comparator_eq; move/andP=>[Hcpb Hbrb] /=.
  rewrite Hcpb; move/negbT: (Hc); rewrite voting_comparator_eq negb_and.
  case Hbrc: ((block_round (qc_vote_data (qc_of c))) <= round c);
    [rewrite orbF andbT andTb -ltnNge => Hcpc | rewrite andbF andTb => _ ].
  - by rewrite ltnNge; move/ltnW: (leq_trans Hcpc Hcpb)=> Hbb; rewrite Hbb (leq_trans Hbrc Hbb) /=.
  move/negbT: Hbrc; rewrite -ltnNge=> Hbrc; case Hqbb: (block_round (qc_vote_data (qc_of c)) <= round b); first by [].
  move/negbT: Hqbb; rewrite -ltnNge=> Hqbb; rewrite maxnAC; rewrite  [maxn (round b).+1 _]maxnCA; move/maxn_idPr: (Hqbb)=>->.
  rewrite 2!maxnA -/(comparator state) [maxn (maxn (comparator _) _) _]maxnAC; move/ltnW: (leq_ltn_trans Hcpb Hqbb); move/maxn_idPr=>->.
  move: (leq_maxr (last_vote_round state).+1 (preferred_block_round state)); rewrite -/(comparator state)=> Hprcsb.
  by rewrite maxnAC; move: (leq_ltn_trans (leq_trans Hprcsb Hcpb) Hqbb); move/ltnW/maxn_idPr=>->.
by rewrite andbAC -voting_comparator_eq Hc andFb andbAC -voting_comparator_eq Hb andFb.
Qed.

Lemma comparator_next state1 state2 b:
  comparator state1 = comparator state2
  -> comparator (next_state state1 b) = comparator (next_state state2 b).
Proof.
move=> H12; case H1: (voted_on state1 b); move: (H1); rewrite voting_comparator_eq H12 -voting_comparator_eq=> H2.
- by rewrite (voting_comparator H1) (voting_comparator H2).
by rewrite (non_voting_comparator (negbT H1)) (non_voting_comparator (negbT H2)) H12.
Qed.

Lemma comparator_processing state1 state2 bseq:
  comparator state1 = comparator state2
  -> comparator (node_processing state1 bseq).1 = comparator (node_processing state2 bseq).1.
Proof.
elim: bseq state1 state2 =>[| x s IHs] state1 state2 H12 //.
by rewrite 2!node_processing_cons1 (IHs _ _ (comparator_next x H12)).
Qed.

Lemma comparator_push_right state bs b:
  comparator (node_processing state (b::bs)).1 = comparator (node_processing state (rcons bs b)).1.
Proof.
elim: bs state b => [|x s IHs] state b //=.
rewrite -rcons_cons -node_processing_rcons; move/comparator_next: (IHs state x)=>->.
rewrite -node_processing_rcons comparatorC 2!node_processing_rcons.
rewrite node_processing_cons1 IHs -node_processing_cons1 -rcons_cons -node_processing_rcons.
by move/comparator_next: (IHs state b)=>->; rewrite node_processing_rcons.
Qed.

Lemma next_state_repeat state b:
  (next_state (next_state state b) b) = (next_state state b).
Proof.
rewrite next_state_lvr_if voting_next_N update_maxn next_state_pbr_update update_maxn  /= -maxnA maxnn.
rewrite -/(preferred_block_round {| last_vote_round := last_vote_round state;
  preferred_block_round := maxn (preferred_block_round state) (qc_round b) |}).
rewrite -update_maxn -next_state_pbr_update.
have H: forall s, s = {| last_vote_round := (last_vote_round s);
                    preferred_block_round:= (preferred_block_round s)|}; first by case.
by rewrite {3}(H (next_state state b)).
Qed.

Lemma comparator_repeat state b:
  comparator (next_state (next_state state b) b) =
  comparator (next_state state b).
Proof.
by rewrite next_state_repeat.
Qed.

Lemma comparator_predC1 state bs b:
  b \in bs ->
  comparator (node_processing state bs).1 =
  comparator (node_processing (next_state state b) (filter (predC1 b) bs)).1.
Proof.
elim: bs state b =>[|x s IHs] // state b.
rewrite in_cons node_processing_cons1; case Hx: (b \in s).
- move=>_; rewrite (IHs _ _ Hx); case Hbx: (b == x).
  - by move/eqP: Hbx=>->; rewrite (comparator_processing _ (comparator_repeat _ _)) {2}/filter /predC1 /= eq_refl /=.
   by rewrite (comparator_processing _ (comparatorC state x b)) {2}/filter /predC1 /= eq_sym Hbx /= -node_processing_cons1.
rewrite orbF=> Hbx; move/negbT: Hx; rewrite -not_in_all_predC1; move/all_filterP; rewrite /filter /predC1 /= eq_sym Hbx /==>->.
by move/eqP: Hbx=><-.
Qed.

Lemma comparator_orderfree state bs1 bs2:
  bs1 =i bs2 ->
  comparator (node_processing state bs1).1 = comparator (node_processing state bs2).1.
Proof.
elim: bs1 state bs2 => [|x s IHs] state bs2 H12 //; last rewrite node_processing_cons1.
- by case: bs2 H12 => [|x2 s2] H12 //; move: (H12 x2); rewrite in_nil in_cons eq_refl.
case Hx: (x \in s).
- have: s=ibs2; first by move=> y; rewrite -H12 in_cons; move: Hx; case Hxy: (y == x); [move/eqP: Hxy=>->->| rewrite orFb].
  move: (predC1_split Hx); move/IHs=>->; rewrite node_processing_cons1 (comparator_processing _ (comparator_repeat state x)).
  rewrite -node_processing_cons1; move/IHs: (predC1_split Hx)=><-; apply IHs.
have: s=i (filter (predC1 x) bs2); first move => y.
- move: (H12 y); rewrite in_cons mem_filter /predC1 /=; case Hyx: (y == x); by [move/eqP: Hyx=>->| rewrite andTb orFb].
  by move/IHs=>->; move: (mem_head x s); rewrite H12; move/comparator_predC1=>->.
Qed.

Lemma voted_in_processing_repeat state b bs:
  voted_in_processing (next_state state b) (b:: bs) =
  voted_in_processing (next_state state b) (bs).
Proof.
rewrite /voted_in_processing !node_processing_cons !mask_cons.
by rewrite voting_next_N next_state_repeat.
Qed.

Lemma voted_in_processing_comparison state1 state2 bs:
  comparator state1 = comparator state2 ->
  voted_in_processing state1 bs = voted_in_processing state2 bs.
Proof.
elim: bs state1 state2=>[| x s IHs] state1 state2 H12 //.
rewrite /voted_in_processing 2!node_processing_cons 2!mask_cons.
rewrite -/(map snd) -/unzip2 -2!/(voted_in_processing (next_state _ x) s).
rewrite (IHs _ _ (comparator_next x H12)) /=.
by rewrite 2!voting_comparator_eq H12.
Qed.

Lemma voted_in_predC1 state b bs:
  voted_in_processing (next_state state b) (bs) =
  voted_in_processing (next_state state b) (filter (predC1 b) bs).
Proof.
elim: bs state b =>[| x s IHs] state b //=.
case Hbx: (x == b)=>/=.
- move/eqP: Hbx=>->; rewrite {1}/voted_in_processing node_processing_cons mask_cons.
  rewrite next_state_repeat voting_next_N -/(map snd) -/unzip2.
  by rewrite -/(voted_in_processing (next_state state b) s) IHs.
rewrite /voted_in_processing 2![(node_processing _ (x:: _)).2]node_processing_cons.
rewrite 2!mask_cons -/(map snd) -/unzip2 -/(voted_in_processing _ s).
rewrite (voted_in_processing_comparison _ (comparatorC _ _ _)) IHs.
by rewrite (voted_in_processing_comparison _ (comparatorC _ _ _)).
Qed.

Lemma voted_in_rundup state bs:
  voted_in_processing state bs = voted_in_processing state (rundup bs).
Proof.
elim: bs state =>[| x s IHs] state //=.
rewrite /voted_in_processing 2!node_processing_cons /unzip2 map_cons mask_cons.
rewrite -/(voted_in_processing (next_state state x) s) IHs .
rewrite mask_cons -/(map snd) -/unzip2 -/(voted_in_processing (next_state state x) _).
by rewrite -voted_in_predC1.
Qed.

Lemma voted_in_processing_state_orderfree state bs1 bs2 bseq:
  bs1 =i bs2 ->
  voted_in_processing (node_processing state bs1).1 bseq =
  voted_in_processing (node_processing state bs2).1 bseq.
Proof.
move=> H; apply (voted_in_processing_comparison _ (comparator_orderfree _ H)).
Qed.

Lemma voted_in_processing_idx state bseq b:
  (b \in (voted_in_processing state bseq)) =
  (voted_on (nth state (unzip1 (node_processing state bseq).2) (index b bseq) ) b && (b \in bseq)).
Proof.
rewrite voted_in_rundup.
elim: bseq b state =>[| bb bbs IHbb] b state /=.
- by rewrite in_nil andbF.
rewrite /voted_in_processing /= 2!node_processing_cons /unzip2 mask_cons -/(map snd) /=.
case H: (bb == b).
- move/eqP: H=> ->; rewrite in_cons eqxx.
  case H2: (voted_on state b); first by rewrite in_cons eqxx orTb andbT.
  rewrite /=; apply: negbTE; apply: contraT; move/negPn=>H.
  by move: (mem_mask H); rewrite mem_filter /= eq_refl.
rewrite mem_cat mem_nseq in_cons eq_sym H andbF 2!orFb.
rewrite -/unzip2 -/(voted_in_processing (next_state state bb) _).
rewrite -voted_in_predC1 IHbb /=; case Hbbs: (b\in bbs); last by rewrite 2!andbF.
rewrite (nth_in_default_irrel (next_state state bb) state _); first by [].
by rewrite size_map size_processing index_mem.
Qed.

Lemma voted_in_processing_exists state bseq b:
  (b \in voted_in_processing state bseq) ->
  exists s, (s \in (unzip1 (node_processing state bseq).2)) && (voted_on s b) && (b \in bseq).
Proof.
rewrite voted_in_processing_idx.
move/andP => [H Hb]; exists (nth state (unzip1 (node_processing state bseq).2) (index b bseq)).
rewrite H Hb 2!andbT; apply/(nthP state); exists (index b bseq)=> //.
by rewrite size_map size_processing index_mem.
Qed.

Lemma voted_in_processing_sorted state bseq:
  (sorted (fun b1 b2 => round b1 < round b2) (voted_in_processing state bseq)).
Proof.
move: state; elim bseq => [| b bs] //; rewrite /sorted=> IHs state //.
rewrite voted_in_processing_cons.
case Hv: (voted_on state b)=> //=.
move: (IHs (next_state state b)).
  case H:((voted_in_processing (next_state state b) bs))=> //= [x xs]->.
rewrite andbT (@leq_trans (comparator (next_state state b)))=> //.
- by rewrite (voting_comparator Hv) ltnSn.
move: (mem_head x xs); rewrite -H; move/voted_in_processing_exists=> [s].
move/andP=> [Hs]; move/andP: Hs=> [Hs]; rewrite voting_comparator_eq; move/andP => [Hlt Hbr] Hx.
apply: (leq_trans _ Hlt); move: (node_processing_sorted (next_state state b) (bs)); rewrite /sorted.
case Hunz1: (unzip1 (node_processing (next_state state b) bs).2) => [|y ys]; first by move: Hs; rewrite Hunz1 in_nil.
move: (Hunz1); rewrite node_processing_head; case Hbs: bs => [|z zs]; first by move: Hx; rewrite Hbs in_nil.
move/eqP; rewrite eqseq_cons; move/andP=>[Hy Hys]; rewrite -(eqP Hy).
move/(order_path_min comparators_transitive); move/allP; rewrite Hunz1 in Hs.
move: Hs; rewrite in_cons; case Hsy: (s == y).
by move/eqP: Hsy=>->; move/eqP: Hy=><-.
by move/orP=>[//|] Hin; apply.
Qed.

Lemma voted_in_processing_uniq state bseq:
  uniq (voted_in_processing state bseq).
Proof.
apply (sorted_uniq rounds_transitive rounds_irreflexive).
apply voted_in_processing_sorted.
Qed.

Lemma voted_in_processing_both state bseq b1 b2:
  (b1 != b2) ->
  (b1 \in (voted_in_processing state bseq)) ->
  (b2 \in (voted_in_processing state bseq)) ->
  (round b1 <= round b2) ->
  subseq ([:: b1; b2]) (voted_in_processing state bseq).
Proof.
move => Hneq H1 H2 H12; move: (cat_take_drop_in H1); move/eqP=> Hsplit.
move: (H2); rewrite -{1}Hsplit; rewrite mem_cat in_cons eq_sym.
move/negbTE: Hneq=>->; rewrite orFb; move/orP=>[|].
- rewrite -sub1seq=> H13; move: (subseq_refl [:: b1])=> H24; move: {H13 H24}(cat_subseq H13 H24)=> Hpref.
  move: (subseq_trans Hpref (prefix_subseq _ (drop (index b1 (voted_in_processing state bseq)).+1 (voted_in_processing state bseq)))).
  rewrite cat1s -catA cat1s Hsplit=> Hsub; move/subseq_sorted: Hsub; move/(_ _ _ (voted_in_processing_sorted state bseq)).
  by move/(_ rounds_transitive); rewrite /= ltnNge H12.
rewrite -sub1seq=> H24; move: (subseq_refl [::b1])=> H13; move: {H13 H24}(cat_subseq H13 H24)=> Hpref.
move: (subseq_trans Hpref (suffix_subseq (take (index b1 (voted_in_processing state bseq)) (voted_in_processing state bseq)) _)).
by rewrite 2!cat1s Hsplit.
Qed.

Lemma voted_in_processing_ltn state bseq b1 b2:
  (b1 != b2) ->
  (b1 \in (voted_in_processing state bseq)) ->
  (b2 \in (voted_in_processing state bseq)) ->
  (round b1 <= round b2) ->
  round b1 < round b2.
Proof.
move => Hneq Hb1 Hb2 Hb12; move:(voted_in_processing_both Hneq Hb1 Hb2 Hb12)=> Hsub.
move/subseq_sorted: Hsub; move/(_ _ _ (voted_in_processing_sorted state bseq)).
by move/(_ rounds_transitive) => /=; rewrite andbT.
Qed.

Lemma voted_in_processing_parent state bseq b1 b2:
  b1 != b2 ->
  parent b1 b2 ->
  (b1 \in (voted_in_processing state bseq)) ->
  (b2 \in (voted_in_processing state bseq)) ->
  subseq ([:: b1; b2]) (voted_in_processing state bseq).
Proof.
move=> Hneq Hpar Hb1 Hb2; apply voted_in_processing_both=> //.
move: (voted_in_processing_exists Hb2)=> [s /andP [/andP [_ H] _]].
move: H; rewrite ineq_voted_on; move/andP=>[_]; move/andP=>[_].
by apply leq_trans; move/andP: Hpar=> [_]; move/eqP=>->.
Qed.

Lemma voted_in_processing_subseq state bseq vote_seq v0:
  path parent v0 vote_seq ->
  (v0 \notin vote_seq) && uniq vote_seq ->
  {subset (v0::vote_seq) <= (voted_in_processing state bseq)} ->
  subseq (v0::vote_seq) (voted_in_processing state bseq).
Proof.
move: state bseq v0; elim vote_seq=> /= [|v vs IHvs] state bseq v0.
- by move=> _ _; rewrite sub1seq; apply; rewrite mem_seq1 eq_refl.
move/andP=> [Hpv0 Hpath]; move/andP=> [Hv0 Huniq] Hsst.
have Hssv: {subset [:: v & vs] <= voted_in_processing state bseq}.
- by move=> x Hx; apply Hsst; rewrite inE Hx orbT.
move: (IHvs state bseq v Hpath Huniq Hssv)=> IHs.
move: (Hv0); rewrite inE negb_or; move/andP=> [Hvv0 _].
have Hproc0: v0 \in voted_in_processing state bseq.
- by apply: Hsst; rewrite inE eq_refl.
have Hproc1: v \in voted_in_processing state bseq.
- by apply: Hsst; rewrite 2!inE eq_refl orbT.
move: (voted_in_processing_parent Hvv0 Hpv0 Hproc0 Hproc1)=> Hss0.
by rewrite -cat1s; apply: (subseq_stitch (voted_in_processing_uniq _ _)).
Qed.

(************************************************************)
(** Node Aggregation                                       **)
(************************************************************)


Definition node_aggregator bseq :=
  (foldl (fun stateNvote => voting_rule stateNvote.1) (genesis_state,false) bseq).1.


Definition commit_rule state (qc: QC)(bround: nat) :=
  let: potential_commit_round := (parent_block_round (qc_vote_data qc)) in
  if (potential_commit_round.+1 == (block_round (qc_vote_data qc))) &&
        ((block_round (qc_vote_data qc)).+1 == bround) then
    Some(potential_commit_round)
  else None.

End State.
