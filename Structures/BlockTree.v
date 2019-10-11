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

(* Canonical BDHType := Eval hnf in (Block_hashType inj_hashB). *)
(* Canonical BSType := Eval hnf in (Block_signType inj_hashB verifB). *)

Implicit Type b: BType.

Notation "# b" := (hashB b) (at level 20).

Parameter peers : seq Address.
Parameter GenesisBlock : BType.

(* In fact, it's a forest, as it also keeps orphan blocks *)
Definition BlockTree := union_map Hash BType.
(* Canonical umBlockTree := Eval hnf in [um_class of BlockTree]. *)

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
    if find (qc_hash b) bt is Some parent then
      (#b \\-> b \+ bt)
    else bt.

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

Definition voting_rule(state: ConsensusState)(bp: BType) :=
  match (round bp), (last_vote_round state), (preferred_block_round state) with
  | rd, lvr, pvr =>
    if [&& rd > lvr & rd >= pvr] then
      let newState := mkConsensusState rd pvr in
      (true, newState)
    else (false, state)
  end.


Definition commit_rule(state: ConsensusState)(qc: QC)(bround: nat) :=
  let: potential_commit_round := (parent_block_round (qc_vote_data qc)) in
  if (potential_commit_round.+1 == (block_round (qc_vote_data qc))) && ((block_round (qc_vote_data qc)).+1 == bround) then
    Some(potential_commit_round)
  else None.

Definition update(state: ConsensusState)(qc: QC) :=
  let: round := (block_round (qc_vote_data qc)) in
  if (round > preferred_block_round state) then
    mkConsensusState (last_vote_round state) (round)
  else
    state.

End Forests.
