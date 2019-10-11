From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype ssrfun seq path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From LibraChain
Require Import SeqFacts Chains HashSign.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* We now define VoteData, which is something we know how to hash and sign*)

Open Scope sign_scope.
Section BlockType.

Variable Hash: ordType.

Record VoteData := mkVD {
  block_hash: Hash;
  executed_hash: Hash;
  block_round: nat;
  parent_block_hash: Hash;
  parent_block_round: nat;
}.

(* The VoteMsg assume there's a way to hash and sign VoteData*)
Variables (PublicKey: Type) (Signature: eqType)
            (HashV: signType VoteData PublicKey Signature).

Definition VD_eqMixin :=
  Eval hnf in (InjEqMixin (@hash_inj _ HashV)).
Canonical VD_eqType :=
  Eval hnf in EqType _ VD_eqMixin.

Variable Address: hashType PublicKey.

Record VoteMsg := mkVM {
  vote_data: VoteData;
  vote: (PublicKey * Signature);
}.

Definition PK_eqMixin :=
  Eval hnf in InjEqMixin (@hash_inj _ Address).
Canonical PK_eqType :=
  Eval hnf in EqType _ PK_eqMixin.

Definition vm2triple (v: VoteMsg) :=
  let: mkVM vd pks := v in (vd, pks).

Definition triple2vm (triple: VoteData * (PublicKey * Signature)) :=
  let: (vd, pks) := triple in mkVM vd pks.

Lemma can_vm_triple: ssrfun.cancel vm2triple triple2vm.
Proof. by move => []. Qed.

Definition vm_eqMixin := CanEqMixin can_vm_triple.
Canonical vm_eqType := EqType _ vm_eqMixin.

Record QuorumCert := mkQC {
  qc_vote_data: VoteData;
  qc_votes: seq (PublicKey * Signature);
}.

Definition qc2votes (qc: QuorumCert) :=
  let: mkQC vd votes := qc in (vd, votes).
Definition votes2qc (vs: VoteData * seq (PublicKey * Signature)) :=
  let: (vd, votes) := vs in mkQC vd votes.
Lemma can_qc_votes: ssrfun.cancel qc2votes votes2qc.
Proof. by move => []. Qed.

Definition qc_eqMixin := CanEqMixin can_qc_votes.
Canonical qc_eqType := EqType _ qc_eqMixin.

(* We can finally define the block type *)

(* The hashability implies the eqType*)
Variable Command: Type.
Variable NodeTime: Type.

Record BlockData := mkBD {
    (* Parent's hash pointer is in the QC *)
    (* Payload *)
    txs : seq Command;
    (* UnixTime (see liveness) *)
    time: NodeTime;
    round: nat;
    (* Parent's QC information *)
    proof : QuorumCert;
}.

Variable hashB: BlockData -> Hash.
Hypothesis hashB_inj: injective hashB.

Definition Block_hashMixin :=
  Eval hnf in HashMixin hashB_inj.

Canonical Block_hashType :=
  Eval hnf in HashType BlockData Hash Block_hashMixin.

Variable verifB: Hash -> PublicKey -> Signature -> bool.

Definition Block_signMixin :=
  Eval hnf in SignMixin verifB.

Canonical Block_signType :=
  Eval hnf in SignType BlockData PublicKey Signature Hash Block_signMixin.

Record BlockType := mkB {
  block_data: BlockData;
  block_source: PublicKey * Signature;
}.

Definition BD_eqMixin :=
  Eval hnf in (InjEqMixin (@hash_inj _ Block_hashType)).
Canonical BD_eqType :=
  Eval hnf in EqType _ BD_eqMixin.

Definition bt2bdnsource (bt: BlockType) :=
  let: mkB bd source := bt in (bd, source).
Definition bdnsource2bt (bdnsource: BlockData * (PublicKey * Signature)) :=
  let: (bd, source) := bdnsource in mkB bd source.
Lemma can_bt_bdnsource: ssrfun.cancel bt2bdnsource bdnsource2bt.
Proof. by move => []. Qed.

Definition bt_eqMixin := CanEqMixin can_bt_bdnsource.
Canonical bt_eqType := EqType _ bt_eqMixin.


End BlockType.
