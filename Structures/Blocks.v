From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype ssrfun seq path choice.
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

Variable Hash: countType.

Definition pickle_ordering: rel [eqType of Hash] :=
  fun h1 h2 => (pickle h1) < (pickle h2).

Lemma pickle_irref: irreflexive pickle_ordering.
Proof. by move => x; rewrite /pickle_ordering ltnn. Qed.
Lemma pickle_trans: transitive pickle_ordering.
Proof. by move => x y z; rewrite /pickle_ordering; apply ltn_trans. Qed.
Lemma pickle_spec:  forall x y, [|| pickle_ordering x y, x == y | pickle_ordering y x].
Proof. move => x y; rewrite /pickle_ordering.
case H: (pickle x == pickle y).
- move/pcan_inj: (@pickleK Hash); move/(_ _ _ (eqP H))/eqP=>->.
  by rewrite orbT.
by move/negbT: H; rewrite neq_ltn orbCA=>->; rewrite orbT.
Qed.

Definition hash_ordMixin := OrdMixin pickle_irref pickle_trans pickle_spec.
Definition hash_ordType := OrdType _ hash_ordMixin.
Canonical hash_ordType.


Record VoteData := mkVD {
  block_hash: Hash;
  executed_hash: Hash;
  block_round: nat;
  parent_block_hash: Hash;
  parent_block_round: nat;
}.


Definition vote2nats (vd: VoteData) :=
  (block_hash vd, executed_hash vd, block_round vd, parent_block_hash vd, parent_block_round vd).
Definition nats2vote (nats: Hash * Hash * nat * Hash * nat) :=
  let: (bh, eh, br, ph, pr) := nats in mkVD bh eh br ph pr.
Lemma vote_nats_cancel: ssrfun.cancel vote2nats nats2vote.
Proof. by move => []. Qed.

Definition vote_data_eqMixin := CanEqMixin vote_nats_cancel.
Canonical vote_data_eqType :=
  Eval hnf in EqType _ vote_data_eqMixin.

Definition vote_data_choiceMixin := CanChoiceMixin vote_nats_cancel.
Canonical vote_data_choiceType :=
  Eval hnf in ChoiceType _ vote_data_choiceMixin.

Definition vote_data_countMixin := CanCountMixin vote_nats_cancel.
Canonical  vote_data_countType :=
  Eval hnf in CountType VoteData vote_data_countMixin.

(* The VoteMsg assume there's a way to hash and sign VoteData*)
(* The Pubkey, SignType are countTypes, reflecting they are serializable*)
Variables (PublicKey: countType) (Signature: countType)
            (HashV: signType VoteData PublicKey Signature).

(* Definition VD_eqMixin := *)
(*   Eval hnf in (InjEqMixin (@hash_inj _ HashV)). *)
(* Canonical VD_eqType := *)
(*   Eval hnf in EqType _ VD_eqMixin. *)

Variable Address: hashType PublicKey.

Record VoteMsg (phA: phant Address) := mkVM {
  vote_data: VoteData;
  vote: (PublicKey * Signature);
}.

(* Definition PK_eqMixin := *)
(*   Eval hnf in InjEqMixin (@hash_inj _ Address). *)
(* Canonical PK_eqType := *)
(*   Eval hnf in EqType _ PK_eqMixin. *)

Definition vm2triple (v: VoteMsg (Phant Address)) :=
  let: mkVM vd pks := v in (vd, pks).

Definition triple2vm (triple: VoteData * (PublicKey * Signature)) :=
  let: (vd, pks) := triple in mkVM (Phant Address) vd pks.

Lemma can_vm_triple: ssrfun.cancel vm2triple triple2vm.
Proof. by move => []. Qed.

Definition vm_eqMixin := CanEqMixin can_vm_triple.
Canonical vm_eqType := EqType _ vm_eqMixin.

Definition vm_choiceMixin := CanChoiceMixin can_vm_triple.
Canonical vm_choiceType := ChoiceType _ vm_choiceMixin.

Definition vm_countMixin := CanCountMixin can_vm_triple.
Canonical vm_countType :=
  Eval hnf in CountType _ vm_countMixin.

Record QuorumCert (phA: phant Address) := mkQC {
  qc_vote_data: VoteData;
  qc_votes: seq (PublicKey * Signature);
}.

Definition qc2votes (qc: QuorumCert (Phant Address)) :=
  let: mkQC vd votes := qc in (vd, votes).
Definition votes2qc (vs: VoteData * seq (PublicKey * Signature)) :=
  let: (vd, votes) := vs in mkQC (Phant Address) vd votes.
Lemma can_qc_votes: ssrfun.cancel qc2votes votes2qc.
Proof. by move => []. Qed.

Definition qc_eqMixin := CanEqMixin can_qc_votes.
Canonical qc_eqType := EqType _ qc_eqMixin.

Definition qc_choiceMixin := CanChoiceMixin can_qc_votes.
Canonical qc_choiceType := ChoiceType _ qc_choiceMixin.

Definition qc_countMixin := CanCountMixin can_qc_votes.
Canonical qc_countType :=
  Eval hnf in CountType _ qc_countMixin.

(* We can finally define the block type *)

(* The hashability would imply the eqType, but we need serializability -> *)
(* countType *)
Variable Command: countType.
Variable NodeTime: countType.

Record BlockData := mkBD {
    (* Parent's hash pointer is in the QC *)
    (* Payload *)
    txs : seq Command;
    (* UnixTime (see liveness) *)
    time: NodeTime;
    round: nat;
    (* Parent's QC information *)
    proof : QuorumCert (Phant Address);
}.

Definition bd2qudruplet (bd: BlockData) :=
  (txs bd, time bd, round bd, proof bd).
Definition quadruplet2bd (q: seq Command * NodeTime * nat * QuorumCert(Phant Address)) :=
  let: (tx, nt, r, pf) := q in mkBD tx nt r pf.
Lemma cancel_bd_quadruplet: ssrfun.cancel bd2qudruplet quadruplet2bd.
Proof. by move =>[]. Qed.

Definition bd_eqMixin := CanEqMixin cancel_bd_quadruplet.
Canonical bd_eqType := EqType _ bd_eqMixin.

Definition bd_choiceMixin := CanChoiceMixin cancel_bd_quadruplet.
Canonical bd_choiceType := ChoiceType _ bd_choiceMixin.

Definition bd_countMixin := CanCountMixin cancel_bd_quadruplet.
Canonical bd_countType :=
  Eval hnf in CountType _ bd_countMixin.

Record BlockType (hashB: BlockData -> Hash)(inj_hashB: injective hashB) (verifyB: Hash -> PublicKey -> Signature -> bool) := mkB {
  block_data: BlockData;
  block_source: PublicKey * Signature;
}.

Coercion block_data: BlockType >-> BlockData.

Section BlockStructures.

Variable hashB: BlockData -> Hash.
Hypothesis hashB_inj: injective hashB.

Definition Block_hashMixin :=
  Eval hnf in HashMixin hashB_inj.

Canonical Block_hashType :=
  Eval hnf in HashType BlockData [ordType of Hash] Block_hashMixin.

Variable verifB: Hash -> PublicKey -> Signature -> bool.

Definition Block_signMixin :=
  Eval hnf in SignMixin verifB.

Canonical Block_signType :=
  Eval hnf in SignType BlockData PublicKey Signature [ordType of Hash] Block_signMixin.

Definition BD_eqMixin :=
  Eval hnf in (InjEqMixin (@hash_inj _ Block_hashType)).
Canonical BD_eqType :=
  Eval hnf in EqType _ BD_eqMixin.

Definition bt2bdnsource (bt: BlockType hashB_inj verifB) :=
  let: mkB bd source := bt in (bd, source).
Definition bdnsource2bt (bdnsource: BlockData * (PublicKey * Signature)) :=
  let: (bd, source) := bdnsource in mkB hashB_inj verifB bd source.
Lemma can_bt_bdnsource: ssrfun.cancel bt2bdnsource bdnsource2bt.
Proof. by move => []. Qed.

Definition bt_eqMixin := CanEqMixin can_bt_bdnsource.
Canonical bt_eqType := EqType _ bt_eqMixin.
Definition bt_choiceMixin := CanChoiceMixin can_bt_bdnsource.
Canonical bt_choiceType := ChoiceType _ bt_choiceMixin.
Definition bt_countMixin := CanCountMixin can_bt_bdnsource.
Canonical bt_countType := CountType _ bt_countMixin.


End BlockStructures.

End BlockType.
