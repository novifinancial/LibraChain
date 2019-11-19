From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq choice fintype path finset.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From LibraChain
Require Import SeqFacts Chains HashSign Blocks ConsensusState BlockTree BFTFacts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Safety.
(* We require Hashes, Addresses, Signatures and PublicKeys to be numbers in *)
(* some fashion, i.e. to have an injective embedding in ints *)
Variable Hash : countType.

Variables (PublicKey: countType) (Signature: countType).
Variable Address: hashType PublicKey.

(* The Block Data (w/o signatures) *)
Notation BDataType := (BlockData Hash Signature Address Command NodeTime).

Variable hashB: BDataType -> Hash.
Hypothesis inj_hashB: injective hashB.

Variable verifB: Hash -> PublicKey -> Signature -> bool.

(* Block Type : block data with signatures *)
Notation BType := (BlockType inj_hashB verifB).
Notation QC := (QuorumCert Hash Signature (Phant Address)).

Canonical BDHType := Eval hnf in (Block_hashType inj_hashB).
Canonical BSType := Eval hnf in (Block_signType inj_hashB verifB).

Implicit Type b: BType.

Notation "# b" := (hashB b) (at level 20).

Parameter peers : seq Address.
Parameter GenesisBlock : BType.

(* f is the byzantine fraction (see below) *)
Variable f: nat.

(* boolean predicate for all signatures in a sequence to be valid *)
Definition all_valid (h: Hash) (s: seq (PublicKey * Signature)) :=
  all (fun ps => (@verify_op _ _ _ BSType h (fst ps) (snd ps))) s && (size s >= (2*f).+1).

Definition qc_valid (qc: QC) :=
  all_valid (block_hash (qc_vote_data qc)) (qc_votes qc).

Definition source_valid (block: BType) :=
  let: (p, s) := (block_source block) in
       (@verify_op _ _ _ BSType (#block) p s).


Notation BlockStore := (BlockTree inj_hashB verifB).

(* Nodes have a public key, log of processed blocks and block store*)
Record NodeState := mkNode {
    public_key: PublicKey;
    block_log: seq BType;
}.

Definition node_state2components (ns: NodeState) :=
  let: mkNode pk bl := ns in (pk, bl).

Definition components2node_state (tuple: PublicKey * seq BType) :=
  let: (pk, bl) := tuple in mkNode pk bl.

Lemma can_ns_components: ssrfun.cancel node_state2components components2node_state.
Proof. by move => []. Qed.

(* There are a half-dozen wrong things that have turned wrong for me to do this by hands, TODO: *)
(* diagnose & fix*)
Canonical BlockTree_eqType := (union_map_eqType [ordType of Hash] [eqType of BType]).

Definition ns_eqMixin := CanEqMixin can_ns_components.
Canonical ns_eqType := EqType _ ns_eqMixin.

Definition ns_choiceMixin := CanChoiceMixin can_ns_components.
Canonical ns_choiceType := ChoiceType _ ns_choiceMixin.

Definition ns_countMixin := CanCountMixin can_ns_components.
Canonical ns_countType := CountType _ ns_countMixin.

Notation GenesisState := (genesis_state inj_hashB verifB).

Definition voted_by_node(n: NodeState) :=
  (voted_in_processing GenesisState (block_log n)).

Definition addr_of(n: NodeState) := (hash_op Address (public_key n)).

Definition qc_addresses(qc: QC) :=
  map (hash_op Address) (unzip1 (qc_votes qc)).

Variable validator_nodes: seq NodeState.
Definition Validator:= seq_sub validator_nodes.

Hypothesis Huniq_vals: uniq validator_nodes.

(* There is a finite number of blocks at any given time *)

Definition all_blocks := foldl cat [::] (map (block_log) validator_nodes).

Definition BlockFinType := seq_sub all_blocks.

Section ValidBlocks.
(* Valid blocks are the small subType which presents with enough valid *)
(* signatures *)
Record valid_block : Type := mkValid {
    block :> BlockFinType;
    _: source_valid (val block) && qc_valid (qc_of (val block));
}.

Canonical valid_block_subType := Eval hnf in [subType for block].
Definition valid_block_eqMixin := Eval hnf in [eqMixin of valid_block by <:].
Canonical valid_block_eqType := Eval hnf in EqType _ valid_block_eqMixin.
Definition valid_block_choiceMixin := [choiceMixin of valid_block by <:].
Canonical valid_block_choiceType := Eval hnf in ChoiceType valid_block valid_block_choiceMixin.
Definition valid_block_countMixin := [countMixin of valid_block by <:].
Canonical valid_block_countType := Eval hnf in CountType valid_block valid_block_countMixin.
Canonical valid_block_subCountType := Eval hnf in [subCountType of valid_block].
Definition valid_block_finMixin := [finMixin of valid_block by <:].
Canonical valid_block_finType := Eval hnf in FinType valid_block valid_block_finMixin.
Canonical valid_block_subFinType := Eval hnf in [subFinType of valid_block].

Implicit Type vb : valid_block.

Definition valid vb mkB : valid_block :=
  mkB (let: mkValid _ vbP := vb return (source_valid (ssval (val vb))) && qc_valid (qc_of (ssval (val vb))) in vbP).

Lemma valid_blockE vb : valid (fun sP => @mkValid vb sP) = vb.
Proof. by case: vb. Qed.

Definition node_in_votes(n: NodeState): pred valid_block :=
  fun vb => addr_of n \in (qc_addresses (qc_of (ssval (val vb)))).

Definition block_in_voting(n: NodeState): pred valid_block :=
  fun (vb:valid_block) => has (fun b => #b == (qc_hash (ssval (val vb)))) (voted_by_node n).

Definition honest : pred NodeState := fun n =>
  [set vb |node_in_votes n vb] \subset [set vb|block_in_voting n vb].

Hypothesis BFT:
  (#|[set x : Validator |honest (val x)]| >= (2*f).+1) &&
  (size validator_nodes == (3*f).+1).
End ValidBlocks.

End Safety.
