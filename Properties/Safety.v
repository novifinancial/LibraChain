From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq choice fintype path finset.
Require Import Eqdep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SeqSubMissing.
Variables (T : choiceType) (s : seq T).
Local Notation sT := (seq_sub s).

Variable (D: pred T).

Lemma card_seq_sub : uniq s -> #|[set x:sT| D (val x)]| = size (filter D s).
Proof.
move=> Us; case: (pickP (fun x: sT => D(val x)))=> [x Px |P0].
- rewrite -(card_seq_sub (filter_uniq D Us)).
  move/valP: (x)=> Hx.
  have: (val x \in filter D s); first by rewrite mem_filter Px Hx.
  rewrite -(codom_val (seq_sub_subFinType (filter D s))).
  move/codomP=> [x0 Hxx0]; pose f := fun (x:sT) => insubd x0 (val x).
  rewrite -(@card_in_imset _ _ f); first apply eq_card.
  - move=> x1; rewrite inE; apply/idP; apply/imsetP.
    move/valP: (x1); rewrite mem_filter; move/andP=> [Dx1 Hx1].
    exists (insubd x (val x1)); last by rewrite /f /= insubdK; [rewrite valKd| rewrite Hx1 ].
    by rewrite /insubd (insubT _) inE /= Dx1.
  move=> y2 y1 Hy2 Hy1; rewrite in_set in Hy1; rewrite in_set in Hy2.
  rewrite /f /insubd (insubT _) /=; first by  rewrite mem_filter (valP y2) Hy2.
  rewrite (insubT _) /=; first by rewrite mem_filter (valP y1) Hy1.
  move=> Hyp1 Hyp2; case; apply val_inj.
rewrite cardsE; move/eq_card0: (P0)=>->; rewrite size_filter.
apply/eqP/negPn; rewrite eq_sym -lt0n -has_count.
rewrite negbT //; apply/hasP; move => [x Hx Dx].
move: Hx; rewrite -(codom_val (seq_sub_subFinType s))=> Hcd.
by move/codomP: Hcd=> [x0 Hxx0]; move: (P0 x0); rewrite -Hxx0 Dx.
Qed.

End SeqSubMissing.

From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From LibraChain
Require Import SeqFacts Chains HashSign Blocks ConsensusState BlockTree BFTFacts.

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

Implicit Type b: BDataType.

Notation "# b" := (hashB b) (at level 20).

Parameter peers : seq Address.
Parameter GenesisBlock : BType.

(* f is the byzantine fraction (see below) *)
Variable f: nat.

(* boolean predicate for all signatures in a sequence to be valid *)
Definition all_valid (h: Hash) (s: seq (PublicKey * Signature)) :=
  all (fun ps => (@verify_op _ _ _ BSType h (fst ps) (snd ps))) s.

Definition qc_valid (qc: QC) :=
  all_valid (block_hash (qc_vote_data qc)) (qc_votes qc) && (uniq (qc_votes qc)).

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

Notation GenesisState := (genesis_state inj_hashB verifB ).

Definition voted_by_node(n: NodeState) :=
  (voted_in_processing GenesisState [seq block_data i | i <- block_log n]).

Definition addr_of(n: NodeState) := (hash_op Address (public_key n)).

Definition qc_keys(qc: QC) :=
  unzip1 (qc_votes qc).

Definition qc_addresses(qc: QC) :=
  map (hash_op Address) (qc_keys qc).

Variable validator_nodes: seq NodeState.
Hypothesis Huniq: uniq validator_nodes.
Hypothesis inj_keys: {in validator_nodes, injective public_key}.

Definition Validator:= seq_sub validator_nodes.

Definition node_keys :=
  map public_key validator_nodes.

Definition NodeKey := seq_sub node_keys.

Lemma mem_node_keys (v: Validator):
  (public_key (val v)) \in node_keys.
Proof.
rewrite /node_keys; apply/mapP; exists (val v)=> //.
by move/valP: (v).
Qed.

Definition to_pk (v: Validator): NodeKey :=
  Sub (public_key (val v)) (mem_node_keys v).

Lemma inj_to_pk : injective to_pk.
Proof.
move=> x1 x2; case; by move/(inj_keys (valP x1))/val_inj.
Qed.

Definition qc_relevant(qc: QC):=
  filter (fun pk => pk \in node_keys) (undup (qc_keys qc)).

Hypothesis Huniq_vals: uniq validator_nodes.

(* There is a finite number of blocks at any given time *)

Definition all_blocks := foldl cat [::] (map (block_log) validator_nodes).

Definition BlockFinType := seq_sub all_blocks.

Section ValidBlocks.
(* Valid blocks are the small subType which presents with enough valid *)
(* signatures *)
Record valid_block : Type := mkValid {
    block :> BlockFinType;
    _: source_valid (val block) && qc_valid (qc_of (val block)) && (size (qc_relevant (qc_of (val block))) == 2*f+1);
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

Definition type_val (vb: valid_block) : BType :=
  ((val \o val) vb).
Coercion type_val: valid_block >-> BType.

Definition data_val (vb: valid_block) : BDataType :=
  ((val \o val) vb).
Coercion data_val: valid_block >-> BDataType.

Definition valid vb mkB : valid_block :=
  mkB (let: mkValid _ vbP := vb return (source_valid vb) && qc_valid (qc_of vb) && (size (qc_relevant (qc_of vb)) == 2*f+1) in vbP).

Lemma valid_blockE vb : valid (fun sP => @mkValid vb sP) = vb.
Proof. by case: vb. Qed.

(* node_in_votes captures the inclusion of this node in the block's signatures *)
Definition node_in_votes(n: NodeState): pred valid_block :=
  fun vb => addr_of n \in (qc_addresses (qc_of vb)).

Notation "'qc#' vb" := (qc_hash vb) (at level 40).

Notation "'qc_round' vb" :=
  (block_round (qc_vote_data (qc_of vb))) (at level 40).

(* block_in_voting captures the inclusion of the valid block in the node's *)
(* voting log  *)
Definition block_in_voting(n: NodeState): pred valid_block :=
  fun (vb:valid_block) => has (fun b => (parent hashB) b vb) (voted_by_node n).

(* This captures that the only blocks one can find this node's signatures are *)
(* those in its voting log => the node only votes according to the procedure *)
(* we describe in voted_by_node. *)
Definition honest : pred NodeState := fun n =>
  [set vb |node_in_votes n vb] \subset [set vb|block_in_voting n vb].

Hypothesis BFT:
  (#|[set x : Validator |honest (val x)]| >= (2*f).+1) &&
  (size validator_nodes == (3*f).+1).

(* the definition of node_in_votes through the injective hashes (addresses) of *)
(* public keys is the same as enumerating the public keys *)
Lemma nodes_in_votes_relevantE vb:
  [set v: Validator| node_in_votes (val v) vb] =
  [set v: Validator| (public_key (val v)) \in (qc_keys (qc_of vb))].
Proof.
apply eq_finset=> x/=.
rewrite /node_in_votes /qc_addresses /addr_of mem_map //.
by apply hash_inj.
Qed.

Lemma validators_in_votes vb:
  #|[set v: Validator| node_in_votes (val v) vb]| == (2*f).+1.
Proof.
rewrite -addn1.
move/valP/andP: (vb)=>[_]; move/eqP=><-; rewrite nodes_in_votes_relevantE.
rewrite (@card_seq_sub _ _ (fun (v:NodeState) => (public_key v) \in _) Huniq).
rewrite -(size_map public_key) -uniq_size_uniq.
- rewrite map_inj_in_uniq ?filter_uniq //.
  move=> x y; rewrite 2!mem_filter; move/andP=>[_ Hx]; move/andP=>[_ Hy].
  by apply (inj_keys Hx).
- by rewrite /qc_relevant filter_uniq // undup_uniq.
move=> x; rewrite /qc_relevant /node_keys mem_filter mem_undup.
by rewrite -filter_map mem_filter /= andbC.
Qed.

(* The intersection lemma implies a honest validator voted for any pair of blocks*)
Lemma honest_in_two_blocks (vb1 vb2: valid_block):
    exists (x:Validator), (node_in_votes (val x) vb1 && node_in_votes (val x) vb2 && honest (val x)).
Proof.
move: (validators_in_votes vb1) (validators_in_votes vb2)=> Hvb1 Hvb2.
move/andP: (conj Hvb1 Hvb2)=> H12; move: {Hvb1 Hvb2 H12}(intersectionP Huniq BFT H12).
move=>[x]; rewrite 4!inE; move/andP => [H12 Hhx]; move/andP: {H12}H12=>[H1 H2].
by exists x; rewrite Hhx H1 H2.
Qed.

(* That node has both blocks in its logs *)
Lemma honest_voted_two_blocks (vb1 vb2: valid_block):
  exists (n: Validator), (block_in_voting (val n) vb1) && (block_in_voting (val n) vb2 && honest(val n)).
Proof.
move: (honest_in_two_blocks vb1 vb2)=> [x]; move/andP=> [H12 Hh].
move/andP: H12=> [H1 H2]; exists x; rewrite Hh.
move/subsetP: (Hh); move/(_ vb1); rewrite inE H1 inE=> -> //.
by move/subsetP: Hh; move/(_ vb2); rewrite inE H2 inE=> -> //.
Qed.

Lemma block_in_voting_processingP (n:NodeState) vb:
  (block_in_voting n vb) ->
  exists b, (parent hashB b vb)  &&
    (b \in (voted_in_processing GenesisState [seq block_data i | i <- block_log n])).
Proof.
by move/hasP=> [b Hvb Hhb]; exists b; rewrite Hhb.
Qed.

(* This is S2 in LibraBFT v2. The statement on state hashes is trivial *)
(* editing block_in_voting, and non-essential for the proof *)
Lemma valid_blocks_same_round_equal (vb1 vb2: valid_block):
  (qc_round vb1 == qc_round vb2) -> qc# vb1 == qc# vb2.
Proof.
move=> Hr.
move: (honest_voted_two_blocks vb1 vb2)=> [n]; move/andP=> [H1 /andP[H2 Hh]].
move/block_in_voting_processingP: H1=> [b1 /andP [Hb1 Hproc1]].
move/block_in_voting_processingP: H2=> [b2 /andP [Hb2 Hproc2]].
case H12: (b1 == b2).
- by move/andP: Hb1=>[/andP[/andP[/eqP[<-] _] _] _]; move/andP: Hb2=>[/andP[/andP[/eqP[<-] _] _] _]; move/eqP: H12=>->.
case/orP: (leq_total (round b1) (round b2)).
- move/(voted_in_processing_ltn (negbT H12) Hproc1 Hproc2); move/ltn_eqF.
  by move/andP: Hb1=>[/andP[/andP[_ /eqP[->]] _] _]; move/andP: Hb2=>[/andP[/andP[_ /eqP[->]] _] _]; rewrite Hr.
rewrite eq_sym in H12.
move/(voted_in_processing_ltn (negbT H12) Hproc2 Hproc1); move/ltn_eqF.
by move/andP: Hb1=>[/andP[/andP[_ /eqP[->]] _] _]; move/andP: Hb2=>[/andP[/andP[_ /eqP[->]] _] _]; rewrite eq_sym Hr.
Qed.

Lemma valid_qc_ancestor_is_parent (n: NodeState) (block: BType) vb:
  parent hashB block vb ->
  block_in_voting n vb ->
  (block_data block \in (voted_in_processing GenesisState [seq block_data i | i<- block_log n])).
Proof.
move=> Hpar.
move/block_in_voting_processingP=> [b0 /andP[/andP [/andP [/andP [Hb0 Hrd0] Hqc0] Hqcr0] Hproc0]].
move: (Hb0); move/andP: Hpar=> [/andP[/andP [/eqP[<-] _] _] _]; move/eqP/inj_hashB=> Hbb0.
by rewrite -Hbb0.
Qed.

(* The parenthood relationship over valid blocks *)
Definition vb_parent :=
  [eta (parent hashB): rel valid_block].

(* The chaining relationship — parents with consecutive round — over valid blocks *)
Definition vb_chained (vb1 vb2: valid_block) :=
  direct_parent vb1 vb2.


End ValidBlocks.

End Safety.
