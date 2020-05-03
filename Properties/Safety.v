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

(* f is the byzantine fraction (see below) *)
Variable f: nat.

(* boolean predicate for all signatures in a sequence to be valid *)
Definition all_valid (h: Hash) (s: seq (PublicKey * Signature)) :=
  all (fun ps => (@verify_op _ _ _ BSType h (fst ps) (snd ps))) s.

(* a valid qc only contains distinct and valid signatures *)
Definition qc_valid (qc: QC) :=
  all_valid (block_hash (qc_vote_data qc)) (qc_votes qc) && (uniq (qc_votes qc)).

(* a valid block is properly signed by its emitter *)
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

Definition all_blocks :=
  flatten [seq block_log n | n <- validator_nodes].

Definition BlockFinType := seq_sub all_blocks.

Section ValidBlocks.

Definition valid_pred (block: BType) :=
  source_valid block && qc_valid (qc_of block) && (size (qc_relevant (qc_of block)) == 2*f+1) && (qc_hash block != #block).

(* Valid blocks are the small subType which presents with enough valid *)
(* signatures *)
Record valid_block : Type := mkValid {
    block :> BlockFinType;
    _: valid_pred (val block);
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
  mkB (let: mkValid _ vbP := vb return (source_valid vb) && qc_valid (qc_of vb) && (size (qc_relevant (qc_of vb)) == 2*f+1) && (qc_hash vb != #vb) in vbP).

Lemma valid_blockE vb : valid (fun sP => @mkValid vb sP) = vb.
Proof. by case: vb. Qed.

Parameter GenesisBlock : valid_block.

(* node_in_votes captures the inclusion of this node in the block's signatures *)
Definition node_in_votes(n: NodeState): pred valid_block :=
  fun vb => addr_of n \in (qc_addresses (qc_of vb)).

Notation "'qc#' vb" := (qc_hash vb) (at level 40).

(* The parenthood relationship over valid blocks *)
Definition vb_parent :=
  [eta (parent hashB): rel valid_block].

(* The chaining relationship — parents with consecutive round — over valid blocks *)
Definition vb_chained (vb1 vb2: valid_block) :=
  direct_parent vb1 vb2.

Definition voted_by_node(n: NodeState): seq BType :=
  [ seq b <- block_log n | ((block_data b) \in voted_in_processing GenesisState [seq block_data i | i <- block_log n]) && (valid_pred b)].

(* block_in_voting captures the inclusion of the valid block in the node's *)
(* voting log  *)
Definition block_in_voting(n: NodeState): pred valid_block :=
  fun (vb:valid_block) => has (fun b:BType => parent hashB b vb) (voted_by_node n).

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
move/valP/andP: (vb)=> [/andP[_ H] _]; move/eqP: H=><-; rewrite nodes_in_votes_relevantE.
rewrite (@card_seq_sub _ _ (fun (v:NodeState) => (public_key v) \in _) Huniq).
rewrite -(size_map public_key) -uniq_size_uniq.
- rewrite map_inj_in_uniq ?filter_uniq //.
  move=> x y; rewrite 2!mem_filter; move/andP=>[_ Hx]; move/andP=>[_ Hy].
  by apply (inj_keys Hx).
- by rewrite /qc_relevant filter_uniq // undup_uniq.
move=> x; rewrite /qc_relevant /node_keys mem_filter mem_undup.
by rewrite -filter_map mem_filter /= andbC.
Qed.

Lemma honest_in_one_block (vb: valid_block):
  exists (x: Validator), (node_in_votes (val x) vb) && honest (val x).
Proof.
move/card_S2f_gt: (validators_in_votes vb); move/(_ Huniq)=> Hcard.
move: (Hcard _ BFT).
move/(leq_ltn_trans (leq0n f)); rewrite card_gt0; move/set0Pn=>[x].
rewrite !inE; move/andP=> [Hn Hh]; by exists x; apply/andP.
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

(* This is the off-by one difference between most formalisms of LibraBFT and *)
(* the present Coq formalization. LibraBFT often speaks of confirmed / QC'ed blocks and *)
(* focuses on the blocks, treating the downward blocks which QC confirms them *)
(* implicitly. We can't afford to do this in Coq — since we chose to not have *)
(* an entire separate relation and type for "dangling" QCs — hence we have to *)
(* be very explicit with naming these confirming blocks. Hence note that here, *)
(* we express that if vb is in the vote log of n, its parent is voted for. *)
Lemma block_in_voting_processingP (n:NodeState) vb:
  (block_in_voting n vb) ->
  exists b, (parent hashB b vb) &&
    (b \in (voted_in_processing GenesisState [seq block_data i | i <- block_log n])).
Proof.
move/hasP=> [b Hvb Hhb]; exists b; rewrite Hhb andTb.
by move: Hvb; rewrite mem_filter; move/andP=> [/andP[-> Hval] Hlog].
Qed.

(* This is S2 in LibraBFT v2. The statement on state hashes is trivial *)
(* editing block_in_voting *)
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

(* Lemma S3 in LibraBFT v2, ported to v3 formalization *)
(* See comment of block_in_voting_processingP to understand why it takes us 4 *)
(* blocks to form a 3-chain *)
Lemma three_chain_higher (b0 b1 b2 c2 b c : valid_block):
  (path vb_chained b0 [:: b1 ; b2 ]) && (vb_parent b2 c2) &&
  (vb_parent b c) ->
  (round b > round b2) ->
  (* a.k.a. previous_round b > round b0 in this presentation*)
  (qc_round b >= round b0).
Proof.
move/andP=> [/andP[Hpath Hpar23] Hparbc].
move: (honest_voted_two_blocks c2 c)=> [n /andP[Hvot3 /andP[Hvotc Hh]] Hqc].
move: (valid_qc_ancestor_is_parent Hparbc Hvotc) => Hbvot.
move: Hpath; rewrite /vb_chained.
rewrite -cat1s cat_path; move/andP=>[Hb0b1]; rewrite /= andbT; move/andP=> [Hpar12 Hrd12].
move: Hb0b1; rewrite /= andbT; move/andP=> [Hpar01 Hrd01].
move: (valid_qc_ancestor_is_parent Hpar23 Hvot3) => H2vot.
move/andP: Hparbc=> [/andP[/andP[Hb /eqP[Hrd]] Hparent] Hparent_rd].
move/andP: (Hpar01)=> [/andP[/andP[H0 /eqP[Hrd0]] Hparent0] Hparent_rd0].
move/andP: (Hpar12)=> [/andP[/andP[H1 /eqP[Hrd1]] Hparent1] Hparent_rd1].
rewrite Hrd0 (eqP Hparent_rd1).
(* TODO : clean up type inference in this imbricated subtype*)
apply: (@voted_in_processing_subseq_qc_parent_rel _ _ _ _ _ _
        GenesisState [seq block_data i | i <- block_log (val n)]).
apply: voted_in_processing_both => //=.
- by apply/negPn=> H; move:Hqc; rewrite (eqP H) ltnn.
by rewrite ltnW.
Qed.

Lemma lt_wf_ind : forall (n : nat) (P : nat -> Prop),
  (forall n0 : nat, (forall m : nat, (m < n0) -> P m) -> P n0) ->
  P n.
Proof.
move=>n P H; apply: Wf_nat.lt_wf_ind=> [m mn].
by apply: (H m)=>[m0 m0m]; apply: mn; apply/ltP.
Qed.

Lemma logged_in_all_blocks (v: Validator) (b: BType):
  b \in block_log (val v) -> b \in all_blocks.
Proof.
move=> Hlog.
have H: (block_log (val v)) \in [seq block_log i | i <- validator_nodes].
- by apply/mapP; exists (val v)=> //; move/valP: (v).
by apply/flattenP; exists (block_log (val v)).
Qed.

Lemma valid_block_in_voting_processingP (v: Validator) vb:
  let n := val v in
  (block_in_voting n vb) ->
  exists b: valid_block, (vb_parent b vb) &&
    ((block_data b) \in (voted_in_processing GenesisState [seq block_data i | i <- block_log n])).
Proof.
rewrite /=; move/hasP=> [b Hvb Hhb].
move: Hvb; rewrite mem_filter; move/andP=> [/andP[Hvot Hval] Hlog].
move/logged_in_all_blocks: Hlog=>Hball; pose bb : BlockFinType := (Sub b Hball).
pose bv : valid_block := (Sub bb Hval).
exists bv; rewrite /= /vb_parent {1}/bv /parent.
by rewrite /type_val /comp !SubK -/(parent hashB b vb) Hhb andTb.
Qed.

(* Property S4 in LibraBFT v2, ported to v3 formalization *)

(* This includes a pretty strong variation in introducing d, the "lagging" *)
(* element in the blocks in comparison with the earlier three-chain.  'd' serves *)
(* exclusively to introduce a voted block carrying a QC for c, ensuring *)
(* qc_parent_round c < qc_round c, i.e.  qc_round b < round b, which is essential *)
(* to the use of the induction hypothesis. *)
(* We are therefore proving a weaker property than S4 — which is *)
(* incorrect as stated, though this technical error is of no consequence, since *)
(* the lemma yields the final theorem S5 anyway. *)
Lemma three_chain_linked (b0 b1 b2 c2 : valid_block):
  (path vb_chained b0 [:: b1 ; b2 ]) && (vb_parent b2 c2) ->
  forall n: nat,
    (forall b c d: valid_block, (round b == n) && (path vb_parent b [:: c ; d]) && (round b >= round b0) ->
                           (exists bs: seq valid_block, (path vb_parent b0 bs) && (block_data (last b0 bs) == b))).
Proof.
move=>Hchain; elim/lt_wf_ind=> n IHn b c d; move/andP=>[/andP[Hn /andP[Hparbc /andP[Hparcd _]]] Hbb0].
case Hbb2: (round b > round b2).
- have Hqcb: (qc_round b >= round b0); first by apply: (@three_chain_higher b0 b1 b2 c2 b c); rewrite // Hparbc andbT Hchain.
  (* qc_round b <= round b — this is the only part that uses d *)
  have Hqc_cd: qc_parent_round c <= qc_round c.
  - move: (honest_in_one_block d)=> [nd /andP[Hvotd]].
    move/subsetP; move/(_ d); rewrite 2!inE; move/(_ Hvotd)=> Hvotingd.
    move: (valid_qc_ancestor_is_parent Hparcd Hvotingd).
    by move/voted_in_processing_exists=>[sb /andP[/andP[_ Hd] _]]; move: (voted_br_gt_qcr Hd).
  move: (Hparbc) Hqc_cd; rewrite {1}/vb_parent /parent; move/andP=>[/andP[/andP[_ /eqP[<-]] _] /eqP[<-]].
  (* set parb and prove round parb = qc_round b *)
  move: (honest_in_two_blocks b c)=> [node /andP[/andP[Hvotb Hvotc] Hhon]]; move/subsetP: (Hhon); move/(_ b).
  rewrite 2!inE; move/(_ Hvotb); move/valid_block_in_voting_processingP=> [parb /andP[Hparbb Hvotparb]].
  move: (Hparbb); rewrite {1}/vb_parent {1}/parent; move/andP=> [/andP[/andP[Hparb_h /eqP[Hrb]] _] _].
  rewrite -Hrb=> Hrd_parbb.
  (* establish parb != b & the prelude for voted_in_processing_ltn *)
  have Hrounds_parb_b : round parb < round b.
  - move/subsetP: Hhon; move/(_ c); rewrite 2!inE; move/(_ Hvotc).
    move/valid_block_in_voting_processingP=> [parc /andP[Hparc Hvotparc]].
    move: (Hparc) (Hparbc); rewrite {1 2}/vb_parent {1 2}/parent.
    move/andP=>[/andP[/andP[Hparc_h _] _] _]; move/andP=>[/andP[/andP[Hb_h _] _] _].
    move: Hb_h; rewrite -(eqP Hparc_h); move/eqP/inj_hashB=>Heqparcb; rewrite -Heqparcb in Hvotparc Hparc.
    apply: (voted_in_processing_ltn _ Hvotparb Hvotparc Hrd_parbb).
    move/valP: (b); move/andP=>[_]; rewrite -(eqP Hparb_h).
    by apply/contra=> HH; apply/eqP; congr hashB; rewrite (eqP HH) /=.
  rewrite (eqP Hn) in Hrounds_parb_b; move: (IHn (round parb) Hrounds_parb_b parb b c); rewrite eqxx andTb.
  rewrite -Hrb in Hqcb; rewrite Hqcb /= 2!andbT Hparbb Hparbc /=.
  move/(_ is_true_true)=> [bs Hbs]; exists (rcons bs b).
  rewrite rcons_path last_rcons eqxx andbT; move/andP: Hbs=>[->] /=.
  by case bs=>[|x xs] /=; rewrite /vb_parent; move/eqP=>->.
(* Prequel: unzip the vb_chained assumption *)
move/andP: Hchain=> [Hchain Hb2c2]; have Hpar_chain: vb_parent b0 b1 && vb_parent b1 b2.
by move: Hchain; rewrite /= andbT /vb_chained /direct_parent /vb_parent; move/andP=> [/andP[-> _] /andP[-> _]].
have Hrd_chain: (round b1 == (round b0).+1) && (round b2 == (round b1).+1).
by move: Hchain; rewrite /= andbT /vb_chained /direct_parent; move/andP=> [/andP[_ ->] /andP[_ ->]].
(* Prequel : establish round b = qc_round c *)
move/andP: (Hparbc)=> [/andP[/andP[Hqch_c Hqc_c]  _ ] _].
move/negbT: Hbb2; rewrite -leqNgt leq_eqVlt; move/orP=>[Hbb2|Hbb2].
- move: Hb2c2; rewrite {1}/vb_parent {1}/parent; move/andP=>[/andP[/andP[Hqch_c2 Hqc_c2] _] _].
  move: Hbb2; rewrite (eqP Hqc_c2) (eqP Hqc_c); move/valid_blocks_same_round_equal.
  rewrite -(eqP Hqch_c) -(eqP Hqch_c2); move/eqP/inj_hashB=> Heq_bb2.
  by exists [:: b1; b2]; rewrite /= andbT Hpar_chain andTb eq_sym; apply/eqP.
move: Hbb2; move/andP: (Hrd_chain)=>[_ /eqP[->]]; rewrite ltnS leq_eqVlt; move/orP=> [Hbb1|Hbb1].
- move: Hbb1; rewrite (eqP Hqc_c); move/andP: (Hpar_chain)=>[_]; rewrite {1}/vb_parent {1}/parent.
  move/andP=> [/andP[/andP[Hqch_b1 /eqP[->]] _] _]; move/valid_blocks_same_round_equal.
  rewrite -(eqP Hqch_c) -(eqP Hqch_b1); move/eqP/inj_hashB=> Heq_bb1.
  by exists [:: b1]; rewrite /= Heq_bb1 eqxx 2!andbT; move/andP: Hpar_chain=> [-> _].
move: Hbb1; move/andP: Hrd_chain=> [/eqP[->] _]; rewrite ltnS=> Hbb1.
move: (eqn_leq (round b0) (round b)); rewrite {}Hbb0 {}Hbb1 andbT; move/idP.
move: Hpar_chain; rewrite andbC; move/andP=>[_]; rewrite {1}/vb_parent {1}/parent.
move/andP=> [/andP[/andP[Hqch_b0 /eqP[->]] _] _]; rewrite (eqP Hqc_c).
move/valid_blocks_same_round_equal; rewrite -(eqP Hqch_b0) -(eqP Hqch_c).
move/eqP/inj_hashB=> Hbb0.
by exists [::]=>/=; apply/eqP.
Qed.


Theorem safety (b0 b1 b2 c2: valid_block) (d0 d1 d2 e2: valid_block):
  (path vb_chained b0 [:: b1 ; b2 ]) && (vb_parent b2 c2) ->
  (path vb_chained d0 [:: d1 ; d2 ]) && (vb_parent d2 e2) ->
  (exists bs: seq valid_block, (path vb_parent b0 bs) && (block_data (last b0 bs) == d0)) \/
  (exists ds: seq valid_block, (path vb_parent d0 ds) && (block_data (last d0 ds) == b0)).
Proof.
wlog: b0 b1 b2 c2 d0 d1 d2 e2 / (round b0 <= round d0)=> H Hb0 Hd0.
- move/orP: (leq_total (round b0) (round d0))=>[H1|H1];
  [move: (H b0 b1 b2 c2 _ d1 d2 e2 H1 Hb0 Hd0) | move: (H d0 d1 d2 e2 _ b1 b2 c2 H1 Hd0 Hb0) ]; try by apply.
  by case; [right|left].
left; apply: (@three_chain_linked _ _ _ _ Hb0 (round d0) d0 d1 d2).
rewrite eq_refl andTb H andbT /= andbT; move/andP: Hd0=>[/andP[H1 /andP[H2 _]] _].
by rewrite /vb_parent; move/andP: H1=>[-> _]; move/andP: H2=>[-> _].
Qed.

End ValidBlocks.

End Safety.
