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
Require Import Recdef.

(* A formalization of a block forests *)
(*Some bits and pieces (btExtend relation properties) taken from *)
(*https://github.com/certichain/toychain *)

(************************************************************)
(******************* <parameters> ***************************)
(************************************************************)
Section Forests.

Variable Hash : countType.
Variables (PublicKey: countType) (Signature: countType) (Address: hashType PublicKey).

Parameters (Command NodeTime: countType).

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

Definition qc_of b := (proof (block_data b)).
Definition qc_hash b := (block_hash (qc_vote_data (qc_of b))).

Definition genesis_round := (round (block_data GenesisBlock)).

(* In fact, it's a forest, as it also keeps orphan blocks *)
Definition BlockTree := union_map [ordType of Hash] BType.

Implicit Type bt : BlockTree.

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

Lemma btExtendV bt b :
  valid (btExtend bt b) -> valid bt.
Proof.
rewrite/btExtend; case: ifP.
by case: ifP=>//=; rewrite valid_undef.
by move=>Nd; rewrite validPtUn Nd //==>[/andP] [].
Qed.

Lemma btExtendV_comm bt a b :
  valid (btExtend (btExtend bt a) b) =
  valid (btExtend (btExtend bt b) a).
Proof.
rewrite/btExtend; case: ifP; case: ifP; case: ifP; case: ifP;
move=>A B C D.
by rewrite D C B.
by rewrite D dom_undef in_nil validPtUn valid_undef.
by rewrite dom_undef in D.
by rewrite dom_undef in D.
- case: ifP; case: ifP.
  case: ifP=>X Y Z.
  by rewrite Y X in A; rewrite A in C.
  by rewrite find_undef in Z.
  by move=>X; move: D; rewrite domPtUn inE X Bool.orb_false_r=>/andP [] _;
     move/eqP=>->_ ; rewrite !validPtUn !inE.
  case: ifP=>X Y Z.
  by rewrite Y X in A; rewrite A in C.
  by rewrite Y X dom_undef in A.
  move=>X; move: D; rewrite domPtUn inE X Bool.orb_false_r=>/andP[]->.
    move/eqP=>E; move: A; rewrite X domPtUn inE=>/andP[]V _.
    move: B; rewrite E findUnR; last by move: V; rewrite !validPtUn.
    rewrite X findPt //==>/eqP []E'; subst b;
    by rewrite findUnR ?V //= X findPt //==>/eqP [].
- case: ifP.
  case: ifP=>X Y //=.
  by move: D; rewrite domPtUn inE Y=>/andP[] V _;
    move: B; rewrite findUnR ?V //= Y X.
  by move=>X; move: D; rewrite domPtUn inE X Bool.orb_false_r=>/andP [] V;
    move/eqP=>E; move: A; rewrite X E domPtUn inE eq_refl Bool.orb_true_l;
    move: V; rewrite !validPtUn C X !Bool.andb_true_r//==>->.
- case: ifP; case: ifP=>//=.
  case: ifP=>X Y Z=>//=.
  by rewrite Y X in A; rewrite A in C.
  move=>X; move: D; rewrite domPtUn inE X Bool.orb_false_r=>/andP [] V.
  move/eqP=>E; move: B; rewrite E !findUnR;
    do? by move:V; rewrite !validPtUn C X //=.
  by rewrite X !findPt //= eq_sym=>->.
- case: ifP.
  case: ifP=>X Y; move: B; rewrite findUnR.
  by case: ifP; [rewrite X | rewrite Y].
  by move: D; rewrite domPtUn inE validPtUn Y C //==>/andP[].
  by case: ifP; rewrite join_undefR.
  by move: D; rewrite domPtUn inE validPtUn Y C //==>/andP[].
  by rewrite joinA (joinC (#a \\-> _) (#b \\-> _)) -joinA;
     rewrite validPtUn inE D //= Bool.andb_false_r valid_undef.
- rewrite D in A *; case: ifP=>//=.
  rewrite findUnR. by rewrite C B.
  by move: A; rewrite domPtUn inE=>/andP[].
- rewrite D in A *.
  by rewrite validPtUn D !validPtUn A D //= !Bool.andb_true_r.
- case: ifP; case: ifP; do? by rewrite join_undefR.
  case: ifP=>X Y Z.
  by rewrite Z in B.
  by rewrite find_undef in Z.
  move=>X; rewrite findUnR. by rewrite C B.
  by move: A; rewrite X domPtUn validPtUn inE X C //=;
     rewrite Bool.orb_true_r !Bool.andb_true_r.
- case: ifP.
  case: ifP=>X Y; first by rewrite Y X C in A.
  by rewrite !join_undefR.
  rewrite joinA (joinC (#a \\-> _) (#b \\-> _)) -joinA.
  suff: (# a \\-> a \+ bt) = um_undef by move=>->.
  by apply invalidE; rewrite validPtUn C Bool.andb_false_r.
- case: ifP; case: ifP=>X Y; do? by rewrite X C in B.
  by rewrite find_undef in Y.
  by rewrite X dom_undef in_nil in B.
- case: ifP; first by rewrite !validPtUn A C D //= !Bool.andb_true_r.
  move: B; rewrite domPtUn inE C Bool.orb_false_r=>/andP[]V /eqP E.
  contradict D.
  rewrite domPtUn inE E eq_refl Bool.orb_true_l Bool.andb_true_r.
  by move: V; rewrite !validPtUn C //= Bool.andb_true_r=>/andP[]->.
- case: ifP=>X.
  contradict D.
    rewrite domPtUn inE A Bool.orb_true_r validPtUn C //=.
    case V: (valid bt)=>//=.
    move: (invalidE bt); rewrite V //=; case=>Z _.
    have T: true by []. specialize (Z T).
    by move: Z A=>->; rewrite dom_undef in_nil.
  by rewrite joinA (joinC (#b \\-> _)) -joinA !validPtUn //=;
     rewrite A //= Bool.andb_false_r valid_undef !Bool.andb_false_l.
by rewrite !joinA (joinC (#b \\-> _) (#a \\-> _)).
Qed.

Lemma btExtendV_fold1 bt bs b :
  valid (foldl btExtend bt (rcons bs b)) -> valid (foldl btExtend bt bs).
Proof.
rewrite -cats1 foldl_cat /= {1}/btExtend; case: ifP.
case: ifP=>_ _ =>//=; last by rewrite valid_undef.
by move=>_; rewrite validPtUn /= =>/andP[H _].
Qed.

Lemma btExtendV_fold bt xs ys :
  valid (foldl btExtend bt (xs ++ ys)) -> valid (foldl btExtend bt xs).
Proof.
elim/last_ind: ys=>[|ys y Hi]; first by rewrite cats0.
by rewrite foldl_cat; move/btExtendV_fold1; rewrite -foldl_cat; apply Hi.
Qed.

Lemma btExtendV_fold_xs bt xs :
  valid (foldl btExtend bt xs) -> valid bt.
Proof.
have X: xs = ([::] ++ xs) by rewrite cat0s.
by rewrite X; move/btExtendV_fold.
Qed.

Lemma btExtendV_fold_dup bt xs a b :
  valid (foldl btExtend bt (rcons xs a)) ->
  b \in xs -> #a = #b -> a = b.
Proof.
elim/last_ind: xs=>[|xs x H]//=.
rewrite -!cats1 !foldl_cat //=.
have E: (btExtend (btExtend (foldl btExtend bt xs) a) x) =
        foldl btExtend bt (rcons (rcons xs a) x)
by rewrite -!cats1 -catA !foldl_cat //=.
rewrite btExtendV_comm E=>V; move: (btExtendV_fold1 V)=>V0.
specialize (H V0); rewrite mem_cat inE=>/orP; case=>//=.
move/eqP=>Eq; subst x; move=>Hh.
case X: (a == b); first by move/eqP: X.
contradict V.
rewrite -!cats1 !foldl_cat //=.
move: (btExtendV_fold1 V0)=>V1.
rewrite{1}/btExtend; case: ifP.
- case: ifP.
  rewrite{5}/btExtend; case: ifP.
  case: ifP; last by rewrite valid_undef.
  rewrite -Hh.
  move=>A B C _; contradict C.
  by rewrite{1}/btExtend B A; move/eqP: A=>-> /eqP [] Y;
     rewrite Y eq_refl in X.
  move=>A B C D; move: B.
  by rewrite{1}/btExtend A -Hh findPtUn ?D //==>/eqP [] Y;
     rewrite Y eq_refl in X.
  by rewrite valid_undef.
move=>D; rewrite{1}/btExtend.
case: ifP.
case: ifP; last by rewrite join_undefR valid_undef.
by move=>B A; rewrite -Hh validPtUn A //= Bool.andb_false_r.
by rewrite -Hh joinA (joinC _ (foldl btExtend _ _));
   move=>_; apply/negP; apply invalidE; rewrite pts_undef join_undefR.
Qed.

Lemma btExtendH bt b : valid bt -> validH bt -> validH (btExtend bt b).
Proof.
move=>V H z c; rewrite /btExtend.
case: ifP=>X.
- case: ifP=>_; by [move/H | rewrite find_undef].
rewrite findUnL ?validPtUn ?V ?X//.
case: ifP=>Y; last by move/H.
rewrite domPtK inE in Y; move/eqP: Y=>Y; subst z.
by rewrite findPt; case=>->.
Qed.

Lemma btExtendH_fold bt bs :
  validH bt -> valid (foldl btExtend bt bs) ->
  validH (foldl btExtend bt bs).
Proof.
move=>Vh V'; elim/last_ind: bs V' =>[|xs x Hi] V'; first done.
move: (btExtendV_fold1 V')=>V; move: (Hi V).
rewrite -cats1 foldl_cat /= {2}/btExtend; case: ifP.
case: ifP=>//=; by move: validH_undef.
move=>D H; rewrite/validH=>h b; rewrite findUnR ?validPtUn ?V ?D //=.
case: ifP; first by move: (H h b).
by rewrite findPt2; case: ifP=>//= /andP[/eqP ->] _ _ [] ->.
Qed.

Lemma btExtendIB bt b :
  validH bt -> valid (btExtend bt b) -> has_init_block bt ->
  has_init_block (btExtend bt b).
Proof.
move=>Vh V'; rewrite /btExtend/has_init_block=>Ib.
move: (btExtendV V')=>V; case: ifP=>X; last first.
by move: (find_some Ib)=>G; rewrite findUnR ?validPtUn ?X ?V //= G Ib.
case: ifP=>//=.
case: (um_eta X)=>v [F _].
rewrite F=>/eqP; move: (Vh _ _ F)=>H Neq.
contradict V'; rewrite/btExtend X; case: ifP.
by rewrite F=>/eqP [] E; subst v.
by rewrite valid_undef.
Qed.

Lemma btExtendIB_fold bt bs :
  validH bt -> valid (foldl btExtend bt bs) -> has_init_block bt ->
  has_init_block (foldl btExtend bt bs).
Proof.
move=>Vh V'; rewrite/has_init_block=>iB.
elim/last_ind: bs V'=>[|xs x Hi]; first done.
rewrite -cats1 foldl_cat /= {1}/btExtend; case: ifP.
- case: ifP; last by rewrite valid_undef.
  by move=>F D V; rewrite{1}/btExtend D F; apply Hi.
move=>Nd; rewrite validPtUn Nd /==>/andP[V _].
rewrite{1}/btExtend Nd findUnR ?validPtUn ?V ?Nd //=.
by move: (find_some (Hi V)) (Hi V)=>-> ->.
Qed.

Lemma in_ext bt b : valid (btExtend bt b) -> validH bt -> b ∈ btExtend bt b.
Proof.
move=>V' Vh; rewrite/btHasBlock/btExtend;
move: (btExtendV V')=>V; case: ifP=>//=; last first.
- rewrite domUn inE ?validPtUn ?V //==>D; rewrite D domPt inE/=.
  apply/andP; split.
  by apply/orP; left.
  by rewrite findUnL ?validPtUn ?V ?D //; rewrite domPt inE /=;
      case: ifP=>/eqP//= _; rewrite findPt /=.
move=>D; case: ifP.
by rewrite D=>/eqP ->; apply /andP; split=>//=.
case: (um_eta D)=>b' [] F' _; move: (Vh _ _ F')=>H F.
rewrite F' in F; contradict V'.
rewrite/btExtend D; case: ifP; last by rewrite valid_undef.
by rewrite F' F.
Qed.

Lemma btExtend_dom bt b :
  valid (btExtend bt b) -> {subset dom bt <= dom (btExtend bt b)}.
Proof.
move=>V' z; rewrite/btExtend; case:ifP=>C//=D.
case: ifP=>//= F.
by contradict V'; rewrite/btExtend C F valid_undef.
move: (btExtendV V')=>V.
by rewrite domUn inE andbC/= validPtUn/= V D/= C orbC.
Qed.

Lemma btExtend_dom_fold bt bs :
  valid (foldl btExtend bt bs) -> {subset dom bt <= dom (foldl btExtend bt bs)}.
Proof.
move=>V z; elim/last_ind: bs V=>[|xs x Hi]=>//.
move=>V'; move: (btExtendV_fold1 V')=>V D; specialize (Hi V D).
rewrite -cats1 foldl_cat /=; apply btExtend_dom=>//=.
by move: V'; rewrite -cats1 foldl_cat /=.
Qed.

Lemma btExtend_find bt z h b :
  valid (btExtend bt z) ->
  h \in dom bt ->
  find h (btExtend bt z) = Some b ->
  find h bt = Some b.
Proof.
move=>V' D; move: (btExtendV V')=>V.
rewrite/btExtend; case:ifP=>C.
case: ifP=>//=C'; first by rewrite find_undef.
rewrite findUnR ?validPtUn ?V ?C //; case: ifP=>//=.
by rewrite D.
Qed.

Lemma btExtend_find_fold bt h b bs :
  valid (foldl btExtend bt bs) ->
  h \in dom bt ->
  find h (foldl btExtend bt bs) = Some b ->
  find h bt = Some b.
Proof.
move=>V' D.
elim/last_ind: bs V'=>[|xs x Hi]=>//.
move=>V'; move: (btExtendV_fold1 V')=>V; move: V'.
rewrite -cats1 foldl_cat /= =>X.
specialize (Hi V); rewrite{1}/btExtend.
case: ifP.
case: ifP; last by rewrite find_undef.
by move=>_ _ ; apply Hi.
move=>Nd; rewrite findUnR ?validPtUn ?Nd ?V //.
case: ifP; first by move=>_; apply Hi.
move=>Nd'; rewrite findPt2 //=; case: ifP=>//=.
by move: (btExtend_dom_fold V D); rewrite Nd'.
Qed.

Lemma btExtend_fold_in_either bt xs b :
  b ∈ (foldl btExtend bt xs) ->
  b ∈ bt \/ b \in xs.
Proof.
elim/last_ind: xs=>[|xs x H]; first by left.
rewrite -cats1 foldl_cat //= {1}/btExtend.
case: ifP; last first.
- move=>D; rewrite/btHasBlock=>/andP [].
  rewrite domPtUn inE=>/andP[]Z/orP; case.
  * move/eqP=>Hh; rewrite Hh findPtUn; last by rewrite -Hh.
    move/eqP=>[]E; subst x; right.
    by rewrite mem_cat inE eq_refl Bool.orb_true_r.
  move=>A; rewrite findPtUn2 ?Z //=; case: ifP.
  by move=>_ /eqP[]->; right; rewrite mem_cat inE eq_refl Bool.orb_true_r.
  move=>_ B; have X: (b ∈ foldl btExtend bt xs) by rewrite/btHasBlock A B.
  move: (H X); case; first by rewrite/btHasBlock=>->; left.
  by move=>M; right; rewrite mem_cat M Bool.orb_true_l.
case: ifP.
move=>_ _ M; case: (H M); first by left.
by move=>X; right; rewrite mem_cat X Bool.orb_true_l.
by move=> _ _; rewrite/btHasBlock dom_undef in_nil Bool.andb_false_l.
Qed.

Lemma btExtend_in_either bt b b' :
  b ∈ btExtend bt b' -> b ∈ bt \/ b == b'.
Proof.
move=>X0; have X: (b ∈ (foldl btExtend bt [:: b'])) by [].
case: (btExtend_fold_in_either X); first by left.
by rewrite inE=>->; right.
Qed.

Lemma btExtend_fold_in bt xs b :
  valid (foldl btExtend bt xs) -> b ∈ bt \/ b \in xs ->
  b ∈ (foldl btExtend bt xs).
Proof.
elim/last_ind: xs=>[|xs x H]; first by move=>_; case=>//=.
move=>V'; move: (btExtendV_fold1 V')=>V; specialize (H V).
rewrite -cats1 foldl_cat //= {1}/btExtend.
case: ifP; last first.
- move=>D; case.
  * move=>Hv; have X: (b ∈ bt \/ b \in xs) by left.
    move: (H X); rewrite/btHasBlock=>/andP[] A B;
    rewrite domPtUn inE validPtUn V D A Bool.orb_true_r //=;
    (rewrite findPtUn2; last by rewrite validPtUn V D);
    case: ifP=>//=; by move/eqP=>E; move: D A; rewrite E=>->.

  * rewrite mem_cat inE=>/orP; case=>Hv.
    have X: (b ∈ bt \/ b \in xs) by right.
    move: (H X); rewrite/btHasBlock=>/andP[] A B;
    rewrite domPtUn inE validPtUn V D A Bool.orb_true_r //=;
    (rewrite findPtUn2; last by rewrite validPtUn V D);
    case: ifP=>//=; by move/eqP=>E; move: D A; rewrite E=>->.

  * by move/eqP in Hv; rewrite/btHasBlock domPtUn Hv inE eq_refl D;
    rewrite validPtUn V D findPtUn ?validPtUn ?V ?D //=.
case:ifP.
* move=>F D; case=>Hv.
  by (have X: (b ∈ bt \/ b \in xs) by left); move: (H X).
  move: Hv; rewrite mem_cat inE=>/orP; case=>Hv.
  by (have X: (b ∈ bt \/ b \in xs) by right); move: (H X).
  by move/eqP in Hv; subst x; rewrite/btHasBlock D F.
move=>F D; contradict V'.
by rewrite -cats1 foldl_cat //= {1}/btExtend D F valid_undef.
Qed.

Lemma btExtend_idemp bt b :
  valid (btExtend bt b) -> btExtend bt b = btExtend (btExtend bt b) b.
Proof.
move=>V'; move: (btExtendV V')=>V; rewrite{2}/btExtend; case: ifP.
case: ifP=>//=.
move=>X; rewrite{1}/btExtend; case: ifP=>D.
case: ifP=>F; last by rewrite dom_undef.
by move=>_; contradict X; rewrite/btExtend D F F.
by contradict X; rewrite/btExtend D; rewrite findPtUn ?validPtUn ?V ?D //= eq_refl.
move=>X; contradict X.
rewrite/btExtend; case: ifP=>D.
case: ifP=>F; first by rewrite D.
by contradict V'; rewrite/btExtend D F valid_undef.
by rewrite domPtUn inE validPtUn V D //= eq_refl.
Qed.

(* Just a reformulation *)
Lemma btExtend_preserve (bt : BlockTree) ob b :
  valid (btExtend bt b) ->
  ob ∈ bt -> ob ∈ btExtend bt b.
Proof.
move=>V'; move: (btExtendV V')=>V; rewrite/btHasBlock=>/andP [H0 H1].
rewrite/btExtend; case: ifP=>D.
- case: ifP=>F.
  by rewrite H0 H1.
  by contradict V'; rewrite/btExtend D F valid_undef.
have Vu: (valid (# b \\-> b \+ bt)) by rewrite validPtUn V D.
rewrite findUnR // H0 H1 domUn inE Vu H0 /=.
by apply/andP; split=>//=; apply/orP; right.
Qed.

Lemma btExtend_withDup_noEffect (bt : BlockTree) b:
  b ∈ bt -> bt = (btExtend bt b).
Proof. by rewrite/btHasBlock/btExtend=>/andP[]->->. Qed.

(* There must be a better way to prove this. *)
Lemma btExtend_comm bt b1 b2 :
  valid (btExtend (btExtend bt b1) b2) ->
  btExtend (btExtend bt b1) b2 = btExtend (btExtend bt b2) b1.
Proof.
move=>V2; move: (btExtendV V2)=>V1; move: (btExtendV V1)=>V0.
have V1': valid (btExtend bt b2).
rewrite/btExtend; case: ifP.
- case: ifP=>//= F D.
  contradict V2; rewrite{2}/btExtend; case: ifP.
  case: ifP=>_ _; rewrite/btExtend.
    by rewrite D F valid_undef.
    by rewrite dom_undef validPtUn //= dom_undef valid_undef //=.
  move=>Nd;
  by rewrite/btExtend domPtUn validPtUn inE Nd V0 D Bool.orb_true_r //=;
     rewrite findUnR ?validPtUn ?V0 ?Nd //= D F valid_undef.
by move=>Nd; rewrite validPtUn V0 Nd.
(* Now have V1' *)
case A: (b1 ∈ bt).
- move/andP: A=>[A0 A1].
  rewrite ![btExtend _ b1]/btExtend A0 A1 (btExtend_dom V1' A0).
  case: ifP=>//=; rewrite{1}/btExtend; case: ifP.
  case: ifP; first by rewrite A1.
  by move=>F D; contradict V1'; rewrite/btExtend D F valid_undef.
  by move=>Nd; move: V1'; rewrite{1}/btExtend Nd=>V;
     rewrite findUnR ?V1' //= A0 A1.
case B: (b2 ∈ bt).
- move/andP: B=>[B0 B1].
  rewrite ![btExtend _ b2]/btExtend B0 (btExtend_dom V1 B0).
  case: ifP; first by rewrite B1.
  rewrite{1}/btExtend; move/nandP: A=>[A0|A1].
  case: ifP; first by move=>D; rewrite D in A0.
    by clear A0; move=>A0; rewrite findUnR ?validPtUn ?V0 ?A0 //= B0 B1.
  rewrite B1; case: ifP.
  case: ifP; first by move/eqP=>F; rewrite F in A1; move/eqP: A1.
    by clear A1; move=>A1 A0 _; rewrite/btExtend A0 A1.
   by move=>Nd; rewrite findUnR ?validPtUn ?V0 ?A0 ?Nd //= B0 B1.
move/nandP: A=>[A0|A1]; move/nandP: B=>[B0|B1].
- have VPt1: (forall a, valid (# b1 \\-> a \+ bt)). by move=>a; rewrite validPtUn V0 A0.
  apply Bool.negb_true_iff in A0; apply Bool.negb_true_iff in B0.
  rewrite/btExtend A0 B0; case: ifP.
  + rewrite domPtUn VPt1 inE B0 //= =>/orP [] //==>/eqP H.
    rewrite -H findUnR //= A0 domPtUn inE eq_refl VPt1 A0 findUnR //= A0 !findPt /=.
    case: ifP; rewrite eq_sym=>/eqP; case: ifP=>/eqP=>//=.
    by case=>->.
  have VPt2: (forall a, valid (# b2 \\-> a \+ bt)). by move=>a; rewrite validPtUn V0 B0.
  move=>X; have H: ((# b1 == # b2) = false)
   by move: X; rewrite domPtUn inE VPt1 B0 //==>/norP [/eqP H _]; apply/eqP.
  rewrite findUnR //= A0 domPtUn inE VPt2 A0 findPt2 eq_sym H //=.
  by rewrite (joinC (#b1 \\-> _)) (joinC (#b2 \\-> _));
    rewrite (joinC (#b2 \\-> _)) joinA (joinC bt).
- have VPt1: (forall a, valid (# b1 \\-> a \+ bt)). by move=>a; rewrite validPtUn V0 A0.
  apply Bool.negb_true_iff in A0;
  rewrite/btExtend A0.
  rewrite domPtUn VPt1 inE //=; case: ifP.
  + move=>/orP [].
    by move/eqP=>H; rewrite -H findUnR //= A0 findPt domUn VPt1 !inE domPt A0 inE eq_refl //=;
       rewrite findUnR //= A0 findPt //= eq_sym; case: ifP=>//= /eqP[]->.
    move=>D; rewrite findUnR //= D; case: ifP.
      by move/eqP=>E; rewrite E in B1; move/eqP: B1.
      by rewrite dom_undef //= join_undefR.
  move/norP=>[Nh Nd]; case: ifP; case: ifP.
  case: ifP; do? by move=>_ D; rewrite D in Nd.
  by rewrite domPtUn inE A0=>Nd' /andP [] VPt2 /orP []=>//=;
     move/eqP=>H; rewrite H in Nh; move/eqP: Nh.
  by move=>D; rewrite D in Nd.
  move=>_ _;
  by rewrite (joinC (#b1 \\-> _)) (joinC (#b2 \\-> _));
    rewrite (joinC (#b2 \\-> _)) joinA (joinC bt).
- have VPt2: (forall a, valid (# b2 \\-> a \+ bt)). by move=>a; rewrite validPtUn V0 B0.
  apply Bool.negb_true_iff in B0.
  rewrite/btExtend B0 domPtUn VPt2 inE //=.
  case: ifP; case: ifP; case: ifP;
  do? by [
    move/eqP=>A; rewrite A in A1; move/eqP: A1 |
    rewrite dom_undef
  ]. case: ifP.
  move=>/orP [] //= /eqP H; rewrite H findUnL; last by rewrite -H; apply VPt2.
  rewrite domPt inE eq_refl //= findUnR; last by rewrite -H; apply VPt2.
  move=>F ->; rewrite findPt //=; case: ifP=>/eqP; first by case=>E; subst b2.
  by move: F; rewrite findPt //= eq_sym=>/eqP.
  by move/norP=>[]Nh _ F Nd;
     rewrite domPtUn inE B0 //==>/andP [] _ /orP[]=>//= /eqP H;
     rewrite H in Nh; move/eqP: Nh.
  move=>X Y; rewrite domPtUn inE B0=>/andP [] _ /orP []=>//=/eqP H.
  rewrite -H eq_refl //= findUnL; last by rewrite H; apply VPt2.
  rewrite domPt inE eq_refl //= findPt //=; case: ifP=>//=.
  move/eqP=>[E]; subst b2; contradict X.
  by rewrite findUnR ?validPtUn ?V0 ?B0 //= findPt //==>/eqP.
  move=>_ D; rewrite findUnR ?VPt2 //= D -(Bool.if_negb _ (find (# b1) bt == Some b1) _) A1.
  case: ifP=>_ _; first by rewrite join_undefR.
  have X: (# b1 \\-> b1 \+ bt = um_undef) by
    apply invalidE; rewrite validPtUn V0 D.
  by rewrite joinA (joinC (#b1 \\-> _)) -X joinA.
  by move/orP=>[] //= /eqP H; rewrite H=>D; rewrite H in VPt2;
     rewrite domPtUn inE D eq_refl VPt2.
  by rewrite (joinC (#b1 \\-> _)) (joinC (#b2 \\-> _));
    rewrite (joinC (#b2 \\-> _)) joinA (joinC bt).
(* Nastiest case - 16 subcases to be handled one-by-one *)
rewrite/btExtend; case: ifP; case: ifP; case: ifP; case: ifP.
by move/eqP=>B; rewrite B in B1; move/eqP: B1.
by move=>_ /eqP A; rewrite A in A1; move/eqP: A1.
by rewrite dom_undef.
by rewrite dom_undef.
case: ifP; case: ifP.
  by move/eqP=>B; rewrite B in B1; move/eqP: B1.
  by rewrite dom_undef.
  move=>_ D; rewrite domPtUn inE=>/andP[] _ /orP[].
  by move/eqP=>H F Nd; move: F; rewrite H findUnL ?validPtUn ?V0 ?Nd //=;
    rewrite domPt inE eq_refl findPt //==>/eqP[]->.
  by move=>->.
  move=>Nf Nd2 _ F Nd1. rewrite domPtUn inE Nd2 //==>/andP[]_ /orP[]=>//= /eqP H.
  move: F; rewrite -H findUnL ?validPtUn ?V0 ?Nd1 //= domPt inE eq_refl //= findPt //=.
  move/eqP=>[]E; subst b2; contradict Nf.
  by rewrite findUnL ?validPtUn ?V0 ?Nd1 //= domPt inE eq_refl //= findPt //==>/eqP [].
case: ifP.
  case: ifP=>//=.
  move=>_ D; contradict V1';
  rewrite/btExtend D; case: ifP=>/eqP E;
    by [rewrite E in B1; move/eqP: B1|rewrite valid_undef].
  move=>D A F B; rewrite domPtUn inE D=>/andP []_/orP[] //= /eqP H; rewrite H.
  by contradict A; rewrite domPtUn inE eq_sym H eq_refl D validPtUn V0 D.
case: ifP; case: ifP=>//=.
  by move/eqP=>B; rewrite B in B1; move/eqP: B1.
  by rewrite dom_undef.
  move=>F D _ Nf D'; move: F Nf; rewrite !findUnL ?validPtUn ?V0 ?D ?D' //=.
  rewrite !domPt !inE //= inE (eq_sym (#b2)); case: ifP.
  by move/eqP=>->; rewrite !findPt //==>/eqP []-> /eqP.
  by move=>_ /eqP F; move: (find_some F)=>Nd'; rewrite Nd' in D'.
case: ifP.
  case: ifP; first by move/eqP=> B; move/eqP: B1; rewrite B.
  by rewrite join_undefR.
  move=>D _ _ _. rewrite domUn inE D domPt //= inE=>/andP []_/orP[]//=.
  by move/eqP=><-; rewrite joinA pts_undef join_undefL.
by move=>_/eqP A; rewrite A in A1; move/eqP: A1.
by move=>_/eqP A; rewrite A in A1; move/eqP: A1.
case: ifP; case: ifP.
  by move/eqP=>B; rewrite B in B1; move/eqP: B1.
  by rewrite dom_undef.
  by move=>F D' _ _ D; move: F; rewrite findUnR ?validPtUn ?V0 ?D' //= D;
     move/eqP=>A; rewrite A in A1; move/eqP: A1.
  by rewrite join_undefR.
case: ifP.
  case: ifP; last by rewrite !join_undefR.
  by move/eqP=> B; rewrite B in B1; move/eqP: B1.
  rewrite join_undefR=>_ _ _ D _; rewrite joinA (joinC (#b1 \\-> _)).
  suff: ~~ valid(#b1 \\-> b1 \+ bt) by move/invalidE; rewrite -joinA=>->; rewrite join_undefR.
  by rewrite validPtUn V0 D.
by case: ifP; [move=>_ _ -> | rewrite dom_undef].
rewrite domPtUn inE=>_ /andP[]_/orP []; last by move=>->.
  by move/eqP=>-> D; rewrite domPtUn inE eq_refl //= validPtUn V0 D.
case: ifP.
  by move/eqP=>B; rewrite B in B1; move/eqP: B1.
  by move=>_D D' _; rewrite domPtUn validPtUn V0 inE D' //==>-> //= /norP[].
by move=>_ _ _ _; rewrite !joinA (joinC (#b2 \\-> _)).
Qed.

Definition no_collisions (bt : BlockTree) (xs : seq BType) :=
  valid bt /\
  forall a, a \in xs ->
    (forall b, b \in xs -> # a = # b -> a = b) /\
    (forall b, b ∈ bt -> # a = # b -> a = b).

Lemma btExtendV_valid_no_collisions bt xs :
  valid (foldl btExtend bt xs) -> no_collisions bt xs.
Proof.
elim/last_ind: xs=>[|xs x H0] //=.
- move=>V; move: (btExtendV_fold1 V)=>V1; specialize (H0 V1).
  move: H0; rewrite/no_collisions.
  move=>[] V0 N; split=>//=.
  move=>a; rewrite -cats1 mem_cat inE=>/orP; case; last first.
  * move/eqP=>E; subst a; split.
    move=>b; rewrite mem_cat inE=>/orP; case; last first.
    by rewrite eq_sym=>/eqP.
    by apply (btExtendV_fold_dup V).
    move=>b; rewrite/btHasBlock=>/andP[D F] Hh.
    move: V; rewrite -cats1 foldl_cat //= {1}/btExtend.
    move: (btExtend_dom_fold V1 D)=>D'; rewrite Hh D'.
    case: ifP; last by rewrite valid_undef.
    move=>F' _; move/eqP in F'.
    by move: (btExtend_find_fold V1 D F'); move/eqP: F=>-> []->.
  move=>X; specialize (N a X); case: N=>N0 N1; split=>b; last by apply N1.
  rewrite mem_cat inE=>/orP; case; first by apply N0.
  move/eqP=>E; subst b=>/eqP Hh; rewrite eq_sym in Hh; move/eqP in Hh.
  by move: (btExtendV_fold_dup V X Hh)=>->.
Qed.

Lemma btExtendV_no_collisions_valid bt xs :
  validH bt -> no_collisions bt xs -> valid (foldl btExtend bt xs).
Proof.
elim/last_ind: xs=>[|xs x H1] //=.
by rewrite/no_collisions=>_; case.
rewrite/no_collisions=>Vh; case=>V N.
have N0: no_collisions bt xs.
rewrite/no_collisions; split=>//=.
  move=>a X; have X0: a \in rcons xs x
    by rewrite mem_rcons inE X Bool.orb_true_r.
  specialize (N a X0); move: N=>[]N0 N1; split=>b; last by apply N1.
  move=>X1; have X2: b \in rcons xs x.
    by rewrite mem_rcons inE X1 Bool.orb_true_r.
  by apply N0.
specialize (H1 Vh N0); rewrite -cats1 foldl_cat //= {1}/btExtend.
case: ifP; last by move=>D; rewrite validPtUn H1 D.
case: ifP=>//= F D; contradict H1.
(* Hmm *)
have X: (x \in rcons xs x) by rewrite mem_rcons mem_head.
specialize (N x X); move: N0=>N'; case: N=>N0 N1.
move: (um_eta D)=>[b] [F'] zz; rewrite F' in F.
specialize (N0 b); specialize (N1 b).
move: (btExtendH_fold Vh (dom_valid D) F')=>Hh.
rewrite Hh in D F'; have H: b ∈ (foldl btExtend bt xs).
  by rewrite/btHasBlock D F' eq_refl.
case Z: (x == b); first by move/eqP: Z F=>->; rewrite eq_refl.
case: (btExtend_fold_in_either H).
by move=>Q; move: (N1 Q Hh) Z=>->; rewrite eq_refl.
move=>R; have Q: (b \in rcons xs x)
  by rewrite -cats1 mem_cat inE R Bool.orb_true_l.
by move: (N0 Q Hh) Z=>->; rewrite eq_refl.
Qed.

Lemma btExtendV_fold_comm' bt xs ys :
  validH bt ->
  valid (foldl btExtend (foldl btExtend bt xs) ys) ->
  valid (foldl btExtend (foldl btExtend bt ys) xs).
Proof.
move=>Vh.
elim/last_ind: ys=>[|ys y V1]//= V.
move: (btExtendV_fold1 V)=>V0; specialize (V1 V0).
rewrite -foldl_cat; apply btExtendV_no_collisions_valid=>//=.
rewrite/no_collisions; split.
have X: (xs = [::] ++ xs) by [].
by move: V0; rewrite -foldl_cat X; move/btExtendV_fold/btExtendV_fold.
move: V; rewrite -foldl_cat; move/btExtendV_valid_no_collisions.
rewrite/no_collisions; case=>V H.
move=>a; rewrite mem_cat Bool.orb_comm=>X.
specialize (H a); rewrite mem_cat in H; specialize (H X).
case: H=>H0 H1; split=>//=.
move=>b; rewrite mem_cat Bool.orb_comm -mem_cat; apply H0.
Qed.

Lemma btExtendV_fold_comm bt xs ys :
  validH bt ->
  valid (foldl btExtend (foldl btExtend bt xs) ys) =
  valid (foldl btExtend (foldl btExtend bt ys) xs).
Proof.
move=>Vh.
have T: true by [].
have X: forall (a b : bool), a <-> b -> a = b.
by move=>a b []; case: a; case: b=>//= A B;
   [specialize (A T) | specialize (B T)].
by apply X; split; apply btExtendV_fold_comm'.
Qed.

Lemma btExtendV_fold' bt xs ys :
  validH bt-> valid (foldl btExtend bt (xs ++ ys)) -> valid (foldl btExtend bt ys).
Proof. by move=>Vh; rewrite foldl_cat btExtendV_fold_comm //= -foldl_cat=>/btExtendV_fold. Qed.

(**************************************************)
(** The chain computed following parent pointers **)
(**************************************************)

Function compute_chain_up_to (bound: BType) bt b {measure round b} : Blockchain :=
  if b ∈ bt then
    match find (qc_hash b) bt with
    | None => [::]
    | Some prev =>
      if prev == bound then [:: b] else
        if (round b <= round prev) then [::] else
          rcons (nosimpl (compute_chain_up_to bound (free (# b) bt) prev)) b
    end
  else [::].
Proof.
move=> bound bt b Hb prev Hprev Hgen.
move/negbT; rewrite leqNgt; move/negbNE=> Hbound.
by apply/ltP.
Qed.

Definition compute_chain bt b :=
  let: l := compute_chain_up_to GenesisBlock bt b in
  if parent GenesisBlock (head GenesisBlock l) then
    compute_chain_up_to GenesisBlock bt b
  else
    [::].

Lemma last_compute_chain_up_to (bound: BType) bt b:
  let: l := (compute_chain_up_to bound bt b) in
  last (head bound l) (behead l) = if l is [::] then bound else b.
Proof.
apply compute_chain_up_to_rec=>//=; move=> {bt b} bt b Hb prev Hprev.
case =>[|Hgenesis _] //; case =>[|] //.
move/negbT; rewrite leqNgt; move/negbNE=> Hround.
move=> _ _ _; set l:= (compute_chain_up_to bound (free (# b) bt) prev).
rewrite -(last_cons GenesisBlock) head_rcons -headI.
by rewrite last_rcons; case l=>//.
Qed.

Lemma compute_chain_up_to_is_chained (bound: BType) bt b:
  validH bt ->
  let: l := (compute_chain_up_to bound bt b) in
  path parent (head bound l) (behead l).
Proof.
apply compute_chain_up_to_rec=>//=; move=> {bt b} bt b Hb prev Hprev.
case =>[|Hgenesis _] //; case =>[|] //.
move/negbT; rewrite leqNgt; move/negbNE=> Hround.
move=> _ _; move: (last_compute_chain_up_to bound (free (#b) bt) prev).
set l:= (compute_chain_up_to bound (free (# b) bt) prev).
case H: l=> [| x xs] /= Hlast IH Hvalid //=.
rewrite rcons_path (IH (validH_free Hvalid)) andTb.
by rewrite /parent Hlast (Hvalid _ _ Hprev).
Qed.

Lemma compute_chain_is_chained bt b:
  validH bt ->
  chained (compute_chain bt b).
Proof.
rewrite /chained /compute_chain.
apply compute_chain_up_to_ind=> //=; move=> {bt b} bt b Hb prev Hprev; try by case (parent GenesisBlock GenesisBlock) => //=.
- by rewrite /parent; move/eqP=> HprevG Hvalid; rewrite (Hvalid _ _ Hprev) HprevG eq_refl /= -HprevG (Hvalid _ _ Hprev) eq_refl.
- case =>[|Hgen] _ //; case=> [|] //.
move/negbT; rewrite leqNgt; move/negbNE=> Hround.
move => _ _; move: (last_compute_chain_up_to GenesisBlock (free (#b) bt) prev).
set l:= (compute_chain_up_to GenesisBlock (free (# b) bt) prev).
case H: l=> [| x xs] /= Hlast //=.
- by case HGb: (parent GenesisBlock b) => //=; rewrite andbT.
- case HGx: (parent GenesisBlock x)=> /= IH Hvalid //=; rewrite rcons_path Hlast {3}/parent (Hvalid _ _ Hprev) eq_refl andbT.
by apply (IH (validH_free Hvalid)).
Qed.

Definition get_block (bt : BlockTree) k : BType :=
  if find k bt is Some b then b else GenesisBlock.
Definition all_blocks (bt : BlockTree) := [seq get_block bt k | k <- dom bt].
Definition all_chains bt := [seq compute_chain bt b | b <- all_blocks bt].

Definition chain b bseq:=
  path (fun b1 b2 => (parent b1 b2) && (round b2 == (round b1).+1)) b bseq.

Notation "chain [ :: x1 ; x2 ; .. ; xn ]" := (chain x1 ( x2 :: .. [:: xn] ..))
  (at level 0, format "chain [ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ).

Fixpoint three_slide (xs: seq BType) :=
  match xs with
  | x :: (y :: z :: ts as l) => (x, y , z) :: (three_slide l)
  | _ => [::]
  end.

Fixpoint highest_3_chain_aux (s: seq (BType * BType * BType)) n :=
  match s with
  | (b1, b2, b3) :: bs => if ((round b1).+1 == (round b2)) && ((round b2).+1 == (round b3)) then
                          (highest_3_chain_aux bs (round b3))
                        else
                          (highest_3_chain_aux bs n)
  | _ => n
  end.

Definition highest_3_chain (s: seq BType) :=
  highest_3_chain_aux (three_slide s) genesis_round.

Definition take_better_bc bc2 bc1 :=
  if ((highest_3_chain bc2) > (highest_3_chain bc1)) then bc2 else bc1.

Definition btChain bt : Blockchain :=
  foldr take_better_bc ([::]) (all_chains bt).


End Forests.
