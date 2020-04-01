From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq choice fintype finset.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.

Set Implicit Arguments.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

(***************************************************)
(*        Some useful facts about sets             *)
(***************************************************)

Section BFTFacts.

Variable T: choiceType.

Variable validators: seq T.
Hypothesis Huniq_val: uniq validators.

(* Validators is the small subType defined by their enumeration validators.*)
Definition Validators := seq_sub validators.

(* In this context, honest is a predicate on validators.*)
Variable honest: pred Validators.
Variable f: nat.

Hypothesis BFT:
  (#|[set x : Validators|honest x]| >= (2*f).+1) &&
  (size validators == (3*f).+1).

Lemma cards_dishonest:
  #|~: [set x| honest x]| <= f.
Proof.
move: (cardsCs [set x|  honest x]); move/andP: BFT=> [Hhon Hsv].
move: (Hsv); rewrite (card_seq_sub Huniq_val) /=; move/eqP=>-> Hdh.
move: (Hhon); rewrite {}Hdh ltn_subRL.
have: 2 * f < (3 * f).+1; first by rewrite ltnS leq_mul2r ltnS (ltn_trans (ltnSn _) (ltnSn _)) orbT.
move/(@ltn_sub2r (2*f) _ _ )=>H; move/H.
rewrite {H}addnK -[(_ * f).+1]addn1 -addnBAC; last by rewrite leq_mul2r ltnS (ltn_trans (ltnSn _) (ltnSn _)) orbT.
by rewrite -mulnBl subSnn mul1n addn1 ltnS.
Qed.

Lemma card_S2f_gt (C: {set Validators}):
  #|C| == (2*f).+1 ->
  #|C :&: [set x | honest x]| >= f.+1.
Proof.
move=> Hc; rewrite (cardsCs (_ :&: [set x|honest x])).
move/andP: BFT=> [Hhon /eqP Hsv].
rewrite (card_seq_sub Huniq_val) Hsv setCI.
have Hi: f < (3 * f).+1 - (2 * f).
- rewrite -[(3*f).+1]addn1 mulnC mulnS mulnC -addnA.
  by rewrite [_ + 1]addnC addnA addn1 addnK.
have H: #|(~: C) :|: ~: [set x | honest x]| <= 2*f.
- apply: (leq_trans (leq_card_setU (~:C) (~: [set x|honest x]))).
  rewrite mulnC mulnS muln1; move: cards_dishonest.
  rewrite -(leq_add2l #|~: C|); move/leq_trans; apply.
  rewrite leq_add2r cardsCs (card_seq_sub Huniq_val) Hsv.
  rewrite setCK (eqP Hc) mulnC mulnS -addn1 mulnC -addnA addn1.
  by rewrite addnK leqnn.
apply: (leq_trans Hi).
by apply: (leq_sub _ H).
Qed.

Lemma intersection (A B: {set Validators}):
  (#|A| == (2*f).+1) && (#|B| == (2*f).+1) ->
  #|[set x in A:&:B | honest x]| > 0.
Proof.
move/andP=>[HA HB]; move/andP: BFT=> [Hhon Hsv].
have H: #|A:&:B| >= f+1.
- rewrite cardsI (eqP HA) (eqP HB).
  apply: (leq_trans _ (leq_sub2l _ (subset_leq_card (subsetT (A:|:B))))).
  rewrite cardsT (card_seq_sub Huniq_val) (eqP Hsv).
  have I: (2 * f).+1 + (2 * f).+1 = f.+1 + (3*f).+1.
  - rewrite [3*_]mulnC mulnS [_*2]mulnC -addnS addnA [f.+1 + f]addSnnS.
    by rewrite [f+f.+1]addnS -{4}[f]muln1 -mulnS [f*2]mulnC.
  by rewrite I addnK addn1.
move: H; rewrite -{1}[A:&:B]setIT -{1}(setUCr [set x|honest x]).
rewrite setIUr cardsU setICA -!setIA setICr !setI0 cards0 subn0 2!setIA.
move/subset_leq_card: (subsetIr (A :&: B) (~: [set x| honest x])).
rewrite -(leq_add2l #|A :&: B :&: [set x|honest x]|)=> H2 H1.
move: {H1 H2}(leq_trans H1 H2); rewrite [_ + #|~: _|]addnC -leq_subLR=>H.
move: (leq_trans (leq_sub2l (f+1) cards_dishonest) H).
by rewrite addnC addnK setIdE.
Qed.

Lemma intersectionP (A B: {set Validators}):
  (#|A| == (2*f).+1) && (#|B| == (2*f).+1) ->
  exists x, x \in [set x in A:&:B|honest x].
Proof.
by move=> H; apply/set0Pn; rewrite -card_gt0 (intersection H).
Qed.

End BFTFacts.
