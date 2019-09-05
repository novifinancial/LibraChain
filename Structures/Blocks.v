From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From LibraChain
Require Import SeqFacts Chains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BlockType.


Variables (Hash NodeTime : ordType) (Command VProof BlockSource : eqType).

Record Block :=
  mkB {
    (* Parent's hash pointer *)
    prevHash : Hash;
    (* Payload *)
    txs : seq Command;
    (* UnixTime (see liveness) *)
    time: NodeTime;
    round: nat;
    (* Parent's QC information *)
    proof : VProof;
    source: BlockSource;
  }.

Definition eq_block (b b' : Block) :=
  match b, b' with
  | mkB ph txs ti rd pf sc, mkB ph' txs' ti' rd' pf' sc' =>
    [&& ph == ph', txs == txs', ti == ti', rd == rd', pf == pf' & sc == sc']
  end.

Lemma eq_blockP : Equality.axiom eq_block.
Proof.
move => b b'.
apply: (iffP idP) => [|<-].
- case b => ph txs ti rd pf bs;
  case b'=> ph' txs' ti' rd' pf' bs'; rewrite /eq_block/=.
  do? [case /andP; move /eqP ->]; by move /eqP ->.
- by case b => ph txs ti rd pf bs //=; do? rewrite eqxx.
Qed.

Canonical Block_eqMixin :=
  Eval hnf in EqMixin eq_blockP.
Canonical Block_eqType :=
  Eval hnf in EqType Block Block_eqMixin.

End BlockType.
