From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype ssrfun seq path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From LibraChain
Require Import SeqFacts Chains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BlockSource.

Variables (Address: finType) (VProof: eqType).

Record BlockSource := mkBS {
                          author: Address;
                          signature: VProof;
                        }.

Definition eq_block_source (b b' : BlockSource) :=
  match b, b' with
  | mkBS auth sig, mkBS auth' sig' =>
    (auth == auth') && (sig == sig')
  end.

Lemma eq_block_sourceP: Equality.axiom eq_block_source.
Proof.
move => bs bs'.
apply (iffP idP)=> [|->]; last by case bs'=>a' s' //=; rewrite ?eqxx //.
case bs=> a s; case bs'=> a' s'; [case/andP; move/eqP ->].
by move/eqP->.
Qed.


Canonical BlockSource_eqMixin :=
  Eval hnf in EqMixin eq_block_sourceP.
Canonical BlockSource_eqType :=
  Eval hnf in EqType BlockSource BlockSource_eqMixin.

End BlockSource.

Section QuorumCert.

Variable Hash: ordType.
Variable VProof: eqType.

Record QuorumCert := mkQC {
                      block_hash: Hash;
                      executed_hash: Hash;
                      block_round: nat;
                      parent_block_hash: Hash;
                      parent_block_round: nat;
                      grandparent_block_hash: Hash;
                      grandparent_block_round: nat;
                      votes: seq VProof;
                    }.

Definition eq_quorum_cert (qc qc': QuorumCert) :=
  match qc, qc' with
  | mkQC bh eh br pbh pbr gpbh gpbr v, mkQC bh' eh' br' pbh' pbr' gpbh' gpbr' v' =>
    [&& bh == bh', eh == eh', br == br', pbh == pbh', pbr == pbr', gpbh == gpbh', gpbr == gpbr' & v == v']
  end.

Lemma eq_qcP: Equality.axiom eq_quorum_cert.
 Proof.
move => qc qc'; apply: (iffP idP) => [| ->].
- case qc=> bh eh br ph pr gph gpr v;
  case qc'=> bh' eh' br' ph' pr' gph' gpr' v' /=; do? [case/andP; move/eqP ->]; by move/eqP ->.
- by case qc'=> bh' eh' br' ph' pr' gph' gpr' v' //=; do? rewrite eqxx.
Qed.

Canonical QC_eqMixin := Eval hnf in EqMixin eq_qcP.
Canonical QC_eqType := Eval hnf in EqType QuorumCert QC_eqMixin.

End QuorumCert.

Section BlockType.

Variables (Hash NodeTime : ordType) (Command VProof : eqType) (Address: finType).

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
    proof : QuorumCert Hash VProof;
    source: BlockSource Address VProof;
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
