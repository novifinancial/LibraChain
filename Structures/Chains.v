(****************************************************************************)
(* Copyright (c) Facebook, Inc. and its affiliates.                         *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License");          *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope seq_scope.
Section Prefixes.

  Variable T : eqType.

Implicit Type bc : seq T.

(* Strict version of the prefix *)
Definition is_strict_prefix bc bc':=
  exists b bc1, bc' = bc ++ (b :: bc1).

Lemma isp_mt bc : ~ is_strict_prefix bc [::].
Proof.    by case=>b[bc1]; case: bc. Qed.

(* The corresponding checker *)
Fixpoint sprefixb {T: eqType} (s1 s2 : seq T) :=
  if s2 is y :: s2' then
    if s1 is x :: s1' then (x == y) && (sprefixb s1' s2')
    else true
  else false.

Notation "'[' bc1 '<<<' bc2 ']'" := (sprefixb bc1 bc2).

Lemma sprefixP bc1 bc2:
  reflect (is_strict_prefix bc1 bc2) [bc1 <<< bc2].
Proof.
elim: bc2 bc1=>//=[|b2 bc2 Hi/=]bc1.
- case:bc1=>//=[|b1 bc1]; constructor 2=>//; apply: isp_mt.
case: bc1=>//[|b1 bc1]/=; first by constructor 1; exists b2, bc2.
case X: (b1 == b2)=>/=; last first.
- constructor 2=>[[p]][bc']; rewrite cat_cons; case=>Z; subst b2.
  by rewrite eqxx in X.
- move/eqP: X=>X; subst b2.
case: Hi=>H; [constructor 1|constructor 2].
- by case:H=>x[xs]->; exists x, xs; rewrite cat_cons.
case=>x[xs]; rewrite cat_cons; case=>Z; subst bc2; apply: H.
by exists x, xs.
Qed.

Lemma bc_spre_nrefl bc : [bc <<< bc] = false.
Proof.
by elim: bc=>[|x xs H] //=; rewrite eqxx H.
Qed.

(* Non-strict prefix *)
Fixpoint prefixb bc1 bc2 :=
  if bc2 is y :: bc2' then
    if bc1 is x :: bc1' then (x == y) && (prefixb bc1' bc2')
    else true
  else bc1 == [::].

Definition is_prefix bc bc' :=
  exists bc1, bc' = bc ++ bc1.

Notation "'[' bc1 '<<=' bc2 ']'" := (prefixb bc1 bc2).

Lemma prefixb0seq bc : [[::] <<= bc]. Proof. by case: bc. Qed.

Lemma prefixbseq0 bc: [bc <<= [::]] = (bc == [::]). Proof. by case bc. Qed.

Lemma bc_pre_refl bc : [bc <<= bc].
Proof.
by elim bc => [|x s IHs] //=; rewrite eqxx IHs.
Qed.

Lemma prefixb_belast bc1 b bc2: [bc1 <<= b :: bc2] = [bc1 <<= (belast b bc2)] || (bc1 == b :: bc2).
Proof.
move: bc1 b bc2; elim=> [b bc2|x s IH b]; first by rewrite 2!prefixb0seq.
elim; first by rewrite prefixbseq0 //= prefixbseq0 eqseq_cons.
by move => x' s' H; rewrite eqseq_cons //= (IH x' s') andb_orr.
Qed.

Lemma prefixP bc1 bc2:
  reflect (is_prefix bc1 bc2) [bc1 <<= bc2].
Proof.
move: bc2 bc1; elim => [|b2 bc2 IH/=] bc1.
- rewrite prefixbseq0 ; apply: (iffP eqP) => [->|] //=; first by exists [::].
  case => [s H]; move: (size_cat bc1 s); rewrite -{}H /=; move/eqP.
  by rewrite eq_sym addn_eq0; move /andP =>[H _]; move/nilP: H.
- move: bc1; case.
  - rewrite prefixb0seq //; apply/(iffP idP)=>//; exists (b2::bc2).
    by rewrite cat0s.
  - move => s l; apply/(iffP idP) => /= [|].
    - move/andP => [Heq]; move/(IH l) => [ss Hss]; exists ss.
      by move/eqP: Heq->; move:Hss ->; rewrite cat_cons.
    - move=> [ss]; rewrite cat_cons; move/eqP; rewrite eqseq_cons eq_sym.
      move/andP => [H H']; rewrite H /=; apply/(IH l).
      by exists ss; move/eqP: H'.
Qed.

Lemma sprefixbseq0 bc: [bc <<< [::]] = false.
Proof. by case bc =>// x s. Qed.

Lemma sprefixb0seq b bc: [[::] <<< b :: bc].
 Proof. by []. Qed.

Lemma sprefix_prefix_belast bc1 b bc2: [bc1 <<< b :: bc2] = [bc1 <<= (belast b bc2)].
Proof.
move: bc2 bc1 b ; elim=>[bc1 b |x s IH bc1 b] /=.
- rewrite prefixbseq0; case bc1 => //[b' s']/=.
  by rewrite (sprefixbseq0 s') andbF eq_sym; apply/negP.
-  case bc1 => [|b' s']; first by rewrite prefixb0seq sprefixb0seq.
   by rewrite //=; move: (IH s' x)->.
Qed.

Lemma bc_spre_trans bc1 bc2 bc3:
  [bc1 <<< bc2] -> [bc2 <<< bc3] -> [bc1 <<< bc3].
Proof.
move/sprefixP => [x][xs] ->; move/sprefixP => [x'][xs']->.
by apply/sprefixP; exists x; exists (xs ++ x' :: xs'); rewrite -catA.
Qed.

Lemma bc_spre_pre bc bc':
  [bc <<< bc'] -> [bc <<= bc'].
Proof. by move/sprefixP=>[] x [] xs=>->; apply/prefixP; exists (x :: xs). Qed.

Lemma bc_pre_spre bc bc':
  [bc <<= bc'] = [bc <<< bc'] || (bc == bc').
Proof.
case bc' => [|x' s']; first by rewrite prefixbseq0 sprefixbseq0.
by rewrite prefixb_belast sprefix_prefix_belast.
Qed.

Lemma bc_spre_irrefl bc1 bc2 :
  [bc1 <<< bc2] && [bc2  <<< bc1] = false.
Proof.
case H: [bc1 <<< bc2]=>//=; case  H': [bc2 <<< bc1] =>//=.
move: (@bc_spre_trans _ _ _ H H'); rewrite bc_spre_nrefl //.
Qed.

(* Decidable fork *)
Definition fork bc1 bc2 :=
  ~~([bc1 <<< bc2] || [bc2 <<< bc1] || (bc1 == bc2)).

Definition fork_rel bc1 bc2 :=
  ~ ((is_prefix bc1 bc2) \/ (is_prefix bc2 bc1)).

Lemma forkP bc1 bc2 :
  reflect (fork_rel bc1 bc2) (fork bc1 bc2).
Proof.
apply/introP; rewrite /fork_rel /fork.
- rewrite orbC; move/norP => [H]; move/norP => [H1 H2].
  case; move/prefixP; rewrite bc_pre_spre; apply/negPn;
  apply/norP; rewrite ?H1 ?H2 ?H; rewrite eq_sym in H; rewrite ?H=> //.
  by move/negPn; move/orP =>[|H]; first move/orP=> [H|H];
  case; [left|right|left]; apply/prefixP; rewrite bc_pre_spre H // orbC //.
Qed.

Lemma bc_fork_neq bc bc' :
  fork bc bc' -> bc != bc'.
Proof.
  move=>H; apply/negbT/negP=>Z; move/eqP:Z=>Z; subst bc'.
by move: H; rewrite /fork eqxx orbC //=.
Qed.

Inductive bc_rel bc bc' : bool-> bool-> bool-> bool-> Set :=
| CmpBcEq of bc == bc' : bc_rel bc bc' true false false false
| CmpBcFork of fork bc bc' : bc_rel bc bc' false true false false
| CmpBcPre12 of sprefixb bc bc' : bc_rel bc bc' false false true false
| CmpBcPre21 of sprefixb bc' bc: bc_rel bc bc' false false false true.

Lemma bc_relP bc bc' :
  bc_rel bc bc' (bc == bc') (fork bc bc') (sprefixb bc bc') (sprefixb bc' bc).
Proof.
case Eq: (bc == bc'); case F: (fork bc bc');
case S12: [bc <<< bc']; case S21: [bc' <<< bc];
try by [constructor|
        contradict Eq; move: (bc_fork_neq F)=>/eqP=>A B; apply A; move/eqP in B |
        contradict F; rewrite /fork Eq S12 S21 //=|
          by move: (bc_spre_irrefl bc bc'); rewrite S12 S21 //=
].
- by move/idP: S12; move/eqP: Eq=>->; rewrite bc_spre_nrefl.
- by move/idP: S21; move/eqP: Eq=>->; rewrite bc_spre_nrefl.
Qed.

End Prefixes.
