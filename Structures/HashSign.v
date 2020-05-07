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

Module Hash.

(* We start with hashable types, which are just codomains of a canonical *)
(* injection into an ordType. *)

Section RawMixin.

(* Surprisingly, we do not need constraints on T: the mixin gives us an eqType *)
(* structure on T, through being precisely eqType's InjEqMixin*)
Variable T: Type.

(* Note the definition of H as an ordtype allows usign them as union_map
keys. *)

Record mixin_of (H: Type) := Mixin {
  hash: T -> H;
  _ : injective hash
}.

End RawMixin.

(* the class takes a naked type H and returns all the *)
(* relatex mixins; the inherited ones and the added ones *)
Section ClassDef.

Variable T: Type.

Record class_of (H: Type) := Class {
  base: Ordered.class_of H;
  mixin: mixin_of T (Ordered.Pack base)
}.

Local Coercion base : class_of >-> Ordered.class_of.

Structure type (phH: phant T) := Pack {
  sort : Type;
  _ : class_of sort
}.

Local Coercion sort: type >-> Sortclass.

Variables (phT: phant T) (H: ordType) (cH: type phT).
Definition class := let: Pack _ c as cH' := cH return class_of cH' in c.
Definition clone c of phant_id class c := @Pack phT H c.
Let xH := let: @Pack _ H _ := cH in H.
Definition xclass := (class: class_of xH).

(* produce a hash type out of the inherited mixins *)
(* equalize m0 and m by means of a phantom; will be exploited *)
(* further down in the definition of HashType *)
Definition pack b0 (m0 : mixin_of T (@Ordered.Pack H b0)) :=
  fun bT b & phant_id (Ordered.class bT) b =>
  fun    m & phant_id m0 m => Pack phT (@Class H b m).

(* FCSL bug?: not declaring its mixin/base coercions *)
Local Coercion Ordered.base : Ordered.class_of >-> Equality.class_of.

Definition eqType := Eval hnf in @Equality.Pack xH xclass.
Definition ordType := Eval hnf in @Ordered.Pack xH xclass.
End ClassDef.

Module Import Exports.
(* FCSL bug fixing*)
Coercion Ordered.base : Ordered.class_of >-> Equality.class_of.

(* Those are the liens analogous to the ones missing in FCSL *)
Coercion base : class_of >-> Ordered.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Notation hashType T := (type (Phant T)).
Notation HashType T H m := (@pack _ (Phant T) H _ m _ _ id _ id).
Notation HashMixin := Mixin.
Notation "[ 'hashType' T 'of' H 'for' cH ]" := (@clone _ (Phant T) H cH _ idfun)
  (at level 0, format "[ 'hashType' T 'of' H 'for' cH ]") : form_scope.
Notation "[ 'hashType' T 'of' H ]" := (@clone _ (Phant T) H _ _ id)
  (at level 0, format "[ 'hashType' T 'of'  H ]") : form_scope.
End Exports.

End Hash.

Export Hash.Exports.

Definition hash_op (T: Type) (H: hashType T) :=
  Hash.hash (Hash.class H).

Lemma hash_inj (T: Type) (H: hashType T) : injective (@hash_op T H).
Proof. by case: H=> ?[b []]. Qed.

Declare Scope hash_scope.
Delimit Scope hash_scope with H.
Open Scope hash_scope.

(*******************************************************************************)
(* The signatures in our case are really tuples composed of a public key and a *)
(* signature. The public key injectively maps to an address, and the signature *)
(* tuple is verifiable w.r.t a message.                                        *)
(*******************************************************************************)
Module Signable.

Section RawMixin.

Variable T: Type.

(* Public keys can canonically be hashed to an address *)
Variable PublicKey: Type.
(* In most practical cases, we expect to be able to hash the PublicKey to an *)
(* eqType Address, which will be used as a finType or through a set *)
Variable Address: hashType PublicKey.

Variable Signature: eqType.

Record mixin_of (H: Type) := Mixin {
  verify: H -> PublicKey -> Signature -> bool;
}.

End RawMixin.

Section ClassDef.

Variables (T: Type) (PublicKey: Type) (Signature : eqType).

Structure class_of (H: Type) := Class {
  base : Hash.class_of T H;
  mixin : mixin_of PublicKey Signature (Hash.Pack (Phant T) base)
}.

Local Coercion base : class_of >-> Hash.class_of.

Structure type (phT: phant T)(phP : phant PublicKey)(phS: phant Signature) := Pack {sort; _ : class_of sort}.

Local Coercion sort : type >-> Sortclass.
Variable (phT: phant T) (phP : phant PublicKey) (phS: phant Signature) (H: Type) (cH : type phT phP phS).
Definition class := let: Pack _ c as cH' := cH return class_of cH' in c.
Definition clone c of phant_id class c := @Pack phT phP phS H c.
Let xH := let: @Pack _ _ _ H _ := cH in H.
Notation xclass := (class : class_of xH).

Definition pack b0 (m0 : mixin_of PublicKey Signature (@Hash.Pack _ (Phant T) H b0)) :=
  fun bH b & phant_id (@Hash.class T (Phant T) bH) b =>
  fun    m & phant_id m0 m => @Pack phT phP phS _ (@Class H b m).

(* Same FCSL "bug"*)
(* if we had not re-exported that coercion above, we would need *)
(* Local Coercion Ordered.base : Ordered.class_of >-> Equality.class_of. *)

Definition eqType := Eval hnf in @Equality.Pack cH xclass.
Definition ordType := Eval hnf in @Ordered.Pack cH xclass.
Definition hashType := Eval hnf in @Hash.Pack _ (Phant T) cH xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Hash.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Declare Scope signable_scope.
Bind Scope signable_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion ordType : type >-> Ordered.type.
Canonical ordType.
Coercion hashType : type >-> Hash.type.
Canonical hashType.

Notation signType T P S := (type (Phant T) (Phant P) (Phant S)).

Notation SignType T P S H m := (@pack _ _ _ (Phant T) (Phant P) (Phant S) H _ m _ _ id _ id).
Notation SignMixin := Mixin.
Notation "[ 'signType' P 'with' S 'of' H 'for' cH ]" := (@clone _ (Phant P) _ (Phant S) H cH _ idfun)
  (at level 0, format "[ 'signType'  P 'with' S 'of'  H  'for'  cH ]") : form_scope.
Notation "[ 'signType' P 'with' S 'of' H ]" := (@clone _ (Phant P) _ (Phant S) H _ _ id)
  (at level 0, format "[ 'signType'  P 'with' S  'of'  H ]") : form_scope.
End Exports.

End Signable.
Export Signable.Exports.

Declare Scope sign_scope.
Delimit Scope sign_scope with S.
Open Scope sign_scope.

Definition verify_op (T P: Type) (S: eqType) (H: signType T P S) :=
  Signable.verify (Signable.mixin (Signable.class H)).

Section HonestNodes.

Variable PublicKey: Type.
(* PublicKey-s hash to Addresses*)
Variable Address: hashType PublicKey.
(* TODO: we may want to make PublicKey & Signature mutually dependent, *)
(* i.e. have structure on a triplet of Private, Public keys and Signature *)
Variable Signature: eqType.

Variable T: Type.
Variable H: signType T PublicKey Signature.

(* Honest nodes are nodes that conditionally sign things*)
Definition honest (condition: pred H)(a: Address) :=
  fun (h:H)(p: PublicKey)(s: Signature) =>
    (hash_op Address p) == a ->
    verify_op (h) p s -> condition h.

End HonestNodes.
