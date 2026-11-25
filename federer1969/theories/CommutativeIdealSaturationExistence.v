(** Federer (1969), 3.4.8(10), p. 331:
    the exact auxiliary power-membership predicate
    exists and is unique. Its construction
    proves existence only; later arguments use
    the independent membership law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealSaturationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [commutative_ideal_saturation_exists]: the
    auxiliary set of germs whose delta
    multiple lies in F, supporting the
    power argument in 3.4.8(10), p. 331. *)
Theorem commutative_ideal_saturation_exists (A:comNzRingType) (I:set A) (delta:A):
  exists S:set A,is_commutative_ideal_saturation I delta S.
Proof. exists (fun x:A=>exists u:nat,I (delta^+u*x));by move=>x. Qed.

(** Source for [commutative_ideal_saturation_unique]: exact
    power membership determines the auxiliary
    saturation uniquely, supporting 3.4.8(10), p. 331. *)
Theorem commutative_ideal_saturation_unique (A:comNzRingType) (I:set A) (delta:A) (S T:set A):
  is_commutative_ideal_saturation I delta S ->is_commutative_ideal_saturation I delta T ->S = T.
Proof.
move=>hS hT;apply:funext=>x;apply:propext;by rewrite hS hT.
Qed.
