(** Federer (1969), 2.1.1, p. 51: every extended-real set has a supremum and
    an infimum, including the empty set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP ExtendedRealBoundsConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type ExtendedRealBoundsSignature.
(** Source for [value]: Federer 2.1.1, p. 51, third paragraph;
    abstract choice of the extended-real least upper bound. *)
Parameter value : forall (R : realType), set (\bar R) -> \bar R.
(** Source for [laws]: Federer 2.1.1, p. 51, third paragraph;
    the chosen value satisfies the least-upper-bound laws. *)
Parameter laws : forall (R : realType) (S : set (\bar R)),
  is_extended_real_supremum S (@value R S).
End ExtendedRealBoundsSignature.

Module ExtendedRealBounds : ExtendedRealBoundsSignature.
(** Source for [value]: Federer 2.1.1, p. 51, third paragraph;
    private witness chosen from the proved existence theorem. *)
Definition value (R : realType) (S : set (\bar R)) :=
  projT1 (cid (@extended_real_supremum_exists R S)).
(** Source for [laws]: Federer 2.1.1, p. 51, third paragraph;
    correctness of the chosen witness, hidden by opaque ascription. *)
Lemma laws (R : realType) (S : set (\bar R)) :
  is_extended_real_supremum S (value S).
Proof. exact: projT2 (cid (@extended_real_supremum_exists R S)). Qed.
End ExtendedRealBounds.
