(** Federer (1969), 3.4.8(8), p. 329:
    the original proper-ideal quotient exists.
    Reuse the project's quotient algebra through
    the private scalar-ring hierarchy adapter. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeQuotientUP ScalarIdealQuotientConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [scalar_commutative_quotient_exists]: the
    canonical quotient p in 3.4.8(8), p. 329,
    with its exact original kernel. The
    Chapter 1 quotient supplies existence. *)
Theorem scalar_commutative_quotient_exists (K:fieldType) (A:comNzRingType)
  (scalar:{rmorphism K->A}) (I:set A):
  is_commutative_ideal I ->~I 1 ->exists (C:comNzRingType) (pi:{rmorphism A->C}),
    is_commutative_ideal_quotient I pi.
Proof. exact:(@scalar_ideal_quotient_witness K A scalar I). Qed.
