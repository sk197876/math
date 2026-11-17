(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: the
    original factorial-growth subsets behind an opaque membership interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermOperationsUP RealNormUP HolomorphicGermUP HolomorphicGermGrowthUP HolomorphicGermGrowthExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type HolomorphicGermGrowthSignature.
(** Source for [value]: the original growth classes indexed
    by positive integers in 3.4.5, p. 319; zero
    indices are also available for supporting subset laws. *)
Parameter value:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X),nat->nat->set (holomorphic_germ_space hNX a).
(** Source for [laws]: the exact original derivative-bound
    membership laws, 3.4.5, p. 319. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) s t,
  is_holomorphic_germ_growth_class s t (@value R X NX hNX a s t).
End HolomorphicGermGrowthSignature.
Module HolomorphicGermGrowth:HolomorphicGermGrowthSignature.
(** Source for [value]: the private set witness from
    proved existence, 3.4.5, p. 319. *)
Definition value (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) s t:=
  projT1 (cid (@holomorphic_germ_growth_class_exists R X NX hNX a s t)).
(** Source for [laws]: the selected class satisfies the
    independent original bounds, 3.4.5, p. 319. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) s t:
  is_holomorphic_germ_growth_class s t (@value R X NX hNX a s t).
Proof. exact:(projT2 (cid (@holomorphic_germ_growth_class_exists R X NX hNX a s t))). Qed.
End HolomorphicGermGrowth.
