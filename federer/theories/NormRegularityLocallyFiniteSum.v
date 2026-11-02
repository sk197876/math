(** Federer (1969), 3.1.22, p. 236: glue local
    class-k extensions with the partition of unity of 3.1.13. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormRegularity FiniteFamilySumUP NormLocallyFiniteFamilyUP NormClassHigherLocallyFiniteSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_class_locally_finite_sum]: supporting
    the extension characterization in Federer 3.1.22,
    p. 236, from the locally finite class law of
    3.1.13, p. 225. This representation adapter uses
    the existing opaque multilinear spaces and finite-sum laws. *)
Lemma norm_class_locally_finite_sum (R:realType) (X Y:lmodType R) (J:choiceType)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (I:J->Prop) (f:J->X->Y) (g:X->Y) k :
  is_norm_locally_finite_function_family NX U I f ->
  is_finite_family_sum_on U I f g ->
  (forall j,I j -> norm_class hNX hNY U (f j) k) ->
  norm_class hNX hNY U g k.
Proof.
exact (@norm_class_higher_locally_finite_sum R X Y J NX NY hNX hNY
  (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY) U I f g k).
Qed.
