(** Federer (1969), 3.2.47, p. 282: finite sums of
    smooth coefficient-vector products in Gram–Schmidt preserve every
    finite differentiability class, by 3.1.11, pp. 220–223. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearSealed NormRegularity
  NormClassHigherFiniteSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_finite_sum]: public representation
    adapter for the finite projection sums in 3.2.47, p. 282,
    including the empty prefix, by 3.1.11, p. 221. *)
Lemma norm_class_finite_sum (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (I:finType) (f:I->X->Y) k:
  (forall x,A x->norm_domain_interior NX A x) ->
  (forall i,norm_class hNX hNY A (f i) k) ->
  norm_class hNX hNY A (fun x=>\sum_i f i x) k.
Proof.
move=>hA hf.
exact (@norm_class_higher_finite_sum R X Y NX NY hNX hNY
  (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY) A hA I f k hf).
Qed.
