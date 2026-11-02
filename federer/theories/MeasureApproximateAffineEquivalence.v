(** Federer (1969), 3.2.16, p. 253:
    both directions of the affine criterion,
    retaining a fixed ambient linear representative
    and an existential affine base value. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP PartialFunctionUP MeasureUP
  MeasureApproximateDifferentialUP MeasureApproximateAffineUP
  MeasureApproximateAffineForward MeasureApproximateAffineReverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [measure_approximate_differential_affine_iff]:
    the exact affine characterization in Federer
    3.2.16, p. 253, for each continuous
    linear representative. The value eta is not
    assumed to be a defined value of f(a). *)
Theorem measure_approximate_differential_affine_iff (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (mu : set X -> \bar R) m (f : partial_function X Y) a (D : Hom X Y) :
  is_measure mu ->
  (has_measure_approximate_differential NY hNX mu m f a D <->
    exists eta, has_measure_approximate_affine_criterion NY hNX mu m f a eta D).
Proof.
move=> hm; split.
- exact: measure_approximate_differential_affine_criterion hm.
- move=> [eta hCrit].
  exact: (@measure_affine_criterion_approximate_differential R X Y NX NY hNX hNY mu m f a eta D hm hCrit).
Qed.

(** Source for [federer_3_2_16_affine_criterion]:
    approximate differentiability if and only if
    there exist eta and a continuous linear
    affine approximation, Federer 3.2.16, p. 253.
    All positive error tests are required. *)
Theorem federer_3_2_16_affine_criterion (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (mu : set X -> \bar R) m (f : partial_function X Y) a :
  is_measure mu ->
  (measure_approximately_differentiable_at NY hNX mu m f a <->
    exists eta (D : Hom X Y), has_measure_approximate_affine_criterion NY hNX mu m f a eta D).
Proof.
move=> hm; split.
- move=> [D hD].
  have [eta he] := (@measure_approximate_differential_affine_iff R X Y NX NY hNX hNY mu m f a D hm).1 hD.
  by exists eta,D.
- move=> [eta [D hCrit]]; exists D.
  apply: (@measure_approximate_differential_affine_iff R X Y NX NY hNX hNY mu m f a D hm).2.
  by exists eta.
Qed.
