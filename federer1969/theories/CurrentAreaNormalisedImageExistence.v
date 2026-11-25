(** Federer (1969), 4.1.25, p. 383: existence of
    the original normalized differential summand. Restrict
    the already sealed partial differential to its nonzero
    Jacobian locus, then apply the existing source-dependent
    graph composition. This serves only as an existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialSealed
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading EuclideanLinearJacobian PartialFunctionUP
  PartialFunctionSourceRestriction PartialFunctionSourcePostcomposition
  CurrentAreaNormalisedImageUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_area_normalised_image_exists]: the
    summand in Federer 4.1.25, p. 383, exists with
    exactly its original partial domain. No regularity
    or representation assumption is inserted into this
    set-theoretic existence result. *)
Theorem current_area_normalised_image_exists (R : realType) m n
    (f : R_n R m -> R_n R n)
    (xi : R_n R m -> exterior_power (R_n R m) m) :
  exists u : partial_function (R_n R m) (exterior_power (R_n R n) m),
    is_current_area_normalised_image f xi u.
Proof.
pose X := R_n R m; pose Y := R_n R n.
pose NX := inner_norm (@euclidean_inner_productP R m).
pose NY := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R n).
pose Full := fun _ : X => True.
pose D := @NormDifferential.value R X Y NX NY hNX hNY Full f.
pose hD := @NormDifferential.laws R X Y NX NY hNX hNY Full f.
pose C := [set x : X | exists L : Hom X Y,
  partial_function_graph D x L /\ @euclidean_linear_jacobian R m n m L != 0].
pose g := partial_function_source_restrict C D.
pose u := partial_function_source_postcompose g
  (@current_area_normalised_image_coefficient R m n xi).
exists u; move=> x v.
rewrite /u partial_function_source_postcompose_graph; split.
- move=> [L [[hC hL] hValue]].
  have [H [hH hNonzero]] := hC.
  have hEqual : H = L := partial_function_single_valued hH hL.
  exists L; split; first exact: (hD x L).1 hL.
  split; last exact: hValue.
  by rewrite -hEqual.
- move=> [L [hActual [hNonzero hValue]]].
  have hL : partial_function_graph D x L := (hD x L).2 hActual.
  exists L; split; last exact: hValue.
  split; last exact: hL.
  exists L; by split.
Qed.
