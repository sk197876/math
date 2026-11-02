(** Federer (1969), 3.2.16, p. 253:
    the reverse affine criterion. The corrected
    annular choice is density-full and admits
    the differentiable extension proved in 3.1.22.
    No closure or local-finiteness premise is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialFunctionExtensionUP PartialFunctionExtensionSealed MeasureUP MeasureRestriction
  MetricDensities MetricDensityZero MetricDensityAnnularRadii
  ShrinkingRadiusSelectionUP NormAnnularSetUP NormAnnularSetSealed
  NormAnnularOmissionDensity MeasureAffineAnnularApproximation
  RelativeDifferentialUP RelativeApproximationCriterion
  MeasureApproximateDifferentialUP MeasureApproximateAffineUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_affine_criterion_approximate_differential]:
    the reverse implication in Federer 3.2.16,
    p. 253. The annular radii obey the
    erratum's half decrease and the centre is
    adjoined only at positive atoms. The conclusion
    is the original ambient-extension definition. *)
Theorem measure_affine_criterion_approximate_differential (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (mu : set X -> \bar R) m (f : partial_function X Y) a eta (D : Hom X Y) :
  is_measure mu ->
  has_measure_approximate_affine_criterion NY hNX mu m f a eta D ->
  has_measure_approximate_differential NY hNX mu m f a D.
Proof.
move=> hm hCrit.
pose M := real_norm_metric_space hNX.
pose S := measure_affine_annular_good_sets NX NY f a eta D.
have hS n : partial_function_graph (@metric_density R M m
    (measure_restrict mu (~` S n))) a 0%E.
  apply: hCrit.2; by rewrite invr_gt0 ltr0n.
have [rho hR] := @metric_density_annular_radii_exist R M mu m S a hm hS.
pose T := @NormAnnularSet.value R X NX S a rho.
have hT : is_norm_annular_set NX S a rho T := NormAnnularSet.laws NX S a rho.
pose A := norm_annular_corrected_set mu a T.
have hFull := norm_annular_corrected_full_density hm hR hT.
pose g0 := @PartialFunctionExtension.value X Y f 0.
have hExt : is_partial_function_total_extension f g0 := @PartialFunctionExtension.laws X Y f 0.
have hFirst := @measure_affine_annular_first_order R X Y NX NY hNX hNY
  mu m f a eta D rho T g0 hm hCrit hR hT hExt.
have [U [g [hg [_ hAgree]]]] := @relative_approximation_extension R X Y NX NY hNX hNY
  (partial_function_domain f) A g0 a eta D hFirst.
exists U,g; split=> //.
have [d [hd hU]] := norm_differential_interior hg.
apply: (@metric_restricted_density_zero_local_mono R M m mu
  (~` partial_function_agreement f
    (partial_function_source_restrict U (partial_function_total g))) (~` A) a hm _ hFull).
exists d; split=> // x hdist hBad hxA.
have hsmall : NX (x-a)<d.
  change (is_true (NX (a-x)<d)) in hdist.
  by rewrite (real_seminorm_subtract hNX.1) in hdist.
have hxU : U x.
  have hh := hU (x-a) hsmall; by rewrite addrC subrK in hh.
have [[y hfy] hEq] := hAgree x hxA hxU.
apply: hBad; exists y; split=> //; split=> //.
exact: eq_trans (esym hEq) (hExt x y hfy).
Qed.
