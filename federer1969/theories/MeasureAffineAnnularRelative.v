(** Federer (1969), 3.2.16, p. 253,
    erratum p. 5, line 32: differentiability
    relative to the selected annular set, with
    the closure-domain convention of 3.1.22 retained.
    A positive atom supplies that closure automatically. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction PartialFunctionExtensionUP MeasureUP TangentConeUP
  RelativeDifferentialUP RelativeApproximationCriterion
  MeasureApproximateAffineUP MeasureAffineAnnularApproximation
  MetricDensityAnnularRadii ShrinkingRadiusSelectionUP NormAnnularSetUP
  NormAnnularOmissionDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_affine_annular_relative_differentiable]:
    the concluding relative differentiability in
    Federer 3.2.16, p. 253, corrected
    by the erratum and read on the closure
    domain specified in 3.1.22, p. 235. *)
Theorem measure_affine_annular_relative_differentiable (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (mu : set X -> \bar R) m (f : partial_function X Y) a eta (D : Hom X Y)
    (rho : nat -> R) (T : set X) (g : X -> Y) :
  is_measure mu ->
  has_measure_approximate_affine_criterion NY hNX mu m f a eta D ->
  is_shrinking_radius_selection
    (@metric_density_annular_radius_property R (real_norm_metric_space hNX) mu m
      (measure_affine_annular_good_sets NX NY f a eta D) a) rho ->
  is_norm_annular_set NX (measure_affine_annular_good_sets NX NY f a eta D) a rho T ->
  is_partial_function_total_extension f g ->
  @closure (real_norm_metric_space hNX) (norm_annular_corrected_set mu a T) a ->
  @relative_norm_differentiable_at R X Y NX NY hNX (partial_function_domain f)
    (norm_annular_corrected_set mu a T) g a.
Proof.
move=> hm hCrit hR hT hExt hcl.
pose A := norm_annular_corrected_set mu a T.
pose L := partial_function_source_restrict (norm_tangent_cone NX A a) (partial_function_total D).
exists L.
apply: (@relative_norm_differential_remainder_criterion R X Y NX NY hNX hNY
  (partial_function_domain f) A g a L hcl).2.
exists eta,D; split.
- exact: (@measure_affine_annular_first_order R X Y NX NY hNX hNY
    mu m f a eta D rho T g hm hCrit hR hT hExt).
- by move=> v y.
Qed.

(** Source for [measure_affine_annular_atom_closure]:
    the positive-atom case in the erratum to
    Federer 3.2.16, p. 253 line 32.
    The corrected set contains a itself, so
    the relative definition's closure condition holds. *)
Lemma measure_affine_annular_atom_closure (R : realType) (X : lmodType R)
    (NX : X -> R) (hNX : is_real_norm NX) (mu : set X -> \bar R)
    (a : X) (T : set X) :
  (0<mu [set a])%E ->
  @closure (real_norm_metric_space hNX) (norm_annular_corrected_set mu a T) a.
Proof.
move=> hA; apply: subset_closure; right; by split.
Qed.
