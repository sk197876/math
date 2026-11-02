(** Federer (1969), 3.2.16, pp. 253–254:
    a null base point need not belong to
    the actual domain. This boundary explains
    why the erratum says the new notion
    generalizes, rather than coincides with, 3.1.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormDifferentialLinear PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction MeasureUP MeasureRestriction MetricDensities
  MetricDensityZeroPowerMass MetricDensityZeroUnions MeasureApproximateDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_approximate_punctured_constant]:
    the actual-domain boundary in Federer
    3.2.16, pp. 253–254. Deleting a null
    base point from a constant map leaves
    it approximately differentiable, with zero linear
    representative and the constant affine value. *)
Theorem measure_approximate_punctured_constant (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (mu : set X -> \bar R) m (a : X) (eta : Y) :
  is_measure mu -> mu [set a]=0%E ->
  has_measure_approximate_differential NY hNX mu m
    (partial_function_source_restrict (~` [set a]) (partial_function_total (fun _ : X=>eta))) a 0.
Proof.
move=> hm ha.
exists setT,(fun _ : X=>eta); split.
- exact: (@norm_differential_constant R X Y NX NY hNX hNY setT a eta
    (@norm_full_domain_interior R X NX a)).
- have hNull := @null_set_metric_density_zero R (real_norm_metric_space hNX) m mu [set a] a hm ha.
  apply: (@metric_restricted_density_zero_subset R (real_norm_metric_space hNX) m mu _ [set a] a hm _ hNull).
  move=> x hx; apply: contrapT=> hne; apply: hx; exists eta; split; by split.
Qed.

(** Source for [punctured_constant_base_undefined]:
    the new example above has no value at
    the base point, so it cannot satisfy
    the actual-domain premise of 3.1.2, p. 212.
    This is the precise boundary retained in
    the corrected comparison of 3.2.16, p. 254. *)
Lemma punctured_constant_base_undefined (X Y : Type) (a : X) (eta : Y) :
  ~partial_function_domain (partial_function_source_restrict (~` [set a])
    (partial_function_total (fun _ : X=>eta))) a.
Proof. by move=> [y [hne _]]; apply: hne. Qed.
