(** Federer (1969), 4.1.19, p. 377:
    measurable form coefficients have measurable
    evaluations against each fixed multivector.
    Reuse the actual dual-norm bound and
    the original Borel postcomposition theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology ContinuousDualUP RealFunctionalNormUP
  PartialFunctionBasic MeasureUP MeasurableFunctionUP
  MeasurableNormedFunctionUP MeasurableTotalBasic BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_dual_evaluation_measurable]:
    fixed-vector evaluations of the measurable
    representing forms in Federer 4.1.19,
    p. 377, are measurable scalar functions.
    No bound on the field is needed
    for this supporting measurability assertion. *)
Theorem norm_dual_evaluation_measurable (R : realType)
    (X : choiceType) (V D : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hDN : is_real_norm DN) (hDual : is_continuous_dual hN ed DN)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (a : X -> D) (y : V) :
  is_measurable_normed_function mu
    (partial_function_total (fun x => (a x : real_norm_metric_space hDN))) ->
  is_measure_measurable_function mu
    (partial_function_total (fun x =>
      (ed (a x) y : real_norm_metric_space (scalar_absolute_value_norm R)))).
Proof.
move=> hA.
have hLinear : linear (fun d : D => ed d y).
  move=> c v w; by rewrite linearP hom_addE hom_scaleE.
pose eval := @HomMap R D R^o (fun d => ed d y)
  (introT (asboolP _) hLinear).
have hContinuous : continuous (fun d : real_norm_metric_space hDN =>
    (eval d : real_norm_metric_space (scalar_absolute_value_norm R))).
  apply: (@norm_bounded_linear_continuous R D R^o DN (fun t : R => `|t|%R)
    hDN (scalar_absolute_value_norm R) eval).
  exists (N y); split.
  - exact: (real_seminorm_nonnegative hN.1 y).
  - move=> d; rewrite mulrC.
    exact: (real_functional_norm_bound
      (continuous_dual_norm_laws hDual d) y).
exact: (@measurable_total_borel_postcomposition R X
  (real_norm_metric_space hDN)
  (real_norm_metric_space (scalar_absolute_value_norm R)) mu hm
  (fun x => (a x : real_norm_metric_space hDN))
  (fun d => (eval d : real_norm_metric_space (scalar_absolute_value_norm R)))
  hA.1 (continuous_borel_function hContinuous)).
Qed.
