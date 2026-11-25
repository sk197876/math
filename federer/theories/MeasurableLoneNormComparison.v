(** Federer (1969), 4.1.23, p. 379: restrict
    finite-image approximants to the original compact
    support without increasing the L1 error. These
    supporting comparisons reuse the original norm integrals
    and exact partial-function graph laws of 2.4.12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialNormedArithmetic PartialNormPower PartialExtendedOrderLoci RealPower
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasurableNormedFunctionUP MeasurableNormedBasic MeasurableNormedDifference
  MeasureIntegralUP MeasureIntegralComparison MeasureLpNorm MeasureLpNormAlmostEquality
  MeasureLoneNormIntegralGeneral MeasureLpConvergence CompactSummableFieldSealed
  CompactSummableFieldLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LoneComparison.
Variable R : realType.
Variable X : choiceType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation VN := (real_norm_metric_space hN).

(** Source for [measurable_lone_total_norm_monotone]:
    pointwise domination of the original norms
    decreases their actual L1 values, supporting
    compact support preservation in 4.1.23,
    p. 379. Infinite values remain allowed. *)
Theorem measurable_lone_total_norm_monotone (f g : X -> VN) :
  is_measurable_normed_function mu (partial_function_total f) ->
  is_measurable_normed_function mu (partial_function_total g) ->
  (forall x, N (f x)<=N (g x)) ->
  (measure_lp_norm mu N 1 (partial_function_total f)<=
    measure_lp_norm mu N 1 (partial_function_total g))%E.
Proof.
move=> hF hG hNorm.
have hFI := @measurable_lone_norm_integral R X V N hN mu hm
  (partial_function_total f) hF.1.
have hGI := @measurable_lone_norm_integral R X V N hN mu hm
  (partial_function_total g) hG.1.
apply: (@measure_integral_monotone R X mu hm _ _ _ _ hFI hGI).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
  (measure_almost_everywhere_true hm))=> x _.
exists (N (f x))%:E,(N (g x))%:E; split.
- exists (f x); split; first exact: erefl.
  by rewrite (real_power_one_exponent (real_seminorm_nonnegative hN.1 _)).
split.
- exists (g x); split; first exact: erefl.
  by rewrite (real_power_one_exponent (real_seminorm_nonnegative hN.1 _)).
- by rewrite lee_fin; exact: hNorm.
Qed.

(** Source for [measurable_lone_total_difference]: the
    L1 distance of two actual total fields
    is the norm of their actual pointwise
    difference, supporting the step approximation in
    Federer 4.1.23, p. 379. *)
Theorem measurable_lone_total_difference (f g : X -> VN) :
  is_measurable_normed_function mu (partial_function_total f) ->
  is_measurable_normed_function mu (partial_function_total g) ->
  is_measurable_normed_function mu
    (partial_function_total (fun x => (f x-g x)%R)) /\
  measure_lp_norm mu N 1 (partial_function_total (fun x => (f x-g x)%R))=
    measure_lp_distance mu N 1 (partial_function_total f) (partial_function_total g).
Proof.
move=> hF hG.
have hDifference := @measurable_normed_function_subtract R X V N hN mu hm
  (partial_function_total f) (partial_function_total g) hF hG.
have hAlmost : measure_almost_equal mu
    (partial_vector_subtract (partial_function_total f) (partial_function_total g))
    (partial_function_total (fun x => (f x-g x)%R)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  exists (f x-g x)%R; split; last exact: erefl.
  apply/partial_vector_subtract_graph; exists (f x),(g x).
  by split; last split.
have hTotal := @measurable_normed_almost_equal R X V N hN mu hm
  _ _ hDifference hAlmost.
split; first exact: hTotal.
symmetry; exact: (@measure_lp_norm_almost_equal R X V N hN mu hm 1
  _ _ (lexx 1) hDifference.1 hTotal.1 hAlmost).
Qed.
End LoneComparison.

Section CompactLoneDifference.
Variable R : realType.
Variable X : topologicalType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation W := (@CompactSummableField.space R X V N hN mu hm).
Local Notation value := (@compact_summable_field_value R X V N hN mu hm).
Local Notation size := (@compact_summable_field_size R X V N hN mu hm).

(** Source for [compact_summable_field_lp_difference]:
    the original Omega difference cost is its
    literal L1 distance, supporting the mass-error
    estimate in Federer 4.1.23, p. 379.
    Raw representatives need not form a separated normed space. *)
Theorem compact_summable_field_lp_difference (f g : W) :
  (size (f-g)%R)%:E=measure_lp_distance mu N 1
    (partial_function_total (value f)) (partial_function_total (value g)).
Proof.
have hValues : value (f-g)%R=(fun x => (value f x-value g x)%R).
  have hIdentity : (f-g)%R=(-1)*:g+f by rewrite scaleN1r addrC.
  rewrite hIdentity compact_summable_field_value_add compact_summable_field_value_scale.
  apply: funext=> x; by rewrite scaleN1r addrC.
have hSize := @compact_summable_field_size_exact R X V N hN mu hm (f-g)%R.
change ((size (f-g)%R)%:E=
  measure_lp_norm mu N 1 (partial_function_total (value (f-g)%R))) in hSize.
rewrite hValues in hSize.
have hDistance := (@measurable_lone_total_difference R X V N hN mu hm
  (value f) (value g)
  (@compact_summable_field_measurable R X V N hN mu hm f)
  (@compact_summable_field_measurable R X V N hN mu hm g)).2.
exact: eq_trans hSize hDistance.
Qed.
End CompactLoneDifference.
