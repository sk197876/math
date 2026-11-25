(** Federer (1969), 3.1.6, pp. 216–217: Lipschitz
    maps have approximate partial derivatives almost everywhere.
    The scalar curve theorem and Fubini discharge this assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  EuclideanCoordinateMetric EuclideanLebesgueDimensions EuclideanCoordinateNullSections
  RealNormUP RealMetricBackground NormMetricScaleContinuity LipschitzUP
  LipschitzRealDifferentiability OrdinaryApproximatePartial NormPartialDerivative
  ApproximatePartialDerivativeUP ApproximatePartialDerivative
  ScalarApproximatePartialMeasurable ApproximatePartialPositiveTargetMeasurable
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialFunctionSourceRestriction
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure
  LebesgueScalarMeasure MeasurableFunctionUP MeasurableGraphEquivalence
  BorelFunctionBasic BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_lipschitz_measurable]: the measurability
    needed to apply 3.1.4 in Federer 3.1.6, p. 217.
    Lipschitz continuity and Borel regularity of Lebesgue measure
    imply measurability of the total map. *)
Lemma euclidean_lipschitz_measurable (R : realType) m (Y : metricType R)
    (f : inner_metric_space (@euclidean_inner_productP R m)->Y) :
  is_metric_lipschitz setT f ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m)
    (partial_function_total f).
Proof.
move=> [M [hM [hM0 hbound]]].
have hc : continuous f.
  apply: (metric_fixed_lipschitz_continuous hM0)=> x y.
  exact: hbound x y Logic.I Logic.I.
have hB := continuous_borel_function hc.
constructor.
- rewrite partial_function_total_domain.
  exact: measure_almost_everywhere_true (euclidean_lebesgue_is_measure R m).
- move=> W hW; rewrite partial_function_total_preimage.
  exact: (borel_regular_borel_measurable
    (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_borel_regular R m) (hB W hW)).
Qed.

(** Source for [scalar_lipschitz_approximate_partial_conull]:
    the linewise application of 2.9.19 followed by Fubini
    in Federer 3.1.6, pp. 216–217, for a scalar target. *)
Theorem scalar_lipschitz_approximate_partial_conull (R : realType) m
    (f : inner_metric_space (@euclidean_inner_productP R m)->real_line_metric R)
    (i : 'I_m) :
  is_metric_lipschitz setT f ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    (partial_function_domain
      (approximate_partial_derivative (scalar_absolute_value_norm R) setT f i)).
Proof.
move=> hLip.
have hf := euclidean_lipschitz_measurable hLip.
have hfA : is_measure_measurable_function (@euclidean_lebesgue_measure R m)
    (partial_function_source_restrict setT (partial_function_total f)).
  apply: (measurable_function_graph_equivalent _ hf)=> x y; by split=> [hy|[_ hy]].
pose A := partial_function_domain
  (approximate_partial_derivative (scalar_absolute_value_norm R) setT f i).
have hA : measure_measurable (@euclidean_lebesgue_measure R m) A.
  exact (@approximate_partial_scalar_domain_measurable R m i setT f hfA).
apply: (euclidean_coordinate_lines_null (i:=i)).
- exact: measure_measurable_complement hA.
- move=> a.
  have [M [hM [hM0 hbound]]] := hLip.
  pose g (t : R) := f (a+t*:(@coordinate_basis R m i)).
  have hg s t : `|g s-g t|<=M*`|s-t|.
    have hh := hbound (a+s*:(@coordinate_basis R m i))
      (a+t*:(@coordinate_basis R m i)) Logic.I Logic.I.
    change (is_true (mdist (g s) (g t)<=M*mdist
      (euclidean_coordinate_line i a s) (euclidean_coordinate_line i a t))) in hh.
    by rewrite euclidean_coordinate_line_distance !real_line_metric_distanceE in hh.
  have hd := lipschitz_real_curve_differentiable_almost_everywhere hg.
  apply: (measure_null_subset (lebesgue_scalar_is_measure R) _ hd).
  move=> t hnot [v hv]; apply: hnot; exists v.
  apply: (approximate_partial_derivative_graph (scalar_absolute_value_norm R) setT
    f i _ v).2.
  apply: ordinary_partial_is_approximate.
  exact: real_coordinate_curve_derivative_partial hv.
Qed.

(** Source for [euclidean_lipschitz_approximate_partial_conull]:
    the finite-target version of the first paragraph in Federer
    3.1.6, pp. 216–217. Target coordinates give a finite
    intersection; a zero-dimensional target is treated directly. *)
Theorem euclidean_lipschitz_approximate_partial_conull (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (i : 'I_m) :
  is_metric_lipschitz setT f ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    (partial_function_domain (approximate_partial_derivative
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f i)).
Proof.
case: n f=> [f hLip|n f hLip].
- apply: (measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R m)
    _ (measure_almost_everywhere_true (euclidean_lebesgue_is_measure R m)))=> a _.
  exists 0.
  apply: (approximate_partial_derivative_graph
    (inner_norm_real_norm (@euclidean_inner_productP R 0)) setT f i a 0).2.
  apply: ordinary_partial_is_approximate.
  move=> e he; exists 1; split; first exact: ltr01.
  move=> t _.
  have hz : t^-1 *: (f (a+t*:(@coordinate_basis R m i))-f a)-0=0
    := coordinate_zero _.
  by rewrite hz inner_norm0.
- rewrite approximate_partial_positive_target_domain.
  apply: (measure_almost_everywhere_countable (euclidean_lebesgue_is_measure R m));
    first exact: countableP.
  move=> j _.
  apply: scalar_lipschitz_approximate_partial_conull.
  have [M [hM [hM0 hbound]]] := hLip.
  exists M; split=> //; split=> // x y _ _.
  apply: (le_trans (euclidean_coordinate_nonexpanding j (f x) (f y)) _).
  exact: hbound x y Logic.I Logic.I.
Qed.
