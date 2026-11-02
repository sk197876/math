(** Federer (1969), 3.2.34, p. 271: apply
    coarea to the original positive-distance strip.
    The Jacobian equals one almost everywhere, including
    the one-dimensional area boundary case. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanOneCoordinate
  RealMetricBackground RealOpenIntervals MetricSetDistanceUP MetricSetDistanceContinuity
  EuclideanDistanceLipschitz EuclideanDistanceJacobianAlmost EuclideanNonStrictCoarea
  EuclideanLebesgueDimensions BorelRegularMeasureUP TopologicalBorel HausdorffMeasure MappingMultiplicity
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral
  MeasureSubsetConstantIntegral MeasureIntegralUniqueness SubsetIntegralAlmostAgreement
  PartialFunctionUP PartialFunctionBasic EuclideanTargetJacobianMeasurable ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_distance_strip_open]: the
    source A={x:a<f(x)<b} in the proof
    of Federer 3.2.34, p. 271. Actual
    continuity makes it open; neither finite mass
    nor closedness of the original set is needed. *)
Lemma euclidean_distance_strip_open (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d a b:
  is_metric_set_distance S d ->open [set x|a<d x<b].
Proof.
move=>hDistance.
have hSet:[set x|a<d x<b]=d @^-1` real_open_interval a b.
  apply/seteqP; split=>x.
  - by move=>/andP[h1 h2]; split.
  - by move=>[h1 h2]; apply/andP; split.
rewrite hSet.
apply:(@open_comp
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
  [the topologicalType of real_line_metric R] d (real_open_interval a b)).
- by move=>x _; exact:(@metric_set_distance_continuous R
    (inner_metric_space (@euclidean_inner_productP R n)) S d hDistance x).
- exact:real_open_interval_open.
Qed.

(** Source for [euclidean_distance_strip_measurable]: the
    coarea source in the last line of Federer
    3.2.34, p. 271. Openness gives Borel,
    hence Lebesgue, measurability without finite mass. *)
Lemma euclidean_distance_strip_measurable (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d a b:
  is_metric_set_distance S d ->
  measure_measurable (@euclidean_lebesgue_measure R n) [set x|a<d x<b].
Proof.
move=>hDistance.
apply:(borel_regular_borel_measurable (euclidean_lebesgue_is_measure R n)
  (euclidean_lebesgue_borel_regular R n)).
apply:open_borel_set; exact:(@euclidean_distance_strip_open R n S d a b hDistance).
Qed.

(** Source for [euclidean_distance_strip_coarea]: the
    application of 3.2.11 in Federer 3.2.34,
    p. 271. This intermediate version uses the
    Euclidean line as target and the exact strip
    fibres. The scalar whole-level-set form is proved
    separately by exact fibre and integral transport.
    Infinite source mass and n=1 are retained. *)
Theorem euclidean_distance_strip_coarea (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d a b:
  (0<n)%N ->closed S ->S!=set0 ->is_metric_set_distance S d ->0<=a ->
  is_measure_integral (@euclidean_lebesgue_measure R 1)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) (n-1)
      (mapping_fibre (fun z=>euclidean_one_embed (d z)) [set x|a<d x<b] y)
      :extended_real_line R))) (@euclidean_lebesgue_measure R n [set x|a<d x<b]).
Proof.
move=>hn hClosed hNonempty hDistance ha.
pose A:set (R_n R n):=[set x|a<d x<b].
pose hMu:=euclidean_lebesgue_is_measure R n.
have hA:=@euclidean_distance_strip_measurable R n S d a b hDistance.
have [I [hSource hTarget]]:=@euclidean_non_strict_coarea_formula R n 1
  (fun x=>euclidean_one_embed (d x)) A hn
  (euclidean_distance_lipschitz hDistance) hA.
have hConstant:=@measure_nonnegative_constant_subset_integral R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  (@euclidean_lebesgue_measure R n) A 1%E hMu hA (ltac:(by rewrite lee_fin)).
rewrite mul1e in hConstant.
have hSourceConstant:is_measure_subset_integral (@euclidean_lebesgue_measure R n) A
    (partial_function_total (fun _ : R_n R n=>(1%E:extended_real_line R))) I.
  apply:(subset_integral_almost_agreement hMu _ hSource).
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono hMu _
    ((measure_almost_everywhere_on_implication _ _ _).1
      (@euclidean_distance_jacobian_one_almost R n S d a b hClosed hNonempty hDistance ha))).
  move=>x hOne hx; exists (1%E:extended_real_line R); split; first exact:hOne hx.
  reflexivity.
have hValue:=measure_integral_unique hSourceConstant hConstant.
by rewrite -hValue.
Qed.
