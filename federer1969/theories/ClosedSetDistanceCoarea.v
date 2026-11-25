(** Federer (1969), 3.2.34, p. 271:
    volume of a strip of the actual distance
    equals the scalar integral of the masses of
    its whole original level sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanOneCoordinate
  MetricSetDistanceUP MetricSetDistanceSealed EuclideanDistanceStripCoarea EuclideanDistanceLevelFibres
  EuclideanLebesgueDimensions ScalarEuclideanApproximateLimits LebesgueScalarMeasure RealOpenIntervals
  HausdorffMeasure MeasureUP MeasurePushforward MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence InjectivePushforwardIntegral PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition PartialZeroExtension ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_34]: the whole lemma
    in Federer 3.2.34, p. 271. S is
    any nonempty closed subset of R^n and
    d is specified by the independent distance laws.
    Both displayed integral and volume may be infinite;
    the fibres are the whole sets d^-1{y}.
    Positive n is the printed scope of H^(n-1).
    The case n=1 follows from area/coarea at
    equal dimensions; no convexity, boundedness, derivative
    field or individual-fibre finiteness is required. *)
Theorem federer_3_2_34 (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d a b:
  (0<n)%N ->closed S ->S!=set0 ->is_metric_set_distance S d ->0<=a<b ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval a b)
    (partial_function_total (fun t:R=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) (n-1) [set x|d x=t]
      :extended_real_line R))) (@euclidean_lebesgue_measure R n [set x|a<d x<b]).
Proof.
move=>hn hClosed hNonempty hDistance /andP[ha hab].
have hVector:=@euclidean_distance_strip_coarea R n S d a b hn hClosed hNonempty hDistance ha.
have hPre:is_measure_integral (@euclidean_lebesgue_measure R 1)
    (partial_function_precompose (@euclidean_one_project R)
      (partial_function_zero_extension (0%E:extended_real_line R) (real_open_interval a b)
        (partial_function_total (fun t:R=>(@hausdorff_measure R
          (inner_metric_space (@euclidean_inner_productP R n)) (n-1) [set x|d x=t]
          :extended_real_line R))))) (@euclidean_lebesgue_measure R n [set x|a<d x<b]).
  apply:(measure_integral_graph_equivalent _ hVector)=>y z.
  exact:euclidean_distance_level_cutoff_graph.
have hPush:measure_pushforward (@euclidean_one_project R) (@euclidean_lebesgue_measure R 1)=
    @lebesgue_scalar_measure R.
  apply:funext=>A; exact:Logic.eq_sym (euclidean_one_project_measure_preimage A).
have hi:=(@injective_pushforward_integral_iff R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R 1)] R
  (@euclidean_lebesgue_measure R 1) (euclidean_lebesgue_is_measure R 1)
  (@euclidean_one_project R) _ (can_inj (@euclidean_one_projectK R)) _).1 hPre.
by rewrite hPush in hi.
Qed.

(** Source for [closed_set_distance_coarea]: the same
    whole lemma of Federer 3.2.34, p. 271,
    applied directly to the existing opaque distance
    object. This corollary discharges the independent
    distance laws and selects no new global witness. *)
Corollary closed_set_distance_coarea (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (hNonempty:S!=set0) a b:
  (0<n)%N ->closed S ->0<=a<b ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval a b)
    (partial_function_total (fun t:R=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) (n-1)
      [set x|MetricSetDistance.value hNonempty x=t]:extended_real_line R)))
    (@euclidean_lebesgue_measure R n [set x|a<MetricSetDistance.value hNonempty x<b]).
Proof.
move=>hn hClosed hab.
exact:(federer_3_2_34 hn hClosed hNonempty (MetricSetDistance.laws hNonempty) hab).
Qed.
