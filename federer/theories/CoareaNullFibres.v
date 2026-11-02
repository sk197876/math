(** Federer (1969), 3.2.11, p. 249: the
    zero-source-measure case, deduced from 2.10.25 and
    2.10.35. Reuse the proved null-fibre theorem, including
    its proper-source justification and arbitrary null source sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanClosedBallCompact
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue HausdorffMeasure HausdorffFibreCutoffs
  NullFibresProperSource MetricClosedBalls LipschitzFunctionCompact MappingMultiplicity CoareaJacobianMeasure
  EuclideanTargetJacobianMeasurable LipschitzUP MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure MeasureAlmostUP
  MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral MeasureConullZeroIntegral
  PartialFunctionUP PartialFunctionBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_euclidean_source_proper]: supporting
    use of 2.10.25 in Federer 3.2.11, p. 249.
    Euclidean closed balls are compact, including dimension zero,
    by the already proved finite-dimensional compactness theorem. *)
Lemma coarea_euclidean_source_proper (R:realType) d:
  metric_boundedly_compact (inner_metric_space (@euclidean_inner_productP R d)).
Proof. move=>a r hr; exact (@EuclideanClosedBallCompact.euclidean_closed_metric_ball_compact R d a r). Qed.

(** Source for [coarea_null_source_fibres_almost_zero]:
    the first sentence of the proof of Federer 3.2.11,
    p. 249. A null source set has Hausdorff-null
    complementary fibres for Lebesgue-almost every target point.
    No source measurability premise is added. *)
Theorem coarea_null_source_fibres_almost_zero (R:realType) n k
    (f:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  is_metric_lipschitz setT f ->euclidean_lebesgue_measure (n+k) A=0 ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set y|@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+k))) k
      (mapping_fibre f A y)=0].
Proof.
move=>[L [hL hBound]] hA.
pose X:=inner_metric_space (@euclidean_inner_productP R (n+k)).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
have hHaus:@hausdorff_measure R X (k+n) A=0.
  have hDim:=congr1 (fun d:nat=>@hausdorff_measure R X d A) (addnC k n).
  rewrite hDim (euclidean_hausdorff_spherical_lebesgue A).1; exact hA.
have hNull:=@null_hausdorff_fibres_proper_source R X Y f L A k n
  (@coarea_euclidean_source_proper R (n+k)) hBound hHaus.
have hTarget:(@hausdorff_measure R Y n)=(@euclidean_lebesgue_measure R n).
  apply:funext=>B; exact (euclidean_hausdorff_spherical_lebesgue B).1.
rewrite hTarget in hNull.
exact hNull.
Qed.

(** Source for [coarea_null_source_integrals]: the null
    source case of Federer 3.2.11, p. 249. Both
    actual integrals equal zero, using the existing density
    measure and the derived null-fibre conclusion. *)
Theorem coarea_null_source_integrals (R:realType) n k
    (f:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  is_metric_lipschitz setT f ->euclidean_lebesgue_measure (n+k) A=0 ->
  is_measure_subset_integral (@euclidean_lebesgue_measure R (n+k)) A
    (extended_euclidean_target_jacobian f) 0 /\
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R (n+k))) k (mapping_fibre f A y)
        :extended_real_line R))) 0.
Proof.
move=>hf hA; split.
- have hMeas:=measure_null_measurable (euclidean_lebesgue_is_measure R (n+k)) hA.
  have hI:=euclidean_coarea_measure_integral hf hMeas.
  by rewrite (euclidean_coarea_measure_null f hA) in hI.
- apply:(measure_almost_zero_integral (euclidean_lebesgue_is_measure R n)).
  exact (coarea_null_source_fibres_almost_zero hf hA).
Qed.
