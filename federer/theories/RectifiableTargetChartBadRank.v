(** Federer (1969), 3.2.22, p. 259: a
    target-chart parameter is either tangent-correct or
    its inverse image under phi has deficient coordinate
    differential rank almost everywhere. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP NormDifferentialDirectional LinearRankUP LinearRankAtLeast LipschitzUP
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue HausdorffMeasure MeasureUP MeasureRestriction
  MeasureAlmostUP MeasureAlmostBasic MeasureApproximateTangentUP RectifiableCompactChartsUP
  RectifiableTargetChartTangent NullTargetRankAllDegrees.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_target_chart_good_parameters]:
    the complement of the bad target-coordinate set
    displayed in Federer 3.2.22, p. 259.
    Every actual differential of gamma at a good
    parameter has image equal to the actual approximate
    tangent cone of Z at its image point. The
    compact chart separately supplies actual differentiability. *)
Definition rectifiable_target_chart_good_parameters (R:realType) mu v
    (Z:set (R_n R v)) (gamma:R_n R mu->R_n R v):set (R_n R mu):=
  [set y|forall D:Hom (R_n R mu) (R_n R v),
    has_norm_differential (inner_norm (@euclidean_inner_productP R mu))
      (inner_norm (@euclidean_inner_productP R v)) setT gamma y D ->
    range D=measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R v))
      (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu) Z)
      mu (gamma y)].

(** Source for [rectifiable_target_chart_good_or_deficient_rank]:
    the second use of 3.2.21 in Federer 3.2.22,
    p. 259. The bad parameters form a
    Lebesgue-mu-null set by the target application of
    3.2.19. Apply the null-target rank theorem to
    a Borel null hull and use actual differential
    uniqueness. Degree zero uses the empty-null-set case;
    no Borel premise on the bad parameter set is added. *)
Theorem rectifiable_target_chart_good_or_deficient_rank (R:realType) m mu v
    (lambda:R) (Z:set (R_n R v)) (C:set (R_n R mu))
    (gamma:R_n R mu->R_n R v)
    (phi:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R mu)):
  1<lambda ->is_uniform_compact_rectifiable_chart lambda C gamma ->
  gamma @` C `<=` Z ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu Z< +oo)%E ->
  is_metric_lipschitz setT phi ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R m) [set a|
    C (phi a) ->rectifiable_target_chart_good_parameters Z gamma (phi a) \/
      forall L:Hom (R_n R m) (R_n R mu),
        has_norm_differential (inner_norm (@euclidean_inner_productP R m))
          (inner_norm (@euclidean_inner_productP R mu)) setT phi a L ->
        ~linear_rank_at_least L mu].
Proof.
move=>hLambda hChart hCZ hZ hFinite hPhi.
have hGood:measure_almost_everywhere_on (@euclidean_lebesgue_measure R mu) C
    (rectifiable_target_chart_good_parameters Z gamma).
  exact:(rectifiable_target_chart_tangent_almost hLambda hChart hCZ hZ hFinite).
pose N:=C `\` rectifiable_target_chart_good_parameters Z gamma.
have hN:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R mu)) mu N=0%E.
  rewrite (euclidean_hausdorff_spherical_lebesgue N).1; exact hGood.
have hRank:=@null_target_rank_all_degrees R m mu mu phi N hPhi hN.
apply:(measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R m) _
  ((measure_almost_everywhere_on_implication _ _ _).1 hRank))=>a hRankA hCa.
have [hG|hG]:=pselect (rectifiable_target_chart_good_parameters Z gamma (phi a)); first by left.
right=>L hL hAtLeast.
have hNa:N (phi a) by split.
have [L0 [r [hL0 [hr hLess]]]]:=hRankA hNa.
have hEq:L=L0:=@norm_differential_unique R (R_n R m) (R_n R mu)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R mu))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R mu)) setT phi a L L0 hL hL0.
rewrite hEq in hAtLeast.
have hLe:=(linear_rank_at_leastP mu hr).1 hAtLeast.
have hFalse:=leq_ltn_trans hLe hLess; by rewrite ltnn in hFalse.
Qed.
