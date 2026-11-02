(** Federer (1969), 3.1.9, p. 218: almost-everywhere
    differentiability on one uniform closed-center set. Small closed
    pieces permit application of 3.1.7 and 2.9.11; 3.1.5 then
    turns their approximate differentials into ordinary differentials. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanMetricSeparability TopologicalBorel
  EuclideanApproximateContext MetricLocalLipschitzCenters MetricClosedSmallCover
  LipschitzUP CenteredBallRelations NormDifferentialUP ApproximateDifferentialUP ApproximateDifferential ApproximateDifferentialExtension
  ApproximateToOrdinaryDifferential LipschitzRestrictionDifferentiability
  PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  DensityMeasurableSets MeasureDensityPoints MeasureSetDensity LocalZeroDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [lipschitz_centers_differentiable_almost]:
    the last paragraph of Federer 3.1.9, p. 218,
    for a fixed C_j. The domain B and its representative f
    need not be globally measurable. *)
Theorem lipschitz_centers_differentiable_almost (R : realType) m n
    (B : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (f : inner_metric_space (@euclidean_inner_productP R m.+1)->
      inner_metric_space (@euclidean_inner_productP R n)) (M r : R) :
  0<M -> 0<r ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m.+1)
    (metric_local_lipschitz_centers B f M r)
    [set a | norm_differentiable_at
      (inner_norm (@euclidean_inner_productP R m.+1))
      (inner_norm (@euclidean_inner_productP R n)) B f a].
Proof.
move=> hM hr.
pose X := inner_metric_space (@euclidean_inner_productP R m.+1).
pose mu := @euclidean_lebesgue_measure R m.+1.
pose hm := euclidean_lebesgue_is_measure R m.+1.
pose C := metric_local_lipschitz_centers B f M r.
pose P := [set a | norm_differentiable_at
  (inner_norm (@euclidean_inner_productP R m.+1))
  (inner_norm (@euclidean_inner_productP R n)) B f a].
have hC : closed C := metric_local_lipschitz_centers_closed (ltW hM) hr.
have [D [hDc hDd]] := euclidean_metric_separable R m.+1.
have hr2 : 0<r/2 by rewrite divr_gt0 // ltr0n.
have [F [hF hcover]] := separable_closed_small_cover_allow_empty
  hDc hDd hC hr2.
have hpiece k : measure_almost_everywhere_on mu (F k) P.
  have [hFk [hsub hdiam]] := hF k.
  have hFm : measure_measurable mu (F k).
    apply: euclidean_borel_measurable; exact: closed_borel_set hFk.
  have hLip := @metric_local_lipschitz_centers_small_piece R
    [the metricType R of X]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
    B (F k) f M r hM hsub.
  have hLipF : is_metric_lipschitz (F k) f.
    apply: hLip=> x y hx hy; apply: le_lt_trans (hdiam x y hx hy) _; lra.
  have ha := (measure_almost_everywhere_on_implication _ _ _).1 (federer_3_1_7 hFm hLipF).
  have hd := (density_complement_zero_points_conclusions (F k)
    (euclidean_approximate_context R m.+1)).2.2.2.1 hFm.
  have hd' := (measure_almost_everywhere_on_implication _ _ _).1 hd.
  apply: (measure_almost_everywhere_on_implication _ _ _).2.
  apply: (measure_almost_everywhere_mono hm _
    (measure_almost_everywhere_and hm ha hd'))=> a [ha0 hd0] hka.
  have [L [hL _]] := ha0 hka.
  have hca := hsub a hka.
  have hdenC : partial_function_graph
      (measure_set_density mu
        (@centered_closed_ball_relation R [the metricType R of X]) (~` C)) a 0%E.
    apply: (@local_zero_density_mono R [the metricType R of X] mu _
      (~` C) (~` F k) setT a
      (euclidean_approximate_context R m.+1) openT I _ (hd0 hka)).
    by move=> x _ hn hx; apply: hn; exact: hsub x hx.
  have happrox : has_approximate_differential
      (inner_norm (@euclidean_inner_productP R n)) B f a L.
    apply: (approximate_differential_enlarge_domain _ _
      ((approximate_differential_graph
        (inner_norm_real_norm (@euclidean_inner_productP R n))
        (F k) f a L).1 hL)).
    + by move=> x hx; exact: (hsub x hx).1.
    + by [].
  exists L; apply: (@federer_3_1_5 R m.+1 n B C f r M a L).
  + by move=> x hx; exact: hx.1.
  + exact hr.
  + exact hM.
  + move=> z hz x hx.
    have hdist : mdist (z : X) x<r.
      by rewrite inner_metric_distanceE -opprB inner_normN.
    have [hxB hbound] := hz.2 x hdist; split=> //.
  + exact hca.
  + exact hdenC.
  + exact happrox.
have hall : measure_almost_everywhere mu
    (\bigcap_k [set a | F k a -> P a]).
  apply: (measure_almost_everywhere_countable hm); first exact: countableP.
  move=> k _; exact: (measure_almost_everywhere_on_implication _ _ _).1 (hpiece k).
apply: (measure_almost_everywhere_on_implication _ _ _).2.
apply: (measure_almost_everywhere_mono hm _ hall)=> a hall0 hca.
change (C a) in hca.
rewrite hcover in hca; have [k _ hka] := hca.
exact: hall0 k Logic.I hka.
Qed.
