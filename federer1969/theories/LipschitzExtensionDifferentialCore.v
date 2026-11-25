(** Federer (1969), 3.2.18, p. 255:
    after extending a near-isometric restriction,
    remove the null exceptional sets of
    Rademacher and source density. On the
    retained measurable core the extension has
    the prescribed differential bounds at every point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RealNormUP HilbertFormCompactness NormDifferentialUP PartialFunctionUP
  LipschitzUP LipschitzBasic Rademacher EuclideanLebesgueDimensions EuclideanApproximateContext
  CenteredBallRelations MeasureSetDensity MeasureDensityPoints DensityMeasurableSets
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure
  EuclideanDifferentialsDensityAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_extension_uniform_differential_core]:
    the passage from 3.2.2 to the
    globally extended charts in Federer
    3.2.18, p. 255. Both actual
    differentiability and the printed two norm
    bounds hold at every point of
    the retained core, whose loss is null. *)
Theorem lipschitz_extension_uniform_differential_core (R : realType) m n
    (S : set (R_n R m)) (h g : R_n R m -> R_n R n) (lambda : R) :
  measure_measurable (@euclidean_lebesgue_measure R m) S ->
  @is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) setT g lambda ->
  (forall x, S x -> h x=g x) ->
  (forall a, S a -> exists D : Hom (R_n R m) (R_n R n),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT h a D /\
    forall v, lambda^-1*inner_norm (@euclidean_inner_productP R m) v<=
      inner_norm (@euclidean_inner_productP R n) (D v) /\
      inner_norm (@euclidean_inner_productP R n) (D v)<=
        lambda*inner_norm (@euclidean_inner_productP R m) v) ->
  exists T : set (R_n R m), T `<=` S /\
    measure_measurable (@euclidean_lebesgue_measure R m) T /\
    euclidean_lebesgue_measure m (S `\` T)=0%E /\
    forall a, T a -> exists D : Hom (R_n R m) (R_n R n),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT g a D /\
      forall v, lambda^-1*inner_norm (@euclidean_inner_productP R m) v<=
        inner_norm (@euclidean_inner_productP R n) (D v) /\
        inner_norm (@euclidean_inner_productP R n) (D v)<=
          lambda*inner_norm (@euclidean_inner_productP R m) v.
Proof.
move=> hS hBound hAgree hDeriv.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose mu := @euclidean_lebesgue_measure R m.
pose V := @centered_closed_ball_relation R [the metricType R of X].
pose Q := measure_density_complement_zero_points mu V S.
pose Dg := norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
  (inner_norm (@euclidean_inner_productP R n)) setT g.
pose T := S `&` (Q `&` Dg).
have hm := euclidean_lebesgue_is_measure R m.
have hQC := @density_complement_zero_points_conclusions R [the metricType R of X] mu V S (euclidean_approximate_context R m).
have hQm : measure_measurable mu Q := hQC.1.
have hQnull : mu (S `\` Q)=0%E := hQC.2.2.2.1 hS.
have hDiffNull : mu (~` Dg)=0%E := federer_3_1_6 (metric_lipschitz_of_bound hBound).
have hDgm : measure_measurable mu Dg.
  have hh := measure_measurable_complement (measure_null_measurable hm hDiffNull).
  by rewrite setCK in hh.
have hTm : measure_measurable mu T.
  exact: (measure_measurable_intersection hm hS (measure_measurable_intersection hm hQm hDgm)).
have hBadNull := measure_null_union hm hQnull hDiffNull.
have hLoss : mu (S `\` T)=0%E.
  apply: (measure_null_subset hm _ hBadNull)=> x [hx hn].
  case: (pselect (Q x))=> hqx; last by left; split.
  right; move=> hdx; apply: hn; by split=> //; split.
exists T; split; first by move=> x hx; exact hx.1.
split; first exact hTm.
split; first exact hLoss.
move=> a [haS [haQ [E hE]]].
have [D [hD hEst]] := hDeriv a haS.
have hDE := @euclidean_differentials_agree_on_full_density R m (R_n R n)
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) S h g a D E hAgree haQ hD hE.
exists D; split=> //; by rewrite hDE.
Qed.
