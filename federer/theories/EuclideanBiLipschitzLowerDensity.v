(** Federer (1969), 3.2.17, p. 254:
    the lower density estimate uses full
    source density, the inner ball inclusion
    and the inverse Lipschitz mass bound.
    Complements need not be measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume EuclideanClosedBallVolume PartialFunctionUP CenteredBallRelations
  MeasureSetDensity MeasureUP MeasureBasic MeasureSplit MeasureRestriction
  MetricClosedBalls MetricDensities MetricDensityZeroPowerMass EuclideanMetricZeroDensity
  PositiveRadiusLowerApproximation MetricBiLipschitzUP EuclideanBiLipschitzMass HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_bilipschitz_lower_density]:
    Theta_*^m(H^m restricted psi(K),psi(a))
    at least lambda^(-2m), Federer 3.2.17,
    p. 254. The proof uses only
    zero density of the source complement and
    exact positive Euclidean ball volumes. *)
Theorem euclidean_bilipschitz_lower_density (R : realType) m n
    (K : set (inner_metric_space (@euclidean_inner_productP R m)))
    (psi : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (lambda : R) a :
  is_metric_bilipschitz_bound K psi lambda -> 0<lambda -> K a ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) (~` K)) a 0%E ->
  (((lambda^+(m+m))^-1)%R%:E <=
    lower_metric_density m (measure_restrict
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (psi @` K)) (psi a))%E.
Proof.
move=> hB hLam ha hFull.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.
pose nu := measure_restrict (@hausdorff_measure R Y m) (psi @` K).
pose alpha := euclidean_unit_ball_volume R m.
pose p := lambda^+m.
pose C := lambda^+(m+m).
have hAlpha : 0<alpha := (euclidean_unit_ball_volumeE R m).2.
have hp : 0<p by rewrite /p exprn_gt0.
have hC : 0<C by rewrite /C exprn_gt0.
have hCC : C=p* p by rewrite /C /p exprD.
have hm := euclidean_lebesgue_is_measure R m.
have hn := measure_restrict_is_measure (@hausdorff_measure_is_measure R Y m) (psi @` K).
have hZero := euclidean_relative_zero_metric_zero_density hFull.
apply: (@positive_radius_lower_scaled_one_bound R _ C^-1 _ _).
  1: by rewrite invr_gt0.
move=> e he.
have hE : 0<e*alpha := mulr_gt0 he hAlpha.
have [d [hd hs]] := metric_zero_density_small_power_mass hm hZero hE.
exists (lambda*d); split; first exact: mulr_gt0 hLam hd.
move=> r /andP [hr hrd].
pose t := r/lambda.
have ht : 0<t by rewrite /t divr_gt0.
have htd : t<=d by apply: ltW; move: hrd; rewrite /t ltr_pdivrMr // mulrC.
have hRad : 0<t<=d by apply/andP; split.
have hBad := hs t hRad.
have hGood := @euclidean_bilipschitz_inner_ball_mass R m n K psi lambda a r hB hLam ha.
have hCover : (mu (metric_closed_ball a t)<=
    mu (K `&` metric_closed_ball a t)+mu ((~` K) `&` metric_closed_ball a t))%E.
  apply: (measure_binary_cover hm _)=> x hx.
  case: (pselect (K x))=> hK; [left|right]; by split.
have hBound := le_trans hCover (leeD hGood hBad).
have hUpper := euclidean_bilipschitz_outer_ball_mass hB hLam ha hr.
have hFinite : nu (metric_closed_ball (psi a) r) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hn _)).
  exact: le_lt_trans hUpper (ltry _).
pose v := fine (nu (metric_closed_ball (psi a) r)).
have hv : nu (metric_closed_ball (psi a) r)=v%:E := esym (fineK hFinite).
change (is_true (mu (metric_closed_ball a t)<=
  p%:E*nu (metric_closed_ball (psi a) r)+((e*alpha)*t^+m)%R%:E)%E) in hBound.
rewrite /mu (euclidean_closed_ball_normalized_volume a (ltW ht)) -/alpha
  hv -EFinM -EFinD lee_fin in hBound.
have hPower : t^+m* p=r^+m.
  rewrite /t /p exprMn exprVn -mulrA.
  by rewrite mulVf ?gt_eqF ?exprn_gt0 // mulr1.
have hScale := ler_wpM2l (ltW hp) hBound.
have hAlg : (1-e)*(alpha*r^+m)<=C*v by rewrite hCC; nra.
pose den := alpha*r^+m.
have hDen : 0<den by rewrite /den mulr_gt0 // exprn_gt0.
have hNative : (1-e)/C<=v/den.
  rewrite ler_pdivrMr // mulrAC ler_pdivlMr //.
  rewrite /den [v*C]mulrC; exact hAlg.
change (is_true (((1-e)*C^-1)%R%:E <= metric_ball_density m nu (psi a) r)%E).
rewrite /metric_ball_density hv inver (gt_eqF hDen) -EFinM lee_fin.
exact hNative.
Qed.
