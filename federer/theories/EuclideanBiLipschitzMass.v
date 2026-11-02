(** Federer (1969), 3.2.17, p. 254:
    compare image Hausdorff mass with Euclidean
    source mass in the two concentric balls.
    The estimates use the actual domain K,
    including nonmeasurable and infinite-mass domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  EuclideanLebesgueDimensions EuclideanBallVolume EuclideanClosedBallVolume
  MeasureUP MeasureBasic MeasureRestriction MetricClosedBalls HausdorffMeasure
  EuclideanHausdorffLebesgue MetricBiLipschitzUP MetricBiLipschitzBalls MetricBiLipschitzHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_bilipschitz_inner_ball_mass]:
    the lower mass comparison in Federer
    3.2.17, p. 254, before division
    by the positive ball-volume factors. *)
Theorem euclidean_bilipschitz_inner_ball_mass (R : realType) m n
    (K : set (inner_metric_space (@euclidean_inner_productP R m)))
    (psi : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (lambda : R) a r :
  is_metric_bilipschitz_bound K psi lambda -> (0<lambda)%R -> K a ->
  euclidean_lebesgue_measure m (K `&` metric_closed_ball a (r/lambda)%R) <=
    (lambda^+m)%:E * @hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m
      ((psi @` K) `&` metric_closed_ball (psi a) r).
Proof.
move=> hB hLam ha.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose A := K `&` metric_closed_ball a (r/lambda)%R.
have hAK : A `<=` K by move=> x hx; exact hx.1.
have hb := (@metric_bilipschitz_hausdorff_bounds R X Y K psi lambda a m A hB hAK).2.
rewrite (euclidean_hausdorff_spherical_lebesgue A).1 in hb.
have hPow : (0<=(lambda^+m)%R%:E)%E.
  rewrite lee_fin; exact: (exprn_ge0 m (ltW hLam)).
have hImageMass : @hausdorff_measure R Y m (psi @` A)<=
    @hausdorff_measure R Y m ((psi @` K) `&` metric_closed_ball (psi a) r).
  exact (@measure_mono R Y (@hausdorff_measure R Y m) (@hausdorff_measure_is_measure R Y m)
    (psi @` A) ((psi @` K) `&` metric_closed_ball (psi a) r)
    (@metric_bilipschitz_inner_ball_image R X Y K psi lambda a r hB hLam ha)).
exact: (le_trans hb (lee_wpmul2l hPow hImageMass)).
Qed.

(** Source for [euclidean_bilipschitz_outer_ball_mass]:
    the upper mass comparison in Federer
    3.2.17, p. 254. The ball-volume
    identity gives the factor lambda^(2m). *)
Theorem euclidean_bilipschitz_outer_ball_mass (R : realType) m n
    (K : set (inner_metric_space (@euclidean_inner_productP R m)))
    (psi : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (lambda : R) a (r : R) :
  is_metric_bilipschitz_bound K psi lambda -> (0<lambda)%R -> K a -> (0<r)%R ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
    ((psi @` K) `&` metric_closed_ball (psi a) r) <=
    (lambda^+(m+m)*(euclidean_unit_ball_volume R m*r^+m))%R%:E.
Proof.
move=> hB hLam ha hr.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose A := K `&` metric_closed_ball a (lambda*r)%R.
have hAK : A `<=` K by move=> x hx; exact hx.1.
have hmono := @measure_mono R Y (@hausdorff_measure R Y m)
  (@hausdorff_measure_is_measure R Y m) _ _
  (@metric_bilipschitz_outer_ball_preimage R X Y K psi lambda a r hB ha).
have hb := (@metric_bilipschitz_hausdorff_bounds R X Y K psi lambda a m A hB hAK).1.
rewrite (euclidean_hausdorff_spherical_lebesgue A).1 in hb.
have hA : euclidean_lebesgue_measure m A<=
    (euclidean_unit_ball_volume R m*(lambda*r)^+m)%R%:E.
  apply: (le_trans (@measure_mono R X _ (euclidean_lebesgue_is_measure R m)
    A (metric_closed_ball a (lambda*r)%R) (fun x hx=>hx.2)) _).
  rewrite (euclidean_closed_ball_normalized_volume a (mulr_ge0 (ltW hLam) (ltW hr))).
  exact: lexx.
have hPow : (0<=(lambda^+m)%R%:E)%E by rewrite lee_fin exprn_ge0 // ltW.
have hscale := lee_wpmul2l hPow hA.
have hh := le_trans hmono (le_trans hb hscale).
rewrite -EFinM in hh.
have hEq : (lambda^+m*(euclidean_unit_ball_volume R m*(lambda*r)^+m)=
    lambda^+(m+m)*(euclidean_unit_ball_volume R m*r^+m))%R.
  rewrite exprMn exprD; ring.
by rewrite hEq in hh.
Qed.
