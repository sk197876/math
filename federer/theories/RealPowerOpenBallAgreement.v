(** Federer (1969), 2.10.2(2), p. 171: Euclidean spherical measure is
    unchanged by replacing closed balls by open balls. First prove the
    comparison under explicit ball-diameter laws, then instantiate the laws
    for every Euclidean dimension, including zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost
  SphericalOpenBallUP OpenBallScaleBound RealPowerCoverVariants RealPowerOpenBallScale
  MetricRealPowerCost MetricRealPowerMeasure MetricRealPowerMeasureUP MetricBallDiameterUP MetricClosedBalls
  MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws
  MetricScaleMeasureBound CaratheodoryLimitUP CaratheodoryBorelRegular
  CaratheodoryFamilyReplacement GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBallDiameterFactor NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_open_ball_agreement_from_diameters]:
    supporting general comparison for Federer 2.10.2(2),
    p. 171. The supplied factor laws are geometric
    hypotheses, independently proved in the Euclidean
    corollary. The factor may be zero. *)
Theorem real_power_open_ball_agreement_from_diameters (R : realType) (X : metricType R)
    (c : R) (hc : @is_metric_ball_diameter_factor R X c) (coef p : R) (hcoef : (0<coef)%R) (hp : (0<=p)%R) (A : set X) :
  @spherical_metric_real_power_measure R X coef p A=@open_ball_metric_real_power_measure R X coef p A.
Proof.
have hs := @spherical_metric_real_power_specification R X coef p.
have ho := @open_ball_metric_real_power_specification R X coef p.
have hlo : @spherical_metric_real_power_measure R X coef p A<=@open_ball_metric_real_power_measure R X coef p A.
  apply: (@caratheodory_family_replacement R X
    (@positive_open_metric_balls R X) (@positive_closed_metric_balls R X)
    (fun j => val j) (fun j => val j)
    (fun j => metric_real_diameter_cost coef p (val j))
    (fun j => metric_real_diameter_cost coef p (val j)) _ _ ho hs _ _ A).
  - move=> j; exact: metric_real_diameter_cost_ge0 (ltW hcoef).
  - move=> j; have [a [r [hr hA]]] := set_valP j.
    have he : val j=[set x | (mdist a x<r)%R].
      apply/seteqP; split=> x hx; [exact: (hA x).1 hx|exact: (hA x).2 hx].
    pose k : @positive_closed_metric_balls R X :=
      @exist _ (fun B : set X => B \in [set B | @is_positive_metric_closed_ball R X B])
        (metric_closed_ball a r) (mem_set (@positive_closed_ball_satisfies_laws R X a r hr)).
    exists k; split.
    + move=> x hx; exact: ltW ((hA x).1 hx).
    + split.
      * change (extended_metric_diameter (metric_closed_ball a r)<=extended_metric_diameter (val j)).
        by rewrite he (closed_ball_diameter_factor hc a hr) (open_ball_diameter_factor hc a hr).
      * change (metric_real_diameter_cost coef p (metric_closed_ball a r)<=metric_real_diameter_cost coef p (val j)).
        by rewrite /metric_real_diameter_cost he (closed_ball_diameter_factor hc a hr) (open_ball_diameter_factor hc a hr).
apply/eqP; rewrite eq_le hlo /=.
apply: (caratheodory_limit_least ho)=> tau nu htau hnu.
have [n hnt] := reciprocal_metric_cutoffs_cofinal htau.
pose t : R := (((n.+1)%:R)^-1)%R.
have ht : (0<t)%R by rewrite /t invr_gt0 ltr0n.
pose psi := metric_scale_envelope (fun j : @positive_open_metric_balls R X => val j)
  (fun j => metric_real_diameter_cost coef p (val j)) t%:E.
have hpsi := @metric_scale_envelope_specification R X (@positive_open_metric_balls R X)
  (fun j => val j) (fun j => metric_real_diameter_cost coef p (val j)) t%:E.
have hpsi_measure := @metric_scale_envelope_measure R X (@positive_open_metric_balls R X)
  (fun j => val j) (fun j => metric_real_diameter_cost coef p (val j)) t%:E
  (fun j => metric_real_diameter_cost_ge0 p (val j) (ltW hcoef)).
pose phi := metric_scale_envelope (fun j : @positive_closed_metric_balls R X => val j)
  (fun j => metric_real_diameter_cost coef p (val j)) ((t/2)%R%:E).
have hphi := @metric_scale_envelope_specification R X (@positive_closed_metric_balls R X)
  (fun j => val j) (fun j => metric_real_diameter_cost coef p (val j)) ((t/2)%R%:E).
have htt : ((t/2)%R%:E<t%:E).
  rewrite lte_fin; have h2 : (0<(2:R))%R by rewrite ltr0n.
  rewrite (ltr_pdivrMr _ _ h2); lra.
have hgen (j : @positive_closed_metric_balls R X) :
    extended_metric_diameter (val j)<=(t/2)%R%:E -> psi (val j)<=metric_real_diameter_cost coef p (val j).
  move=> hj; exact (@open_ball_real_power_closed_generator_bound R X c hc coef p hcoef hp psi (val j) t
    hpsi (set_valP j) (le_lt_trans hj htt)).
apply: le_trans (@metric_scale_envelope_antitone_cutoff R X (@positive_open_metric_balls R X)
  (fun j => val j) (fun j => metric_real_diameter_cost coef p (val j)) t%:E tau psi nu hpsi hnu hnt A) _.
apply: le_trans (@measure_bounded_by_metric_scale_envelope R X (@positive_closed_metric_balls R X)
  (fun j => val j) (fun j => metric_real_diameter_cost coef p (val j)) ((t/2)%R%:E)
  phi psi hphi hpsi_measure hgen A) _.
apply: (@caratheodory_limit_upper R X (@positive_closed_metric_balls R X)
  (fun j => val j) (fun j => metric_real_diameter_cost coef p (val j)) _ hs A ((t/2)%R%:E) phi _ hphi).
by rewrite lte_fin divr_gt0 // ltr0n.
Qed.

(** Source for [euclidean_metric_real_power_open_ball_equality]:
    direct Euclidean open-ball alternative in Federer
    2.10.2(2), p. 171. All dimensions, nonnegative real measure
    degrees, arbitrary target sets and the positive-radius
    convention are retained. *)
Theorem euclidean_metric_real_power_open_ball_equality (R : realType) (n : nat) (coef p : R) (hcoef : (0<coef)%R) (hp : (0<=p)%R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @spherical_metric_real_power_measure R (inner_metric_space (@euclidean_inner_productP R n)) coef p A=
    @open_ball_metric_real_power_measure R (inner_metric_space (@euclidean_inner_productP R n)) coef p A.
Proof.
exact (@real_power_open_ball_agreement_from_diameters R
  (inner_metric_space (@euclidean_inner_productP R n)) _
  (@euclidean_ball_diameter_factor R n) coef p hcoef hp A).
Qed.
