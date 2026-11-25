(** Federer (1969), 3.3.19, p. 303:
    the single-finest-disc alternative has original
    first gauge at least pi times its radius.
    Derive the constant from actual unit-ball
    geometry and the existing Cauchy normalization. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  CoveringFamilyUP MetricClosedBalls CircularTrigonometrySealed CircularUnitCircleLength
  EuclideanBallVolume UnitBallIntrinsicVolume EuclideanUnitBallProjection ProjectionBeta
  IntegralGeometricGauge IntegralGeometricSimilarityGauge IntegralGeometricGaugeSubsetOrder
  SuslinSetUP BorelClosedProjection TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Discs.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation N:=(inner_norm hE).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation q:=(@integral_geometric_gauge R 2 1 (leqnSn 1) 1).

(** Source for [planar_unit_disc_first_gauge]:
    zeta_1 of the actual unit disc is pi,
    supporting the first alternative of 3.3.19,
    p. 303. Actual alpha(2)= pi and
    the proved Cauchy coefficient give the exact
    original beta normalization. *)
Lemma planar_unit_disc_first_gauge:q [set x:E|N x<1]= p%:E.
Proof.
rewrite (@unit_ball_integral_geometric_gauge R 2 1 (leqnSn 1)) (@euclidean_unit_ball_volume1 R).
have hCoefficient:= @unit_ball_cauchy_coefficient R 1.
rewrite (@circular_half_period_planar_volume R) (@euclidean_unit_ball_volume1 R) in hCoefficient.
pose beta:= @projection_beta R 2 1 (leqnSn 1) 1.
have hPositive:0<beta:= @projection_beta_positive R 2 1 (leqnSn 1) 1 (lexx _).
have hNonzero:beta!=0 by rewrite gt_eqF.
have hValue:2/beta= p.
  have hCancel:(2/beta)* beta= 2 by rewrite divfK.
  change (2* p* beta= 2*2) in hCoefficient;nra.
by rewrite -/beta hValue.
Qed.

(** Source for [planar_positive_affine_unit_disc]:
    the original centre-radius disc is exactly the
    positive affine image of the actual unit disc,
    supporting 3.3.19, p. 303. Both
    inclusions use the actual original Euclidean norm. *)
Lemma planar_positive_affine_unit_disc (z:E) (r:R):0<r ->
  (fun x:E=>z+r*:x) @` [set x:E|N x<1]= metric_open_ball z r.
Proof.
move=>hr;have hrN:r!=0 by rewrite gt_eqF.
have hInv:0<r^-1 by rewrite invr_gt0.
apply/seteqP;split=>y.
- move=>[x hx <-].
  change (is_true (N (z-(z+r*:x))<r)).
  have hDifference:z-(z+r*:x)= -(r*:x) by rewrite opprD addrA subrr add0r.
  rewrite hDifference inner_normN inner_normZ (ger0_norm (ltW hr)).
  by rewrite -[ltRHS]mulr1 ltr_pM2l.
- move=>hy.
  pose x:E:= r^-1*: (y-z).
  exists x.
  + change (is_true (N x<1)).
    rewrite /x inner_normZ (ger0_norm (ltW hInv)).
    have hDistance:N (y-z)= mdist z y by rewrite metric_sym inner_metric_distanceE.
    rewrite hDistance mulrC ltr_pdivrMr // mul1r;exact hy.
  + by rewrite /x scalerA mulfV // scale1r addrC subrK.
Qed.

(** Source for [planar_open_disc_first_gauge]:
    the actual first gauge of a radius-r
    original planar disc is pi r, as
    used in 3.3.19, p. 303.
    The public positive similarity law transports
    the actual unit-disc normalization. *)
Lemma planar_open_disc_first_gauge (z:E) (r:R):0<r ->q (metric_open_ball z r)=(p* r)%:E.
Proof.
move=>hr.
have hOpen:open [set x:E|N x<1]:=(euclidean_unit_ball_convex_bounded R 2).2.1.
rewrite -(@planar_positive_affine_unit_disc z r hr)
  (@integral_geometric_positive_similarity_gauge R 2 1 (leqnSn 1) 1 [set x:E|N x<1] z r
    (lexx _) (metric_borel_suslin (open_borel_set hOpen)) hr)
  planar_unit_disc_first_gauge expr1 -EFinM mulrC;exact:erefl.
Qed.

(** Source for [planar_contained_disc_first_gauge_lower]:
    zeta_1(S)>=pi r whenever original S
    contains an original closed disc of radius r,
    the single-hit alternative in 3.3.19,
    p. 303. Original openness supplies
    Suslin measurability; no projected-volume premise. *)
Theorem planar_contained_disc_first_gauge_lower (z:E) (r:R) (S:set E):
  0<r ->open S ->metric_closed_ball z r `<=` S ->((p*r)%:E<=q S)%E.
Proof.
move=>hr hOpen hInside.
have hSmall:open (metric_open_ball z r):= metric_open_ball_open z r.
rewrite -(@planar_open_disc_first_gauge z r hr).
apply:(@integral_geometric_gauge_subset_order R 2 1 (leqnSn 1) 1 _ _
  (lexx _) (metric_borel_suslin (open_borel_set hSmall)) (metric_borel_suslin (open_borel_set hOpen))).
move=>x hx;apply:hInside;exact:ltW hx.
Qed.
End Discs.
