(** Federer (1969), 3.3.21, p. 309: real-degree lower density, with the normalization of 2.10.19, p. 181. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology ring.
From Federer Require Import MetricClosedBalls MeasureUP MeasureBasic RealPower RealHausdorffNormalisation
  ExtendedRealBounds PositiveRadiusLimits PositiveRadiusLimitBounds PositiveRadiusUnboundedValues MetricDensities
  HausdorffDiameterCost RealPowerNaturalHausdorff EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_metric_ball_density]: the actual real-degree
    density quotient used in 3.3.21, p. 309, following 2.10.19,
    p. 181. The coefficient b=alpha(p)2^(-p) is the actual Euler
    Gamma normalization, so b(2r)^p equals alpha(p)r^p at every
    positive radius. No discretized degree or radius is substituted. *)
Definition real_metric_ball_density (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R) (mu:set X->\bar R) (a:X) (r:R): \bar R:=
  mu (metric_closed_ball a r)/(real_hausdorff_normalisation hp * real_power (2 * r)%R p)%:E.

(** Source for [lower_real_metric_density]: lower real-degree
    density in 3.3.21, p. 309. The already sealed positive-radius
    infima and suprema range over all strictly positive real radii. *)
Definition lower_real_metric_density (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R) (mu:set X->\bar R) (a:X):=
  positive_radius_lower_limit (real_metric_ball_density hp mu a).

(** Source for [real_metric_density_denominator_positive]: supporting
    positivity of the original denominator in 3.3.21, p. 309,
    including real degree zero, at every positive original radius. *)
Lemma real_metric_density_denominator_positive (R:realType) (p r:R) (hp:(0<=p)%R):
  (0<r)%R ->(0<real_hausdorff_normalisation hp * real_power (2 * r) p)%R.
Proof.
move=>hr;apply:mulr_gt0;first exact:real_hausdorff_normalisation_positive.
apply:real_power_strictly_positive;by rewrite mulr_gt0 // ltr0n.
Qed.

(** Source for [real_metric_ball_density_nonnegative]: actual
    nonnegative ball masses give nonnegative real-degree quotients,
    supporting the lower density in 3.3.21, p. 309. *)
Lemma real_metric_ball_density_nonnegative (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R) (mu:set X->\bar R) (a:X) (r:R):
  is_measure mu ->(0<r)%R ->0<=real_metric_ball_density hp mu a r.
Proof.
move=>hMu hr;apply:mule_ge0;first exact:measure_nonnegative hMu _.
rewrite inve_ge0 lee_fin;exact:ltW (real_metric_density_denominator_positive hp hr).
Qed.

(** Source for [real_metric_ball_density_natural]: supporting
    exact agreement with the existing natural-degree density in
    2.10.19, p. 181, as used at the m= 1/2 case of 3.3.21,
    p. 309. All measures and original ball centres are retained. *)
Lemma real_metric_ball_density_natural (R:realType) (X:metricType R) q
    (hp:(0<=q%:R:>R)%R) (mu:set X->\bar R) (a:X) (r:R):
  (0<r)%R ->real_metric_ball_density hp mu a r=metric_ball_density q mu a r.
Proof.
move=>hr;rewrite /real_metric_ball_density /metric_ball_density
  real_hausdorff_normalisation_natural real_power_natural_exponent;last by rewrite mulr_ge0 // ?ler0n ltW.
rewrite /hausdorff_normalisation exprMn.
have hTwo:((2:R)^+q!= 0)%R by rewrite gt_eqF // exprn_gt0 // ltr0n.
have hDen:(euclidean_unit_ball_volume R q/(2:R)^+q * ((2:R)^+q * r^+q))%R=
    (euclidean_unit_ball_volume R q * r^+q)%R.
  field;by rewrite hTwo.
by rewrite hDen.
Qed.

(** Source for [lower_real_metric_density_natural]: actual
    natural-degree lower density agrees exactly with the real-degree
    extension, 3.3.21, p. 309, with 2.10.19, p. 181. Only
    positive radii enter either independently specified limit. *)
Lemma lower_real_metric_density_natural (R:realType) (X:metricType R) q
    (hp:(0<=q%:R:>R)%R) (mu:set X->\bar R) (a:X):
  lower_real_metric_density hp mu a=lower_metric_density q mu a.
Proof.
rewrite /lower_real_metric_density /lower_metric_density /positive_radius_lower_limit.
apply:congr1;apply/seteqP;split=>b [e [he ->]];exists e;split=>//;
  congr (extended_real_inf _);apply/seteqP;split=>y [r [hr ->]];exists r;split=>//;
  by rewrite real_metric_ball_density_natural // (andP hr).1.
Qed.
