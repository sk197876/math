(** Federer (1969), 3.3.17, p. 300: an actual finite
    positive atom has infinite positive-degree upper density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import PointMassMeasure MeasureRestriction MetricClosedBalls MetricDensities
  EuclideanBallVolume PositiveRadiusUnboundedValues PositiveRadiusLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [point_mass_upper_degree_one_density_infinite]:
    actual infinite-density regression support for Federer
    3.3.17, p. 300. The original unit atom has closed-ball
    mass one at EVERY positive radius. The actual normalized
    degree-one quotient is 1/(2r); arbitrarily large values
    occur at arbitrarily small ORIGINAL radii. No infinity
    value or limiting profile is assumed. *)
Lemma point_mass_upper_degree_one_density_infinite (R:realType) (X:metricType R) (a:X):
  upper_metric_density 1 (measure_restrict (point_mass R a) [set a]) a=+oo.
Proof.
rewrite /upper_metric_density; apply:positive_radius_upper_infinite_from_spikes=>b d hd.
pose c:=(`|b|+1)%R.
have hC:(0<c)%R by rewrite /c; have h:=normr_ge0 b; lra.
have hTwoC:(0<2*c)%R by rewrite mulr_gt0 // ltr0n.
pose r:=(Num.min (d/2) (2*c)^-1)%R.
have hDHalf:(0<d/2)%R by rewrite divr_gt0 // ltr0n.
have hR:(0<r)%R by rewrite /r lt_min hDHalf invr_gt0.
have hRHalf:(r<=d/2)%R by rewrite /r ge_min lexx.
have hRInv:(r<=(2*c)^-1)%R by rewrite /r ge_min lexx orbT.
have hRD:(r<d)%R.
  have hHalf:(d/2<d)%R by lra.
  exact:le_lt_trans hRHalf hHalf.
have hProduct:(2*c*r<= 1)%R.
  have h:=ler_wpM2l (ltW hTwoC) hRInv.
  by rewrite mulfV ?gt_eqF in h.
have hDen:(0<2*r)%R by rewrite mulr_gt0 // ltr0n.
have hCompare:(c<= 1/(2*r))%R.
  rewrite ler_pdivlMr //.
  have hReorder:(c*(2*r)= 2*c*r)%R by rewrite mulrCA mulrA.
  by rewrite hReorder.
have hB:(b<=c)%R by rewrite /c; have h:=ler_norm b; lra.
exists r; split; first by apply/andP; split.
have hMass:measure_restrict (point_mass R a) [set a] (metric_closed_ball a r)= 1.
  apply:point_mass_in; split; first by [].
  by rewrite /metric_closed_ball /= mdistxx; exact:ltW hR.
rewrite /metric_ball_density hMass euclidean_unit_ball_volume1 expr1 mul1e inver (gt_eqF hDen).
rewrite lee_fin -div1r; exact:le_trans hB hCompare.
Qed.
