(** Federer (1969), 3.3.15, p. 299: open strict superlevels
    of the original normalized-ball supremum at a fixed positive cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
(** lra is used only for finite real radius arithmetic. *)
From Federer Require Import RealMetricBackground MetricClosedBalls MetricDensities MetricDensityNumericalBounds
  EuclideanBallVolume PolynomialStrictNeighbourhood ExtendedRealOrderTopology MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_density_cutoff_superlevel_open]: supporting
    the Borel upper-density level sets in Federer 3.3.15, p. 299,
    for the literal positive-radius normalization of 2.10.19, p. 181.
    Any original strict normalized-ball witness remains a witness at
    nearby centres after a small radius enlargement. Polynomial
    continuity and the actual ball inclusion prove this for every
    measure, all natural degrees and finite or infinite original ball masses. *)
Lemma metric_density_cutoff_superlevel_open (R:realType) (X:metricType R) m
    (mu:set X->\bar R) (delta b:R):
  is_measure mu ->open [set a:X|exists r:R,(0<r<delta) /\
    (b%:E<metric_ball_density m mu a r)%E].
Proof.
move=>hMu; rewrite openE=>a [r [hr hCost]].
have hr0:0<r:=(andP hr).1.
have hrDelta:r<delta:=(andP hr).2.
have hMass:=@metric_ball_density_value_large R X m mu a r b hr0 hCost.
have [q [hLower hUpper]]:=@extended_rationals_order_dense R _ _ hMass.
have hLowerReal:b*(euclidean_unit_ball_volume R m*r^+m)<ratr q.
  by move:hLower; rewrite lte_fin.
have hPolynomial:(b*euclidean_unit_ball_volume R m)*r^+m<ratr q.
  by rewrite -mulrA.
have [d [hd hStable]]:=@polynomial_strict_upper_neighbourhood R
  (b*euclidean_unit_ball_volume R m) r (ratr q) m hPolynomial.
pose e:=Num.min (delta-r) d/2.
have hGap:0<delta-r by rewrite subr_gt0.
have hMin:0<Num.min (delta-r) d by rewrite lt_min hGap hd.
have he:0<e by rewrite /e divr_gt0 // ltr0n.
have heMin:e<Num.min (delta-r) d by rewrite /e; lra.
have hMinGap:Num.min (delta-r) d<=delta-r by rewrite ge_min lexx.
have hMinD:Num.min (delta-r) d<=d by rewrite ge_min lexx orbT.
have heGap:e<delta-r:=lt_le_trans heMin hMinGap.
have heD:e<d:=lt_le_trans heMin hMinD.
have hNewRadius:0<r+e<delta by apply/andP; split; lra.
have hDistance:mdist (r:real_line_metric R) (r+e)=e.
  rewrite real_line_metric_distanceE opprD addrA subrr add0r normrN.
  by rewrite (ger0_norm (ltW he)).
have hNewPolynomial:=hStable (r+e) (ltac:(by rewrite hDistance)).
rewrite -mulrA in hNewPolynomial.
apply:(metricType_numDomainType.nbhs_mdistP a _).2.
exists e; first exact:he.
move=>x hx; exists (r+e); split; first exact:hNewRadius.
have hBall:metric_closed_ball a r `<=` metric_closed_ball x (r+e).
  move=>z hz; have hTri:=metric_triangle x a z.
  rewrite (metric_sym x a) in hTri.
  have hSum:=lerD (ltW hx) hz; rewrite [(e+r)%R]addrC in hSum.
  exact:le_trans hTri hSum.
have hNewMass:(((b*(euclidean_unit_ball_volume R m*(r+e)^+m))%R)%:E<
    mu (metric_closed_ball x (r+e)))%E.
  apply:lt_le_trans _ (@measure_mono R X mu hMu _ _ hBall).
  apply:lt_trans _ hUpper.
  by rewrite lte_fin.
pose denominator:=euclidean_unit_ball_volume R m*(r+e)^+m.
have hDenominator:0<denominator:=metric_ball_density_denominator_positive m (andP hNewRadius).1.
rewrite /metric_ball_density -/denominator inver (gt_eqF hDenominator) muleC
  lte_pdivlMl // -EFinM mulrC.
exact:hNewMass.
Qed.
