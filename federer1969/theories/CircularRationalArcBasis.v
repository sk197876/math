(** Federer (1969), 3.3.19, p. 305: rational
    parameter arcs test density in the actual unit circle,
    including the repeated principal-period endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed CircularUnitVectors
  CircularPrincipalParameter CircularUnitCurve CircularDiscRadialIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Basis.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [circular_rational_arc_ball_basis]: every
    positive-radius neighbourhood of every actual unit vector
    contains a positive rational parameter arc with endpoints
    between zero and 2pi. This discharges the common countable
    density test in 3.3.19, p. 305. Even the point
    exp(0i) is approximated from inside the original period. *)
Theorem circular_rational_arc_ball_basis (u:E) (eps:R):
  inner_norm (@euclidean_inner_productP R 2) u= 1 ->0<eps ->
  exists a b:rat,0<=(ratr a:R) /\(ratr a<ratr b:>R) /\(ratr b<=2* p:>R) /\
    forall x,circular_parameter_arc (ratr a) (ratr b) x ->mdist u x<eps.
Proof.
move=>hu hEps.
have hp:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have [t [ht0 [htP hT]]]:= @circular_principal_parameter_exists R u hu.
have [c [hc0 [hcP hNear]]]:exists c:R,0<c /\c<2* p /\mdist (circular_unit_vector c) u<eps/2.
  case:(eqVneq t 0)=>hZero.
  - pose c:R:= Num.min (eps/8) p.
    have hc:0<c by rewrite /c lt_min;apply/andP;split;[lra|exact hp].
    have hcE:c<=eps/8 by rewrite /c ge_min lexx.
    have hcPi:c<=p by rewrite /c ge_min lexx orbT.
    exists c;split=>//;split;first by lra.
    have hDistance:= @circular_unit_vector_lipschitz R c 0.
    rewrite hZero in hT;rewrite hT subr0 (ger0_norm (ltW hc)) in hDistance.
    lra.
  - have ht:0<t by rewrite lt_neqAle eq_sym hZero ht0.
    exists t;split=>//;split=>//.
    rewrite hT mdistxx;lra.
pose e:R:= Num.min c (Num.min (2* p-c) (eps/4)).
have he:0<e by rewrite /e !lt_min;apply/andP;split;first exact hc0;apply/andP;split;lra.
have heC:e<=c by rewrite /e ge_min lexx.
have heInner:e<=Num.min (2* p-c) (eps/4) by rewrite /e ge_min lexx orbT.
have hePi:e<=2* p-c.
  apply:(le_trans heInner);by rewrite ge_min lexx.
have heEps:e<=eps/4.
  apply:(le_trans heInner);by rewrite ge_min lexx orbT.
pose d:R:= e/2.
have hd:0<d by rewrite /d;lra.
have hLeft:c-d<c by lra.
have hRight:c<c+d by lra.
have [a /andP[haLeft haC]]:= rat_in_itvoo hLeft.
have [b /andP[hbC hbRight]]:= rat_in_itvoo hRight.
move:haLeft haC hbC hbRight;rewrite !bnd_simp =>haLeft haC hbC hbRight.
exists a,b;split;first by rewrite /d in haLeft;lra.
split;first by lra.
split;first by rewrite /d in hbRight;lra.
move=>x [s [hsLeft hsRight] <-].
have hDifference:`|s-c|<d by rewrite ltr_norml;apply/andP;split;lra.
have hDistance:= @circular_unit_vector_lipschitz R s c.
have hTriangle:= metric_triangle u (circular_unit_vector c) (circular_unit_vector s).
rewrite (metric_sym u (circular_unit_vector c))
  (metric_sym (circular_unit_vector c) (circular_unit_vector s)) in hTriangle.
rewrite /d in hDifference;lra.
Qed.
End Basis.
