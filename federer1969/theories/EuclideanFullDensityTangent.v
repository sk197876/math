(** Federer (1969), 3.2.17, pp. 254–255:
    a Euclidean set with zero-density complement
    has every vector as an ordinary tangent.
    This expands the source full-density step
    with the small-ball argument of 3.1.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric RealNormUP HilbertFormCompactness PartialFunctionUP
  EuclideanLebesgueDimensions CenteredBallRelations MeasureSetDensity
  EuclideanDensityGoodPoint MetricClosedBalls TangentConeUP TangentConeBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_full_density_tangent]:
    the full source tangent cone underlying
    the image differential plane in Federer
    3.2.17, pp. 254–255. Nearby points
    of the full-density set approximate any
    chosen ray, including the zero direction. *)
Theorem euclidean_full_density_tangent (R : realType) m
    (K : set (R_n R m)) (a : R_n R m) :
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) (~` K)) a 0%E ->
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R m)) K a=setT.
Proof.
move=> hK.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose N := inner_norm (@euclidean_inner_productP R m).
apply/seteqP; split=> v; first by [].
move=> _ e he.
pose t := Num.min (1/4) (e/(4*(N v+1))).
have hv0 : 0<=N v := inner_norm_nonnegative (@euclidean_inner_productP R m) v.
have ht : 0<t.
  rewrite /t lt_min; apply/andP; split; first by rewrite divr_gt0 // ltr0n.
  rewrite divr_gt0 // mulr_gt0 //; lra.
have ht4 : t<=1/4 by rewrite /t ge_min lexx.
have hte : t<=e/(4*(N v+1)) by rewrite /t ge_min lexx orbT.
have [d [hd hGood]] := euclidean_zero_density_good_point hK hK ht.
pose r := Num.min d e/2.
have hr : 0<r by rewrite /r divr_gt0 // lt_min hd he.
have hMinPos : 0<Num.min d e by rewrite lt_min hd he.
have hHalf : r<Num.min d e.
  rewrite /r; lra.
have hrd : r<d := lt_le_trans hHalf (real_minimum_left_bound d e).
have hre : r<e := lt_le_trans hHalf (real_minimum_right_bound d e).
pose s := r/(2*(N v+1)).
have hs : 0<s by rewrite /s divr_gt0 // mulr_gt0 //; lra.
pose b := a+s*:v.
have hIncluded : @metric_closed_ball R X b (t*r) `<=` @metric_closed_ball R X a r.
  move=> x hx.
  have hxb : mdist (b:X) x<=t*r := hx.
  have htri := metric_triangle (a:X) b x.
  have hab : mdist (a:X) b=s*N v.
    rewrite inner_metric_distanceE /b.
    have heq : a-(a+s*:v)= -(s*:v) by rewrite opprD addrA subrr add0r.
    by rewrite heq inner_normN inner_normZ (ger0_norm (ltW hs)).
  rewrite hab in htri.
  have hscale : s*(2*(N v+1))=r by rewrite /s divfK ?gt_eqF // mulr_gt0 //; lra.
  have htr := ler_wpM2r (ltW hr) ht4.
  apply: (le_trans htri _); nra.
have [x [hx [hxK _]]] := hGood r b hr hrd hIncluded.
have hxNear := hIncluded x hx.
exists x,s^-1; split.
- exact: contrapT hxK.
- split; first by rewrite invr_gt0.
  split.
  + have hh : N (x-a)<=r.
      change (is_true (N (a-x)<=r)) in hxNear.
      rewrite /N (real_seminorm_subtract (inner_norm_real_norm (@euclidean_inner_productP R m)).1); exact hxNear.
    exact: le_lt_trans hh hre.
  + have hEq : s^-1*:(x-a)-v=s^-1*:(x-b).
      have hId : x-b=(x-a)-s*:v by rewrite /b opprD addrA.
      by rewrite hId (scalerBr s^-1 (x-a) (s*:v)) scalerA mulVf ?gt_eqF ?scale1r.

    have hsi : 0<s^-1 by rewrite invr_gt0.
    rewrite hEq /N inner_normZ (ger0_norm (ltW hsi)).
    have hxb : N (x-b)<=t*r.
      change (is_true (N (b-x)<=t*r)) in hx.
      rewrite /N (real_seminorm_subtract (inner_norm_real_norm (@euclidean_inner_productP R m)).1); exact hx.
    have hmul := ler_wpM2l (ltW hsi) hxb.
    apply: (le_lt_trans hmul _).
    have hscale : s*(2*(N v+1))=r by rewrite /s divfK ?gt_eqF // mulr_gt0 //; lra.
    have hterr : t*(4*(N v+1))<=e by move: hte; rewrite ler_pdivlMr //; lra.
    have hcancel : s^-1*(t*r)=t*(2*(N v+1)).
      by rewrite -{1}hscale mulrCA [s^-1*(s*(2*(N v+1)))]mulrA mulVf ?gt_eqF // mul1r.
    rewrite hcancel; lra.
Qed.
