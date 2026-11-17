(** Supporting the corrected continuity argument of Federer (1969),
    3.2.45, p. 279: scalar convex-image length is subadditive in
    the scalar map. The existing line-length and diameter laws suffice. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology ring.
From Federer Require Import RealMetricBackground InnerConvex ScalarConvexLength LebesgueDiameterBound
  LebesgueScalarMeasure MeasureUP MeasureBasic MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_convex_image_sum_length_bound]: an expanded
    helper for the exponent continuity assertion of Federer 3.2.45,
    p. 279. It reuses convex pair-length bounds from 2.10.4,
    p. 172, and the scalar diameter upper bound from 2.10.7,
    pp. 174–175. The source itself needs no topology; only the
    two scalar images must be convex and have finite length. *)
Theorem scalar_convex_image_sum_length_bound (R : realType) (X : choiceType)
    (A : set X) (f g : X -> R) :
  A !=set0 -> @is_inner_convex R R^o (f @` A) ->
  @is_inner_convex R R^o (g @` A) ->
  lebesgue_scalar_measure (f @` A) < +oo ->
  lebesgue_scalar_measure (g @` A) < +oo ->
  lebesgue_scalar_measure ((fun x => (f x + g x)%R) @` A) <=
    lebesgue_scalar_measure (f @` A) + lebesgue_scalar_measure (g @` A).
Proof.
move=> hNonempty hFConvex hGConvex hFFinite hGFinite.
pose F := f @` A.
pose G := g @` A.
pose H := (fun x => (f x + g x)%R) @` A.
pose a : R := fine (lebesgue_scalar_measure F).
pose b : R := fine (lebesgue_scalar_measure G).
have hFValue : lebesgue_scalar_measure F = a%:E.
  symmetry; apply: fineK.
  by rewrite (ge0_fin_numE (measure_nonnegative (lebesgue_scalar_is_measure R) F)).
have hGValue : lebesgue_scalar_measure G = b%:E.
  symmetry; apply: fineK.
  by rewrite (ge0_fin_numE (measure_nonnegative (lebesgue_scalar_is_measure R) G)).
have ha : (0 <= a)%R.
  have h := measure_nonnegative (lebesgue_scalar_is_measure R) F.
  by rewrite hFValue lee_fin in h.
have hb : (0 <= b)%R.
  have h := measure_nonnegative (lebesgue_scalar_is_measure R) G.
  by rewrite hGValue lee_fin in h.
have hH : H !=set0.
  have [x hx] := hNonempty; exists (f x + g x)%R; by exists x.
rewrite -/H hFValue hGValue -EFinD.
apply: le_trans (lebesgue_scalar_diameter_bound hH) _.
apply: (metric_diameter_least
  (@extended_metric_diameter_specification R [the metricType R of real_line_metric R] H)).
- rewrite lee_fin; exact: addr_ge0 ha hb.
- move=> u v [x hx <-] [y hy <-].
  have hxF : F (f x) by exists x.
  have hyF : F (f y) by exists y.
  have hxG : G (g x) by exists x.
  have hyG : G (g y) by exists y.
  have hF := real_convex_pair_length_bound hFConvex hxF hyF.
  have hG := real_convex_pair_length_bound hGConvex hxG hyG.
  rewrite hFValue lee_fin in hF.
  rewrite hGValue lee_fin in hG.
  rewrite real_line_metric_distanceE lee_fin.
  have hDifference : ((f x + g x) - (f y + g y) = (f x-f y) + (g x-g y))%R by ring.
  rewrite hDifference.
  exact: le_trans (ler_normD _ _) (lerD hF hG).
Qed.
