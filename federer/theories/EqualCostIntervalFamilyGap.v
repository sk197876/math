(** Federer (1969), 3.2.40, p. 276: supporting
    point separation in an actual Phi subdivision, derived
    from the original interval laws of 2.10.28(4), p. 192. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter MetricDiameterReal
  CompactIntervalGauge EqualCostIntervalFamilyUP EqualSpacingIntervalGeometry
  CantorSplitRadiusUP CantorSplitRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_interval_family_point_gap]: supporting
    finite packing for the Cantor square in Federer 3.2.40,
    p. 276. Every point of one child is separated from every
    point of a different child by at least the actual gap
    t-s. Derive both parameters from the public interval laws;
    do not unfold or select a Phi implementation. *)
Lemma equal_cost_interval_family_point_gap (R:realType) (h:R->R)
    (J:compact_real_intervals R) (n:nat) (F:{fset compact_real_intervals R})
    (S T:compact_real_intervals R) (x y:real_line_metric R):
  is_equal_cost_interval_family h J n F ->S \in F ->T \in F ->S!=T ->
  val S x ->val T y ->
  let d:=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)) in
  let s:=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)) in
  cantor_split_spacing d n s-s<=mdist x y.
Proof.
move=>[hn [a [b [r [t [hJ [hd [hRadius [ht hCharacter]]]]]]]]] hS hT hDifferent hx hy.
pose d:=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)).
pose s:=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)).
change (is_true (cantor_split_spacing d n s-s<=mdist x y)).
have [i [hi hValueS]]:=(hCharacter S).1 hS.
have [k [hk hValueT]]:=(hCharacter T).1 hT.
have hChild:0<r:=(cantor_split_radius_bounds hRadius).1.
have hSpacing:r<t by rewrite ht; exact:cantor_split_spacing_strict hn hRadius.
have htPositive:0<t:=lt_trans hChild hSpacing.
have hab:a<=b by lra.
have hParent:d=b-a by rewrite /d hJ (extended_metric_diameter_segment hab).
have hLeaf:s=r.
  by rewrite /s hValueS (@equal_spacing_child_diameter R a r t i%:R (ltW hChild)).
rewrite hParent hLeaf -ht real_line_metric_distanceE.
have /andP[hxl hxu]:(a+i%:R*t<=x<=a+i%:R*t+r).
  by move:hx; rewrite hValueS /= in_itv.
have /andP[hyl hyu]:(a+k%:R*t<=y<=a+k%:R*t+r).
  by move:hy; rewrite hValueT /= in_itv.
case:(ltngtP i k)=>[hIK|hKI|hEqual].
- have hIndex:=@natural_strict_index_real_gap R i k hIK.
  have hStep:=ler_wpM2r (ltW htPositive) hIndex.
  rewrite mulrDl mul1r in hStep.
  have hNorm:=ler_norm (y-x); rewrite distrC in hNorm.
  lra.
- have hIndex:=@natural_strict_index_real_gap R k i hKI.
  have hStep:=ler_wpM2r (ltW htPositive) hIndex.
  rewrite mulrDl mul1r in hStep.
  have hNorm:=ler_norm (x-y).
  lra.
- have hSets:val S=val T by rewrite hValueS hValueT hEqual.
  have hEq:S=T:=val_inj hSets.
  by move:hDifferent; rewrite hEq eqxx.
Qed.
