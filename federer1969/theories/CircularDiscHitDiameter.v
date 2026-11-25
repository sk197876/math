(** Federer (1969), 3.3.19, p. 303: if
    the original S meets two original level discs,
    their proved strict separation forces its diameter
    to exceed the actual common radius. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls MetricDiameterUP MetricDiameter
  FactorialDiscScalesSealed CircularDiscTreeUP CircularDiscTreeSeparation CircularDiscHitCount
  FiniteCellHitMeasureUP FiniteCellHitIndicesLaws FiniteTwoDistinctMembers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Diameter.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_two_hits_radius_below_diameter]:
    actual rho_n<delta whenever the original test
    set has diameter at most delta and meets
    two original G_n discs, as used in
    3.3.19, p. 303. No source regularity,
    measurability or boundedness premise is added. *)
Theorem circular_disc_two_hits_radius_below_diameter j (T:set E) (d:R):
  (2<=#|` @circular_disc_hit_indices R H j T|)%N ->
  (extended_metric_diameter T<=d%:E)%E ->rho j<d.
Proof.
move=>hCount hDiameter.
have [z [w [hz [hw hDifferent]]]]:=@finite_two_distinct_members E
  (@circular_disc_hit_indices R H j T) hCount.
have [hzH [x [hxBall hxT]]]:=(@finite_cell_hit_indices_membership E E (H j)
  (fun a=>metric_closed_ball a (rho j)) T z).1 hz.
have [hwH [y [hyBall hyT]]]:=(@finite_cell_hit_indices_membership E E (H j)
  (fun a=>metric_closed_ball a (rho j)) T w).1 hw.
have hGap:=@circular_disc_tree_separation R H hH j z w hzH hwH hDifferent x y hxBall hyBall.
have hBound:=le_trans (metric_diameter_upper (extended_metric_diameter_specification T) hxT hyT) hDiameter.
rewrite lee_fin in hBound;exact:lt_le_trans hGap hBound.
Qed.
End Diameter.
