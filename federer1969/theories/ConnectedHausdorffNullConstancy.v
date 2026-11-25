(** Federer (1969), 3.4.8(11), p. 333:
    constancy on connected critical components.
    This supporting metric lemma reuses the
    connected-length bound of 2.10.12, p. 176. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameter HausdorffMeasure ConnectedHausdorffLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [connected_hausdorff_null_constancy]:
    the zero length of a connected
    image forces it to be a point.
    This supports the critical-component argument
    in 3.4.8(11), p. 333. *)
Theorem connected_hausdorff_null_constancy (R:realType) (X:topologicalType)
    (Y:metricType R) (A:set X) (f:X->Y):
  connected A ->{within A,continuous f} ->
  @hausdorff_measure R Y 1 (f @` A) = 0%E ->
  forall x y,A x ->A y ->f x = f y.
Proof.
move=>hA hf hNull x y hx hy.
have hConnected:connected (f @` A):=connected_continuous_connected hA hf.
have hDiameter:=@federer_2_10_12 R Y (f @` A) hConnected.
rewrite hNull in hDiameter.
have hFx:(f @` A) (f x) by exists x.
have hFy:(f @` A) (f y) by exists y.
have hDistance:=metric_diameter_upper (extended_metric_diameter_specification (f @` A))
  hFx hFy.
have hLe:(mdist (f x) (f y)<=0)%R.
  have h:=le_trans hDistance hDiameter.
  by move:h;rewrite lee_fin.
apply:mdist_positivity;apply/eqP;by rewrite eq_le hLe mdist_ge0.
Qed.
