(** Federer (1969), 3.2.38, pp. 274--275: cells meeting a
    compact set lie in its small tube as the mesh tends to zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_cube_family_near_set]: supporting the
    outside-source error estimates in Federer 3.2.38, pp. 274--275.
    Every member meeting C lies within distance m h of an actual
    point of C. Applied to the compact Lusin core this also controls
    the mass of good cubes outside that core. Arbitrary original
    sources and empty families are permitted in this geometric lemma. *)
Lemma coordinate_cube_family_near_set (R:realType) m (I:Type)
    (a:I->R_n R m) (h d:R)
    (Q:I->set (inner_metric_space (@euclidean_inner_productP R m)))
    (C:set (inner_metric_space (@euclidean_inner_productP R m))):
  (forall i,is_euclidean_coordinate_cube (a i) h (Q i)) ->
  (forall i,(Q i `&` C)!=set0) ->m%:R*h<d ->
  (\bigcup_i Q i) `<=`metric_open_thickening C d.
Proof.
move=>hQ hMeet hDiameter x [i _ hx].
have [c [hc hC]]:=hMeet i; exists c; first exact hC.
change (is_true (mdist c x<d)).
exact:le_lt_trans (coordinate_cube_distance_bound (hQ i) hc hx) hDiameter.
Qed.
