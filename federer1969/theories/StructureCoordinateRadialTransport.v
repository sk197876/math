(** Federer (1969), 3.3.4, p. 291: exact transport of the literal
    radial supremum through the proved original ball/cone identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  StructureCoordinateCones StructureCoordinateGrowth StructureRadialCostLimits
  StructureRadialImageMeasure StructureOpenBallGrowth StructureRadialOpenBallSupremum
  ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_coordinate_radial_ball_transport]: Federer
    3.3.4, p. 291, equality of the unnormalized psi ball growth with
    the original I_j radius supremum. The actual preimage equality is
    the sole geometric input and is discharged by the active-coset
    coordinate theorem. Infinite numerator values and all positive
    real radii and apertures remain. *)
Theorem structure_coordinate_radial_ball_transport (R:realType) m k
    (Y:metricType R)
    (phi:set (inner_metric_space (@euclidean_inner_productP R (m+k)))->\bar R)
    (A D:set (inner_metric_space (@euclidean_inner_productP R (m+k))))
    (a:inner_metric_space (@euclidean_inner_productP R (m+k)))
    (L:{linear R_n R (m+k)->R_n R (m+k)}) (j:'I_k)
    (f:inner_metric_space (@euclidean_inner_productP R (m+k))->Y)
    (z:Y) (delta t:R):
  (forall r s:R,0<s ->structure_coordinate_cone A a L j r%:E s=
    [set x|A x /\ mdist a x<r /\ D x /\ mdist z (f x)<s]) ->0<t ->
  structure_open_ball_growth m (structure_radial_image_measure m phi A a D f delta) z t=
    structure_coordinate_radial_supremum phi A a L j delta t.
Proof.
move=>hPreimage ht.
rewrite (structure_radial_open_ball_supremum m phi A D a f delta z ht)
  /structure_coordinate_radial_supremum /structure_radial_cost_supremum.
congr (extended_real_sup _); apply/seteqP; split=>v.
- move=>[r [hr hValue]]; exists r; split=>//.
  by rewrite /structure_coordinate_cost (hPreimage r t ht).
- move=>[r [hr hValue]]; exists r; split=>//.
  by move:hValue; rewrite /structure_coordinate_cost (hPreimage r t ht).
Qed.
