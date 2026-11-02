(** Federer (1969), 3.2.36, p. 273: the empty
    box and each actual one-dimensional interval give the product bases. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  CoordinateEdgeBoxGeometry ConvexIntrinsicGeneratingPolynomial IntegralGeometricGauge
  ZeroDegreeIntegralGauge FullDimensionIntegralGauge EuclideanLebesgueBoxes SteinerTubePolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_edge_box_zero_polynomial]: the empty edge
    product in the rectangular-box consequence of Federer 3.2.36,
    p. 273. The actual R^0 box has its single positive unit
    intrinsic coefficient, so its generating polynomial is one. *)
Lemma coordinate_edge_box_zero_polynomial (R:realType) (c:'I_0->R) (t:R):
  convex_intrinsic_generating_polynomial (coordinate_edge_box c) t= 1.
Proof.
have hc:forall i:'I_0,0<=c i by move=>i; have:=ltn_ord i; rewrite ltn0.
have hNonempty:=@coordinate_edge_box_nonempty R 0 c hc.
rewrite /convex_intrinsic_generating_polynomial big_ord_recr big_ord0 /=.
rewrite (@zero_degree_integral_geometric_gauge R 0 _ (coordinate_edge_box c) hNonempty).
by rewrite fine1 expr0 mulr1 add0r.
Qed.

(** Source for [coordinate_edge_box_line_polynomial]: a line interval
    of edge length c has zeta^0=1 and zeta^1=c in the product
    deduction of Federer 3.2.36, p. 273. Actual zeroth gauge
    normalization and the actual equal-dimension Lebesgue box formula
    prove the polynomial 1+c t, including c=0. *)
Lemma coordinate_edge_box_line_polynomial (R:realType) (c:'I_1->R) (t:R):
  (forall i,0<=c i) ->
  convex_intrinsic_generating_polynomial (coordinate_edge_box c) t= 1+c ord0*t.
Proof.
move=>hc.
have hNonempty:=coordinate_edge_box_nonempty hc.
have hZero (hGuard:(0<=1)%N):@integral_geometric_gauge R 1 0 hGuard 1 (coordinate_edge_box c)= 1%E.
  exact:zero_degree_integral_geometric_gauge hNonempty.
have hOne (hGuard:(1<=1)%N):@integral_geometric_gauge R 1 1 hGuard 1 (coordinate_edge_box c)=(c ord0)%:E.
  rewrite (@equal_dimension_integral_geometric_gauge R 1 _ 1 (coordinate_edge_box c) (lexx 1)).
  have hVolume:=@euclidean_closed_box R 1 (fun _=>0) c hc.
  rewrite big_ord1 subr0 in hVolume; exact hVolume.
rewrite /convex_intrinsic_generating_polynomial big_ord_recr big_ord1.
rewrite hZero hOne fine1 /= ?expr0 ?expr1 ?mulr1.
reflexivity.
Qed.
