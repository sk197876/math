(** Supporting local finiteness in the Euclidean-factor
    product argument of Federer (1969), 3.2.45, p. 280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanCoordinateCubeUP
  EuclideanCartesianMap EuclideanAdditiveGroup EuclideanCoordinateCubeGeometry EuclideanCoordinateCubeLaws ConvexGeometricProductSlice ConvexCubeProductUpperBound
  IntegralGeometricMeasure MeasureUP MeasureBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_geometric_product_slice_compact_finite]:
    supporting local finiteness for the Haar comparison in
    Federer 3.2.45, p. 280. A compact first-factor set
    lies in an actual coordinate cube; the proved cube
    upper bound is finite when the original second-factor
    Q_1 mass is finite. No measurability of that second
    factor is required. Dimension zero and zero mass remain. *)
Theorem convex_geometric_product_slice_compact_finite (R : realType) m n k (hKN : (k <= n)%N)
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @convex_integral_geometric_measure R n k hKN 1 V < +oo ->
  forall K : set (inner_metric_space (@euclidean_inner_productP R m)), compact K ->
    @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
      (euclidean_cartesian_set K V) < +oo.
Proof.
move=> hV K hK.
have [r [hR hCoordinate]] := @euclidean_compact_coordinate_bound R m K hK.
pose a : R_n R m := [ffun _ => (-r)%R].
have hSide : (0 <= r+r)%R by lra.
have [P hP] := @euclidean_coordinate_cube_exists R m a (r+r)%R hSide.
have hKP : K `<=` P.
  move=> x hX; apply: (hP.2 x).2=> i.
  have hBounds := hCoordinate x hX i.
  rewrite /a ffunE; move: hBounds; rewrite ler_norml=> /andP[hLow hHigh].
  apply/andP; split; lra.
have hUpper := @convex_cube_product_upper_bound R m n k hKN a (r+r)%R P V hP hV.
pose gamma := fun B : set (inner_metric_space (@euclidean_inner_productP R m)) =>
  @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
    (euclidean_cartesian_set B V).
have hGamma := @convex_geometric_product_slice_is_measure R m n k hKN V.
have hMonotone := @measure_mono R _ gamma hGamma K P hKP.
apply: le_lt_trans hMonotone _; apply: le_lt_trans hUpper _.
have hFinite : @convex_integral_geometric_measure R n k hKN 1 V \is a fin_num.
  rewrite (ge0_fin_numE (@measure_nonnegative R _ _
    (@convex_integral_geometric_measure_is_measure R n k hKN 1 (lexx 1)) V)).
  exact hV.
rewrite -(fineK hFinite) -EFinM; exact: ltry.
Qed.
