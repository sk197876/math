(** Federer (1969), 3.2.36, pp. 272--273: the full actual
    Cartesian intrinsic-volume convolution on compact convex factors. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanCartesianMap EuclideanCartesianBorel EuclideanCartesianConvexGeometry CompactHausdorffMetric
  CompactSetDistanceProfile CompactMetricBounded ConvexCartesianTubePolynomial
  SteinerTubePolynomial SteinerTubeScalarPolynomial ConvexSteinerTubeFormula
  ConvexIntrinsicFinitePart IntegralGeometricGauge EuclideanBallVolume EuclideanLebesgueDimensions
  ScalarComplementPolynomialComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_convex_cartesian_intrinsic_volumes]: the
    Cartesian-product theorem in Federer 3.2.36, pp. 272--273:
    zeta^l(P times Q) is the sum of zeta^i(P) zeta^j(Q)
    over i+j=l. The actual product-tube calculation is compared with
    the product body's own Steiner formula; strictly positive alpha
    coefficients cancel through the internal finite polynomial proof.
    No convolution, fibre identity or integration premise is assumed.
    Both factors may be lower-dimensional, and all natural ambient
    and intrinsic dimensions, including zero, are retained. *)
Theorem compact_convex_cartesian_intrinsic_volumes (R:realType) m n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R m)))
    (B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n))):
  is_inner_convex (val A) ->is_inner_convex (val B) ->
  forall l:'I_(m+n).+1,
    @integral_geometric_gauge R (m+n) l (steiner_dimension_guard l) 1
      (euclidean_cartesian_set (val A) (val B))=
    \sum_(i:'I_m.+1) \sum_(j:'I_n.+1|(i+j==l)%N)
      @integral_geometric_gauge R m i (steiner_dimension_guard i) 1 (val A)*
      @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 (val B).
Proof.
move=>hA hB.
pose Z:=inner_metric_space (@euclidean_inner_productP R (m+n)).
pose S:set Z:=euclidean_cartesian_set (val A) (val B).
have hCompact:compact S:=euclidean_cartesian_compact (set_valP A).1 (set_valP B).1.
have hNonempty:S!=set0:=euclidean_cartesian_nonempty (set_valP A).2 (set_valP B).2.
pose C:compact_hausdorff_space Z:=exist _ S (mem_set (conj hCompact hNonempty)).
have hConvex:is_inner_convex (val C):=euclidean_cartesian_convex hA hB.
pose x (i:'I_m.+1):R:=fine (@integral_geometric_gauge R m i (steiner_dimension_guard i) 1 (val A)).
pose y (j:'I_n.+1):R:=fine (@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 (val B)).
pose z (l:'I_(m+n).+1):R:=fine (@integral_geometric_gauge R (m+n) l
  (steiner_dimension_guard l) 1 (val C)).
have hG (i:'I_m.+1):@integral_geometric_gauge R m i (steiner_dimension_guard i) 1 (val A)=(x i)%:E.
  exact:convex_intrinsic_finite_part_value (set_valP A).2 hA (compact_metric_diameter_finite A).
have hH (j:'I_n.+1):@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 (val B)=(y j)%:E.
  exact:convex_intrinsic_finite_part_value (set_valP B).2 hB (compact_metric_diameter_finite B).
have hZ (l:'I_(m+n).+1):@integral_geometric_gauge R (m+n) l (steiner_dimension_guard l) 1 (val C)=(z l)%:E.
  exact:convex_intrinsic_finite_part_value (set_valP C).2 hConvex (compact_metric_diameter_finite C).
have hProductScalar (r:R):convex_cartesian_tube_polynomial (val A) (val B) r=
    (\sum_(i:'I_m.+1) \sum_(j:'I_n.+1) (x i*y j)*
      (euclidean_unit_ball_volume R ((m-i)+(n-j))*r^+((m-i)+(n-j))))%R%:E.
  rewrite /convex_cartesian_tube_polynomial -sumEFin.
  apply:eq_bigr=>i _; rewrite -sumEFin; apply:eq_bigr=>j _.
  by rewrite hG hH -!EFinM.
have hScalar (r:R):(0<r)%R ->
    (\sum_(l:'I_(m+n).+1) z l*(euclidean_unit_ball_volume R (m+n-l)*r^+(m+n-l))=
    \sum_(i:'I_m.+1) \sum_(j:'I_n.+1) (x i*y j)*
      (euclidean_unit_ball_volume R ((m-i)+(n-j))*r^+((m-i)+(n-j))))%R.
  move=>hr.
  have hActual:=@convex_cartesian_tube_volume_polynomial R m n A B
    (compact_set_distance_profile C) r hA hB (compact_set_distance_profile_specification C) hr.
  rewrite (@convex_steiner_tube_formula R (m+n) (val C) (compact_set_distance_profile C)
    (set_valP C).2 hConvex (compact_metric_diameter_finite C)
    (compact_set_distance_profile_specification C) r hr)
    (@steiner_tube_polynomial_scalar_value R (m+n) (val C) r
      (set_valP C).2 hConvex (compact_metric_diameter_finite C)) hProductScalar in hActual.
  exact:EFin_inj hActual.
have hCoefficient:=@scalar_complement_polynomial_comparison R m n x y z hScalar.
move=>l.
rewrite hZ hCoefficient -sumEFin.
apply:eq_bigr=>i _; rewrite -sumEFin; apply:eq_bigr=>j _.
by rewrite hG hH -EFinM.
Qed.
