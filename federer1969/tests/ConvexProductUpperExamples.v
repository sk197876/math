(** Concrete product regressions for the upper inequality in
    Federer (1969), 3.2.45, p. 280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry EuclideanCartesianMap
  EuclideanBlockRectangleMass EuclideanLebesgueDimensions EuclideanLebesgueHaar EuclideanLebesgueBoxes
  EuclideanIntegralGeometricLebesgue IntegralGeometricMeasure ConvexCubeProductUpperBound
  ConvexGeometricProductUpperBound MeasureUP TopologicalBorel BorelRegularMeasureUP
  PointMassMeasure ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [unit_square_convex_product_upper_sharp]:
    concrete sharpness regression for the product upper
    bound in Federer 3.2.45, p. 280.
    Both actual unit segments have Q_1 mass
    one; their square has Q_1^2 mass
    one. The actual block-product Lebesgue theorem
    proves equality independently of the new bound. *)
Example unit_square_convex_product_upper_sharp (R : realType) :
  let P : set (inner_metric_space (@euclidean_inner_productP R 1)) :=
    [set x | forall i, (0 <= x i <= 1)%R] in
  @convex_integral_geometric_measure R 1 1 (leqnn 1) 1 P = 1 /\
  @convex_integral_geometric_measure R (1+1) (1+1) (leq_add (leqnn 1) (leqnn 1)) 1
    (euclidean_cartesian_set P P) = 1 /\
  @convex_integral_geometric_measure R (1+1) (1+1) (leq_add (leqnn 1) (leqnn 1)) 1
    (euclidean_cartesian_set P P) <= 1.
Proof.
move=> P.
have hP : is_euclidean_coordinate_cube ([ffun _ => 0%R] : R_n R 1) 1%R P.
  split; first exact: ler01.
  move=> x; split=> h i; have hI := h i; by move: hI; rewrite ffunE add0r.
have hVolume : @euclidean_lebesgue_measure R 1 P = 1.
  by rewrite (coordinate_cube_volume hP) expr1n.
have hSource : @convex_integral_geometric_measure R 1 1 (leqnn 1) 1 P = 1.
  rewrite (@euclidean_convex_integral_geometric_lebesgue R 1 (leqnn 1) 1 (lexx 1) P); exact hVolume.
have hBorel : borel_set P := closed_borel_set (compact_closed
  (@metric_hausdorff R [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)])
  (coordinate_cube_compact hP)).
have hMeasurable := @euclidean_borel_measurable R 1 P hBorel.
have hRectangle := @euclidean_block_rectangle_mass R 1 1 P P hMeasurable hMeasurable.
have hTarget : @convex_integral_geometric_measure R (1+1) (1+1)
    (leq_add (leqnn 1) (leqnn 1)) 1 (euclidean_cartesian_set P P) = 1.
  rewrite (@euclidean_convex_integral_geometric_lebesgue R (1+1)%N
    (leq_add (leqnn 1) (leqnn 1)) 1 (lexx 1) _).
  by rewrite /euclidean_cartesian_set hRectangle hVolume mul1e.
have hBound := @convex_cube_product_upper_bound R 1 1 1 (leqnn 1)
  _ 1%R P P hP ltac:(by rewrite hSource; exact: ltry).
rewrite expr1n mul1e hSource in hBound.
by split=> //; split.
Qed.

(** Source for [zero_dimensional_convex_product_atom]:
    concrete endpoint regression for the product argument
    of Federer 3.2.45, p. 280. Both
    empty coordinate blocks and their product retain
    mass one. In particular the zeroth power of
    a zero cube side remains one. *)
Example zero_dimensional_convex_product_atom (R : realType) :
  let X := inner_metric_space (@euclidean_inner_productP R 0) in
  @convex_integral_geometric_measure R (0+0) (0+0) (leq_add (leqnn 0) (leqnn 0)) 1
    (euclidean_cartesian_set (@setT X) (@setT X)) = 1.
Proof.
move=> X.
rewrite (@euclidean_convex_integral_geometric_lebesgue R (0+0)%N
  (leq_add (leqnn 0) (leqnn 0)) 1 (lexx 1) _).
change (point_mass R (0%R : X) (euclidean_cartesian_set (@setT X) (@setT X)) = 1).
apply: point_mass_in; by split.
Qed.

(** Source for [whole_line_times_zero_cube_convex_mass]:
    concrete zero-factor regression for the upper bound
    in Federer 3.2.45, p. 280. The
    entire first line times the actual zero-side
    second cube has Q_1^2 mass zero.
    The finite second-factor upper bound retains this
    case even though the first factor is unbounded.
    This is an upper-bound extension, not a claim
    that Federer's ordinary zero-times-infinity product exists. *)
Example whole_line_times_zero_cube_convex_mass (R : realType) :
  let X := inner_metric_space (@euclidean_inner_productP R 1) in
  let P : set X := [set x | forall i, (0 <= x i <= 0)%R] in
  @convex_integral_geometric_measure R (1+1) (1+1) (leq_add (leqnn 1) (leqnn 1)) 1
    (euclidean_cartesian_set (@setT X) P) = 0.
Proof.
move=> X P.
have hP : is_euclidean_coordinate_cube ([ffun _ => 0%R] : R_n R 1) 0%R P.
  split; first exact: lexx.
  move=> x; split=> h i; have hI := h i; by move: hI; rewrite ffunE add0r.
have hSource : @convex_integral_geometric_measure R 1 1 (leqnn 1) 1 P = 0.
  rewrite (@euclidean_convex_integral_geometric_lebesgue R 1 (leqnn 1) 1 (lexx 1) _).
  by rewrite (coordinate_cube_volume hP) expr1.
have hBound := @convex_geometric_euclidean_product_upper_bound R 1 1 1 (leqnn 1)
  setT P ltac:(by rewrite hSource; exact: ltry).
rewrite hSource mule0 in hBound.
have hNonnegative := @measure_nonnegative R _ _
  (@convex_integral_geometric_measure_is_measure R (1+1) (1+1)
    (leq_add (leqnn 1) (leqnn 1)) 1 (lexx 1)) (euclidean_cartesian_set (@setT X) P).
by apply/eqP; rewrite eq_le hBound hNonnegative.
Qed.
