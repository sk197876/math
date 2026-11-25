(** Concrete endpoint regressions for the original section
    and product assertions of Federer 3.2.45, pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanLebesgueDimensions EuclideanLebesgueHaar
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry EuclideanLebesgueBoxes
  IntegralGeometricMeasure EuclideanIntegralGeometricLebesgue ConvexIntegralGeometricSections ConvexGeometricProductTheorem
  DenseMinkowskiInfinite PointMassMeasure ExtendedRealPartial ExtendedRealOrderTopology
  MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness HausdorffProductLowerBound
  PartialFunctionUP PartialFunctionBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_dimensional_convex_section_atom]: concrete
    empty-block regression for the section display of
    Federer 3.2.45, pp. 279–280. The actual
    whole source and every original section in R^0
    have mass one. The ordinary section integral is
    one, rather than zero. The all-set section
    theorem retains this independently evaluated atom. *)
Example zero_dimensional_convex_section_atom (R : realType) :
  let X := inner_metric_space (@euclidean_inner_productP R 0) in
  let F := fun y : X => (@convex_integral_geometric_measure R 0 0 (leqnn 0) 1
    [set z : X | (@setT X) (@euclidean_block_join R 0 0 (y,z))] : extended_real_line R) in
  is_measure_integral (@euclidean_lebesgue_measure R 0) (partial_function_total F) 1 /\
  measure_upper_integral (@euclidean_lebesgue_measure R 0) (partial_function_total F)<=
    @convex_integral_geometric_measure R (0+0) (0+0) (leq_add (leqnn 0) (leqnn 0)) 1 (@setT X).
Proof.
move=> X F.
have hVolume : @euclidean_lebesgue_measure R 0 (@setT X)= 1.
  change (point_mass R (0%R:X) setT= 1); exact: point_mass_in I.
have hValue : @convex_integral_geometric_measure R 0 0 (leqnn 0) 1 (@setT X)= 1.
  by rewrite (@euclidean_convex_integral_geometric_lebesgue R 0 (leqnn 0) 1 (lexx 1)) hVolume.
have hFunction : F=(fun _ : X => (1 : extended_real_line R)).
  apply: funext=> y; exact hValue.
have hIntegral := @nonnegative_extended_constant_integral R X (@euclidean_lebesgue_measure R 0)
  (euclidean_lebesgue_is_measure R 0) 1 lee01.
rewrite hVolume mule1 in hIntegral.
split; first by rewrite hFunction.
exact: (@convex_integral_geometric_section_upper_integral R 0 0 0 (leqnn 0) (@setT X)).
Qed.

(** Source for [unit_square_convex_product_equality]: concrete
    finite-mass regression for the original product
    equality in Federer 3.2.45, p. 280.
    Apply the original theorem to two actual unit
    coordinate intervals. Their independently computed
    Lebesgue and Q_1 masses are one, so
    the actual square has mass one. *)
Example unit_square_convex_product_equality (R : realType) :
  let P : set (inner_metric_space (@euclidean_inner_productP R 1)) :=
    [set x | forall i, (0<=x i<=1)%R] in
  @convex_integral_geometric_measure R (1+1) (1+1) (leq_add (leqnn 1) (leqnn 1)) 1
    (euclidean_cartesian_set P P)= 1.
Proof.
move=> P.
have hP : is_euclidean_coordinate_cube ([ffun _ => 0%R] : R_n R 1) 1%R P.
  split; first exact: ler01.
  move=> x; split=> h i; have hI := h i; by move: hI; rewrite ffunE add0r.
have hVolume : @euclidean_lebesgue_measure R 1 P= 1 by rewrite (coordinate_cube_volume hP) expr1n.
have hMass : @convex_integral_geometric_measure R 1 1 (leqnn 1) 1 P= 1.
  by rewrite (@euclidean_convex_integral_geometric_lebesgue R 1 (leqnn 1) 1 (lexx 1)) hVolume.
have hMeasurable : measure_measurable (@euclidean_lebesgue_measure R 1) P.
  apply: euclidean_borel_measurable; apply: closed_borel_set.
  exact: compact_closed (@metric_hausdorff R [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)])
    (coordinate_cube_compact hP).
have hDomain : mule_def (@euclidean_lebesgue_measure R 1 P)
    (@convex_integral_geometric_measure R 1 1 (leqnn 1) 1 P) by rewrite hVolume hMass /mule_def.
by rewrite (@federer_3_2_45_product R 1 1 1 (leqnn 1) P P hMeasurable hDomain) hVolume hMass mul1e.
Qed.

(** Source for [unit_interval_times_whole_line_convex_product]:
    concrete infinite-second-mass regression for Federer
    3.2.45, p. 280. The first interval
    has volume one and the whole second line
    has infinite Q_1^1 mass. The ordinary
    product is defined, and the new product lower
    bound forces the actual Cartesian mass to be
    infinite. No finite second-mass premise is used. *)
Example unit_interval_times_whole_line_convex_product (R : realType) :
  let X := inner_metric_space (@euclidean_inner_productP R 1) in
  let P : set X := [set x | forall i, (0<=x i<=1)%R] in
  @convex_integral_geometric_measure R (1+1) (1+1) (leq_add (leqnn 1) (leqnn 1)) 1
    (euclidean_cartesian_set P (@setT X))=+oo.
Proof.
move=> X P.
have hP : is_euclidean_coordinate_cube ([ffun _ => 0%R] : R_n R 1) 1%R P.
  split; first exact: ler01.
  move=> x; split=> h i; have hI := h i; by move: hI; rewrite ffunE add0r.
have hVolume : @euclidean_lebesgue_measure R 1 P= 1 by rewrite (coordinate_cube_volume hP) expr1n.
have hMass : @convex_integral_geometric_measure R 1 1 (leqnn 1) 1 (@setT X)=+oo.
  rewrite (@euclidean_convex_integral_geometric_lebesgue R 1 (leqnn 1) 1 (lexx 1)).
  exact: positive_euclidean_whole_volume_infinite (ltnSn 0).
have hMeasurable : measure_measurable (@euclidean_lebesgue_measure R 1) P.
  apply: euclidean_borel_measurable; apply: closed_borel_set.
  exact: compact_closed (@metric_hausdorff R [the metricType R of X]) (coordinate_cube_compact hP).
have hDomain : mule_def (@euclidean_lebesgue_measure R 1 P)
    (@convex_integral_geometric_measure R 1 1 (leqnn 1) 1 (@setT X)) by rewrite hVolume hMass /mule_def /= oner_eq0.
by rewrite (@federer_3_2_45_product R 1 1 1 (leqnn 1) P (@setT X) hMeasurable hDomain)
  hVolume hMass mul1e.
Qed.

(** Source for [null_first_whole_second_product_is_undefined]:
    concrete arithmetic endpoint regression for the
    original partial-product convention in Federer
    2.1.1, p. 51, retained in 3.2.45,
    p. 280. The empty first set has
    volume zero and the whole second line has
    infinite Q_1^1 mass. Their ordinary scalar
    product is undefined. This does not assert
    a value for an undefined book expression. *)
Example null_first_whole_second_product_is_undefined (R : realType) :
  let X := inner_metric_space (@euclidean_inner_productP R 1) in
  extended_multiply (@euclidean_lebesgue_measure R 1 (@set0 X))
    (@convex_integral_geometric_measure R 1 1 (leqnn 1) 1 (@setT X))=None.
Proof.
move=> X.
rewrite (measure_empty (euclidean_lebesgue_is_measure R 1))
  (@euclidean_convex_integral_geometric_lebesgue R 1 (leqnn 1) 1 (lexx 1))
  (@positive_euclidean_whole_volume_infinite R 1 (ltnSn 0)).
exact: extended_multiply_zero_infinity.
Qed.
