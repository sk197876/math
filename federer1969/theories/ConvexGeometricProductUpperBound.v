(** The product upper inequality in Federer (1969),
    3.2.45, p. 280. The cube subdivision follows
    the book; Haar uniqueness reuses the earlier
    product argument in 2.10.45, p. 203. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry EuclideanCartesianMap
  EuclideanLebesgue EuclideanLebesgueDimensions EuclideanLebesgueHaar
  ConvexGeometricProductSlice ConvexGeometricProductSliceHaar ConvexCubeProductUpperBound
  EuclideanInvariantNonnegativeMultiple IntegralGeometricMeasure
  MeasureUP TopologicalBorel BorelRegularisation BorelRegularisationBasic
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_geometric_euclidean_product_upper_bound]:
    direct product upper inequality of Federer 3.2.45,
    p. 280, for a second factor of finite
    original Q_1 mass. The cube argument and
    translation-invariant slice comparison retain arbitrary
    factors, degree zero, zero masses and infinite
    first-factor outer measure. This helper uses total
    extended multiplication; the eventual equality retains
    the book's ordinary partial-product domain. No
    mixed-volume lower inequality is assumed or asserted here. *)
Theorem convex_geometric_euclidean_product_upper_bound (R : realType) m n k (hKN : (k <= n)%N)
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @convex_integral_geometric_measure R n k hKN 1 V < +oo ->
  @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
    (euclidean_cartesian_set U V) <=
      @euclidean_lebesgue_measure R m U * @convex_integral_geometric_measure R n k hKN 1 V.
Proof.
move=> hV.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose gamma := fun A : set X =>
  @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
    (euclidean_cartesian_set A V).
pose reg := borel_regularisation gamma.
have hMeasure := @convex_geometric_product_slice_is_measure R m n k hKN V.
have hRegular := @convex_geometric_product_slice_regularised_invariant R m n k hKN V hV.
have [d hD hValue] := @euclidean_invariant_nonnegative_multiple R m reg hRegular.
pose P : set X := [set x | forall i, (0 <= x i <= 1)%R].
have hP : is_euclidean_coordinate_cube ([ffun _ => 0%R] : R_n R m) 1%R P.
  split; first exact: ler01.
  move=> x; split=> h i; have hI := h i; by move: hI; rewrite ffunE add0r.
have hCompact : compact P := coordinate_cube_compact hP.
have hBorel : borel_set P := closed_borel_set
  (compact_closed (@metric_hausdorff R [the metricType R of X]) hCompact).
have hCubeUpper := @convex_cube_product_upper_bound R m n k hKN _ 1%R P V hP hV.
have hRegValue := @borel_regularised_measure_borel_value R [the topologicalType of X]
  gamma hMeasure P hBorel.
have hCubeVolume : @euclidean_lebesgue_measure R m P = 1.
  rewrite (coordinate_cube_volume hP) expr1n; reflexivity.
have hGammaCube : gamma P = d%:E.
  have hHaarCube := hValue P.
  rewrite hCubeVolume mule1 in hHaarCube.
  exact (eq_trans (esym hRegValue) hHaarCube).
have hMultiplier : d%:E <= @convex_integral_geometric_measure R n k hKN 1 V.
  rewrite expr1n mul1e in hCubeUpper.
  change (is_true (gamma P <= @convex_integral_geometric_measure R n k hKN 1 V)) in hCubeUpper.
  by rewrite hGammaCube in hCubeUpper.
have hDominates := @borel_regularisation_dominates R [the topologicalType of X]
  gamma reg hMeasure (borel_regularisation_laws gamma) U.
have hScaled := lee_wpmul2l (measure_nonnegative (euclidean_lebesgue_is_measure R m) U)
  hMultiplier.
rewrite muleC in hScaled.
rewrite -/(gamma U); apply: le_trans hDominates _.
rewrite (hValue U); exact hScaled.
Qed.
