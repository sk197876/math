(** Federer (1969), 2.10.45, printed p. 203: finitely subdivide the
    Euclidean cube for each second-factor covering piece T, bound every
    product diameter by sqrt(m+1) times the mesh, and sum its Hausdorff
    costs. The existing opaque equal partitions and midpoint grid give
    circumscribed balls instead of naming each small cube; their same
    sqrt(m) mesh diameter bound retains the printed coefficient. Zero side
    length, zero first dimension and empty T are included. Source context:
    SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws RealHausdorffDegreeTransport RealPower RealPowerSuccessor
  RealPowerNaturalHausdorff MetricRealPowerCost RealPowerCoverVariants
  RealPowerCutoffFiniteCover MetricRealPowerMaps HausdorffRectangleLowerBound HausdorffProductSliceTranslation ExtendedRealOrderTopology GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBoxUP RectangularGridUP RectangularGrid RectangularGridBallCover RectangularGridCardinality
  ScalarIntervalPartitionUP ScalarIntervalPartition UniformMeshCountUP UniformMeshCountLaws UniformMeshCount
  SquaredMetricProductUP SquaredProductDiameter MetricProductRectangles MetricClosedBalls MetricDiameterUP MetricDiameter
  HausdorffLengthUP HausdorffMeasureUP HausdorffDiameterCost MetricScaleEnvelopeUP
  HausdorffCutoffFiniteCover RealEuclideanProductCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_euclidean_cube_product_finite_cutoff_bound]: supporting
    finite inner sum and count bound in
    the last display of 2.10.45, p. 203.
    A positive mesh h bounds diam(T), is
    at most delta, and obeys the product
    cutoff. All chosen nodes, counts and centres
    are used only through their sealed laws. *)
Theorem real_euclidean_cube_product_finite_cutoff_bound (R : realType) (m : nat) (k : R) (hk : (0<=k)%R) (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second)
    origin axis Q (u h delta : R) (T : set Y) (Delta : \bar R) (nu : set P -> \bar R) :
  @is_euclidean_rectangular_box R m origin axis (fun _=>u) Q ->
  0<=u -> 0<h -> h<=delta -> (extended_metric_diameter T<=h%:E)%E ->
  ((Num.sqrt m.+1%:R*h)%:E<=Delta)%E ->
  @is_metric_scale_envelope R P (@nonempty_metric_sets R P)
    (fun j=>val j) (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation (addr_ge0 hk (ler0n R m))) (k+m%:R)%R (val j)) Delta nu ->
    (nu (metric_product_rectangle first second Q T)<=
      (real_euclidean_product_upper_coefficient m hk*(u+delta)^+m*
        (real_hausdorff_normalisation hk*real_power h k))%:E)%E.
Proof.
move=> hQ hu hh hdelta hT hcap hn.
pose c := @uniform_mesh_count R u h hu hh.
have hc := @uniform_mesh_count_specification R u h hu hh.
have hcpos : (0<c)%N := uniform_mesh_count_positive_law hc.
pose count : 'I_m -> nat := fun _=>c.
pose node (_ : 'I_m) := @equal_interval_partition R u c hu hcpos.
have hPart (i : 'I_m) := @equal_interval_partition_specification R u c hu hcpos.
have he := euclidean_box_orthonormal_law hQ.
pose centre : rectangular_grid_indices count ->
    inner_metric_space (@euclidean_inner_productP R m) :=
  @rectangular_grid_centres R m origin axis count node he.
have hGrid := @rectangular_grid_centres_specification R m origin axis count node he.
have hw i : u/(count i)%:R<=h := uniform_mesh_count_cell_width hc.
have hcover := rectangular_grid_ball_cover hQ hPart hGrid (ltW hh) hw.
pose r := Num.sqrt m%:R*h/2.
have hr : 0<=r by rewrite /r divr_ge0 ?ler0n //; exact: mulr_ge0 (sqrtr_ge0 _) (ltW hh).
have hrr : r+r=Num.sqrt m%:R*h by rewrite /r; lra.
have hball i : (extended_metric_diameter (metric_closed_ball (centre i) r)<=(Num.sqrt m%:R*h)%:E)%E.
  apply: (metric_diameter_least (extended_metric_diameter_specification _)).
  - rewrite lee_fin; exact: mulr_ge0 (sqrtr_ge0 _) (ltW hh).
  - move=> x y hx hy; rewrite lee_fin.
    by have hb := metric_closed_ball_diameter_bound hx hy; rewrite hrr in hb.
pose S i := metric_product_rectangle first second (metric_closed_ball (centre i) r) T.
have hdia i : (extended_metric_diameter (S i)<=(Num.sqrt m.+1%:R*h)%:E)%E.
  exact (@squared_product_cube_diameter_bound R P
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] Y
    pair first second hp (metric_closed_ball (centre i) r) T m h (ltW hh) (hball i) hT).
have hcov : metric_product_rectangle first second Q T `<=` \bigcup_i S i.
  move=> p [hq ht]; have [i _ hi] := hcover _ hq.
  exists i=> //; by split.
have hrad : 0<=Num.sqrt m.+1%:R*h := mulr_ge0 (sqrtr_ge0 _) (ltW hh).
have hb := @real_power_cutoff_finite_equal_diameter_cover R P (rectangular_grid_indices count)
  (real_hausdorff_normalisation (addr_ge0 hk (ler0n R m))) (k+m%:R)%R
  Delta nu (metric_product_rectangle first second Q T) S (Num.sqrt m.+1%:R*h)
  hn (ltW (real_hausdorff_normalisation_positive _)) (addr_ge0 hk (ler0n R m)) hrad hcap hdia hcov.
have hcard : #|rectangular_grid_indices count|=(c^m)%N.
  by rewrite rectangular_grid_cardinality /count prodr_const card_ord.
have hbudget := @uniform_mesh_count_power_budget R u h delta c m hu (ltW hh) hdelta hc.
have hfactor : 0<=real_hausdorff_normalisation (addr_ge0 hk (ler0n R m))*real_power (Num.sqrt m.+1%:R) (k+m%:R)*real_power h k.
  apply: mulr_ge0; last exact: real_power_nonnegative.
  exact: mulr_ge0 (ltW (real_hausdorff_normalisation_positive _)) (real_power_nonnegative _ _).
have hcost := ler_wpM2l hfactor hbudget.
have hidentity : real_euclidean_product_upper_coefficient m hk*(u+delta)^+m*
    (real_hausdorff_normalisation hk*real_power h k)=
    (real_hausdorff_normalisation (addr_ge0 hk (ler0n R m))*real_power (Num.sqrt m.+1%:R) (k+m%:R)*real_power h k)*(u+delta)^+m.
  rewrite [real_euclidean_product_upper_coefficient m hk*(u+delta)^+m*
    (real_hausdorff_normalisation hk*real_power h k)]mulrA
    [real_euclidean_product_upper_coefficient m hk*(u+delta)^+m*real_hausdorff_normalisation hk]mulrAC
    real_euclidean_product_coefficient_cost_identity; ring.
have hhp : real_power h (k+m%:R) = real_power h k*h^+m.
  by rewrite (real_power_add_exponents_positive _ _ hh)
    real_power_natural_exponent ?(ltW hh).
have hpower : real_power (Num.sqrt m.+1%:R*h) (k+m%:R) =
    real_power (Num.sqrt m.+1%:R) (k+m%:R)*(real_power h k*h^+m).
  by rewrite real_power_product ?sqrtr_ge0 ?(ltW hh) // hhp.
apply: le_trans hb _; rewrite lee_fin hcard natrX hpower hidentity.
have hleft : (c%:R)^+m*(real_hausdorff_normalisation (addr_ge0 hk (ler0n R m))*
    (real_power (Num.sqrt m.+1%:R) (k+m%:R)*(real_power h k*h^+m)))=
    (real_hausdorff_normalisation (addr_ge0 hk (ler0n R m))*real_power (Num.sqrt m.+1%:R) (k+m%:R)*real_power h k)*((c%:R)^+m*h^+m) by ring.
by rewrite hleft.
Qed.
