(** Federer 2.10.45, pp. 202-203: prove the permitted coefficient
    interval nonempty in every real degree, including when V is null.
    Apply the actual product estimates to a finite positive-mass Cantor
    power already supplied by 2.10.29 and 3.4.4. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology ring lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates EuclideanSquaredProduct
  SquaredMetricProductLaws EuclideanCoordinateCubeLaws EuclideanLebesgueDimensions
  EuclideanLebesgueHaar RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffFinitePositiveSet RealHausdorffRectangleLowerBound
  RealEuclideanProductCoefficient RealEuclideanCubeProductUpperBound
  MeasureUP BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_euclidean_product_coefficient_interval]: supporting
    zero-mass case of Federer 2.10.45, pp. 202-203. Compare the proved
    upper and lower estimates on an actual positive finite real-degree
    test set, then cancel its positive mass. No Gamma ratio bound or
    nonempty coefficient interval is assumed. *)
Theorem real_euclidean_product_coefficient_interval (R : realType) m
    (k : R) (hk : (0 <= k)%R) :
  (real_euclidean_product_lower_coefficient m hk <=
    real_euclidean_product_upper_coefficient m hk)%R.
Proof.
have [q [V [hVp hVf]]] := @real_hausdorff_finite_positive_euclidean_set R k hk.
pose E n := inner_metric_space (@euclidean_inner_productP R n).
pose U : set (E m) := [set x | forall i, (0 <= x i <= 1)%R].
have hp := euclidean_blocks_are_squared_metric_product R m q.
have [hUc hUv] := @euclidean_unit_closed_cube R m.
have hUb : borel_set U := closed_borel_set (compact_closed
  (@metric_hausdorff R [the metricType R of E m]) hUc).
have hUm := @borel_regular_borel_measurable R [the topologicalType of E m]
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m)
  (euclidean_lebesgue_borel_regular R m) U hUb.
have ho i : (0%R : R_n R m) i = 0%R by rewrite ffunE.
have hQ := @euclidean_coordinate_cube_laws R m 0%R 0%R 1%R ho ler01.
rewrite add0r in hQ.
have hl := @real_hausdorff_euclidean_rectangle_lower_bound R m
  [the metricType R of E (m+q)%N] [the metricType R of E q]
  (fun y z => @euclidean_block_join R m q (y,z))
  (fun p => (@euclidean_block_split R m q p).1)
  (fun p => (@euclidean_block_split R m q p).2)
  (squared_metric_product_cartesian hp) k hk U V hUm.
have hu := @real_hausdorff_euclidean_cube_product_upper_bound R m k hk
  [the metricType R of E (m+q)%N] [the metricType R of E q]
  (fun y z => @euclidean_block_join R m q (y,z))
  (fun p => (@euclidean_block_split R m q p).1)
  (fun p => (@euclidean_block_split R m q p).2)
  hp 0%R (@coordinate_basis R m) U 1 V hQ ler01 hVf.
pose A := (real_hausdorff_normalisation hk*real_hausdorff_normalisation (ler0n R m)/
  real_hausdorff_normalisation (addr_ge0 hk (ler0n R m)))%R.
have hA : (0 < A)%R.
  apply: divr_gt0; last exact: real_hausdorff_normalisation_positive.
  exact: mulr_gt0 (real_hausdorff_normalisation_positive hk)
    (real_hausdorff_normalisation_positive (ler0n R m)).
have hAE : 0 <= A%:E by rewrite lee_fin; exact: ltW hA.
have hfinite : @real_hausdorff_measure R [the metricType R of E q] k hk V \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (@real_hausdorff_measure_is_measure R _ k hk) V)).
  exact: hVf.
pose v := fine (@real_hausdorff_measure R [the metricType R of E q] k hk V).
have hve : @real_hausdorff_measure R [the metricType R of E q] k hk V = v%:E.
  by rewrite /v fineK.
have hv : (0 < v)%R by move: hVp; rewrite hve lte_fin.
rewrite /U hUv mul1e in hl.
rewrite expr1n mulr1 in hu.
have hb := lee_wpmul2l hAE hu.
have hh := le_trans hl hb.
rewrite -/A hve -!EFinM lee_fin in hh.
pose L := real_euclidean_product_lower_coefficient m hk.
have hL := real_euclidean_product_lower_coefficient_positive m hk.
have hLA : (L*A = 1)%R.
  rewrite /L /A /real_euclidean_product_lower_coefficient.
  field; rewrite ?gt_eqF //; exact: real_hausdorff_normalisation_positive.
have hOne : (1 <= A*real_euclidean_product_upper_coefficient m hk)%R by nra.
have hmul := ler_wpM2l (ltW hL) hOne.
by rewrite mulr1 mulrA hLA mul1r in hmul.
Qed.
