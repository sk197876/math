(** Federer (1969), 2.10.45, pp. 202–203: the lower and upper numerical
    bounds for c are compatible even when H^k(V)=0. Prove this using the
    actual Euclidean product of two unit cubes, whose factors have Hausdorff
    measure one by 2.10.35, p. 197. The coefficient interval is not assumed
    nonempty. Source context: SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology ring.
From Federer Require Import ExtendedRealOrderTopology GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates EuclideanSquaredProduct
  SquaredMetricProductLaws EuclideanCoordinateCubeLaws EuclideanBallVolume
  EuclideanLebesgue EuclideanLebesgueHaar EuclideanLebesgueDimensions EuclideanHausdorffLebesgue
  HausdorffMeasure HausdorffProductSliceMeasure HausdorffRectangleLowerBound
  EuclideanProductCoefficient EuclideanCubeProductUpperBound
  MeasureUP BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_product_lower_coefficient]: direct
    lower bound alpha(k+m)/(alpha(k) alpha(m))
    for c, algebraically equivalent to the first
    displayed inequality in 2.10.45, p. 202. *)
Definition euclidean_product_lower_coefficient (R : realType) m k : R :=
  euclidean_unit_ball_volume R (k+m)/
    (euclidean_unit_ball_volume R k*euclidean_unit_ball_volume R m).

(** Source for [euclidean_product_lower_coefficient_positive]: supporting
    positivity of the lower endpoint in 2.10.45,
    p. 202, from positive unit-ball volumes in 2.7.16(1). *)
Lemma euclidean_product_lower_coefficient_positive (R : realType) m k :
  0<euclidean_product_lower_coefficient R m k.
Proof.
rewrite /euclidean_product_lower_coefficient; apply: divr_gt0.
- exact: (euclidean_unit_ball_volumeE R (k+m)).2.
- exact: mulr_gt0 (euclidean_unit_ball_volumeE R k).2 (euclidean_unit_ball_volumeE R m).2.
Qed.

(** Source for [euclidean_product_coefficient_interval]: supporting
    existence of a permitted c in the zero-mass case
    of 2.10.45, pp. 202–203. Apply the proved
    product bounds to positive-mass Euclidean unit cubes;
    no special convention for a zero factor is needed. *)
Theorem euclidean_product_coefficient_interval (R : realType) m k :
  euclidean_product_lower_coefficient R m k<=euclidean_product_upper_coefficient R m k.
Proof.
pose E n := inner_metric_space (@euclidean_inner_productP R n).
pose U : set (E m) := [set x | forall i, 0<=x i<= 1].
pose V : set (E k) := [set x | forall i, 0<=x i<= 1].
have hp := euclidean_blocks_are_squared_metric_product R m k.
have [hUc hUv] := @euclidean_unit_closed_cube R m.
have [hVc hVv] := @euclidean_unit_closed_cube R k.
have hUb : borel_set U := closed_borel_set (compact_closed
  (@metric_hausdorff R [the metricType R of E m]) hUc).
have hUm := @borel_regular_borel_measurable R [the topologicalType of E m]
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m)
  (euclidean_lebesgue_borel_regular R m) U hUb.
have hHV : @hausdorff_measure R [the metricType R of E k] k V= 1%E.
  by rewrite (euclidean_hausdorff_spherical_lebesgue V).1 /V hVv.
have hVf : (@hausdorff_measure R [the metricType R of E k] k V< +oo)%E by rewrite hHV; exact: ltry.
have ho i : (0 : R_n R m) i=0 by rewrite ffunE.
have hQ := @euclidean_coordinate_cube_laws R m 0 0 1 ho ler01.
rewrite add0r in hQ.
have hl := @hausdorff_euclidean_rectangle_lower_bound R m
  [the metricType R of E (m+k)] [the metricType R of E k]
  (fun y z=>@euclidean_block_join R m k (y,z))
  (fun p=>(@euclidean_block_split R m k p).1) (fun p=>(@euclidean_block_split R m k p).2)
  (squared_metric_product_cartesian hp) k U V hUm.
have hu := @hausdorff_euclidean_cube_product_upper_bound R m k
  [the metricType R of E (m+k)] [the metricType R of E k]
  (fun y z=>@euclidean_block_join R m k (y,z))
  (fun p=>(@euclidean_block_split R m k p).1) (fun p=>(@euclidean_block_split R m k p).2)
  hp 0 (@coordinate_basis R m) U 1 V hQ ler01 hVf.
rewrite hHV /U hUv mul1e in hl.
rewrite hHV expr1n mulr1 mule1 in hu.
pose A := euclidean_unit_ball_volume R k*euclidean_unit_ball_volume R m/
  euclidean_unit_ball_volume R (k+m).
have hA : 0<=A.
  apply: divr_ge0; last exact: ltW (euclidean_unit_ball_volumeE R (k+m)).2.
  exact: mulr_ge0 (ltW (euclidean_unit_ball_volumeE R k).2) (ltW (euclidean_unit_ball_volumeE R m).2).
have hAE : (0<=A%:E)%E by rewrite lee_fin.
have hb := lee_wpmul2l hAE hu.
have hh := le_trans hl hb; rewrite -EFinM lee_fin in hh.
pose L := euclidean_product_lower_coefficient R m k.
have hL := euclidean_product_lower_coefficient_positive R m k.
have hLA : L*A= 1.
  rewrite /L /A /euclidean_product_lower_coefficient.
  field; rewrite ?gt_eqF //; exact: (euclidean_unit_ball_volumeE R _).2.
have ht := ler_wpM2l (ltW hL) hh.
by rewrite mulr1 mulrA hLA mul1r in ht.
Qed.
