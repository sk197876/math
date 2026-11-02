(** Federer (1969), 3.2.36, p. 273:
    actual distance to the Cartesian product
    obeys the squared Pythagorean formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import CompactSetDistanceProfile CompactProfileNearest
  SquaredMetricProductUP SquaredMetricProductLaws MetricSetDistanceUP MetricSetDistanceBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_squared_product_set_distance]:
    supporting the exact tube-fibre identity in
    Federer 3.2.36, p. 273.
    The squared distance to a Cartesian
    product is the sum of squared actual
    factor distances. Only local nearest points
    in the two compact factors are used;
    no global nearest-point map is selected.
    This supporting metric generalization uses
    the existing abstract squared-product laws,
    without convexity or Euclidean dimensions. *)
Theorem compact_squared_product_set_distance (R:realType) (Z X Y:metricType R)
    (pair:X->Y->Z) first second
    (hp:is_squared_metric_product pair first second)
    (A:compact_metric_set X) (B:compact_metric_set Y) (d:Z->R):
  is_metric_set_distance [set z|val A (first z) /\val B (second z)] d ->forall z,
  d z^+2=compact_set_distance_profile A (first z)^+2+
    compact_set_distance_profile B (second z)^+2.
Proof.
move=>hD z.
have [a [ha hNearA]]:=compact_profile_nearest_point A (first z).
have [b [hb hNearB]]:=compact_profile_nearest_point B (second z).
have hPair:[set z|val A (first z) /\val B (second z)] (pair a b).
  change (val A (first (pair a b)) /\val B (second (pair a b))).
  by rewrite (squared_product_first_pair_law hp) (squared_product_second_pair_law hp); split.
have hSquared:mdist z (pair a b)^+2=
    compact_set_distance_profile A (first z)^+2+compact_set_distance_profile B (second z)^+2.
  by rewrite (squared_metric_product_distance_coordinates hp)
    (squared_product_first_pair_law hp) (squared_product_second_pair_law hp) hNearA hNearB.
have hLeast q:[set z|val A (first z) /\val B (second z)] q ->mdist z (pair a b)<=mdist z q.
  move=>[hqA hqB].
  rewrite -(ler_sqr (mdist_ge0 _ _) (mdist_ge0 _ _)) hSquared
    (squared_metric_product_distance_coordinates hp).
  apply:lerD.
  - rewrite (ler_sqr (metric_set_distance_nonnegative (compact_set_distance_profile_specification A) _)
      (mdist_ge0 _ _)).
    exact:(@metric_set_distance_lower R X (val A) (compact_set_distance_profile A) (compact_set_distance_profile_specification A) (first z) (first q) hqA).
  - rewrite (ler_sqr (metric_set_distance_nonnegative (compact_set_distance_profile_specification B) _)
      (mdist_ge0 _ _)).
    exact:(@metric_set_distance_lower R Y (val B) (compact_set_distance_profile B) (compact_set_distance_profile_specification B) (second z) (second q) hqB).
have hDistance:d z=mdist z (pair a b).
  apply/eqP; rewrite eq_le; apply/andP; split.
  - exact:(@metric_set_distance_lower R Z [set z|val A (first z) /\val B (second z)] d hD z (pair a b) hPair).
  - exact:(@metric_set_distance_greatest R Z [set z|val A (first z) /\val B (second z)] d hD z (mdist z (pair a b)) hLeast).
by rewrite hDistance hSquared.
Qed.
