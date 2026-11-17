(** Section diameter control for the original cover argument
    in Federer (1969), 3.2.45, p. 280. Reuse
    the Cartesian projection bounds of 2.10.27, p. 190. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import MetricCartesianProductUP MetricDiameter HausdorffLipschitzCost
  CoveringFamilyUP EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates EuclideanMetricProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_cartesian_section_diameter_bound]: supporting
    finite cutoffs of the sections in Federer 3.2.45,
    p. 280. Identify the original section with the
    second-coordinate image of its first-coordinate fibre.
    The existing nonexpanding projection bound and
    diameter monotonicity give the original source
    diameter as an upper bound. Empty fibres and
    infinite source diameter remain. *)
Lemma metric_cartesian_section_diameter_bound (R : realType) (P X Y : metricType R)
    pair first second (hProduct : @is_metric_cartesian_product R P X Y pair first second)
    (A : set P) x :
  extended_metric_diameter (metric_product_section pair A x)<=extended_metric_diameter A.
Proof.
rewrite -(metric_product_section_image hProduct A x).
have hImage := extended_metric_diameter_lipschitz (metric_product_second_nonexpanding hProduct)
  (A `&` first @^-1` [set x]).
rewrite mul1e in hImage.
apply: le_trans hImage _; apply: extended_metric_diameter_mono=> p hp; exact hp.1.
Qed.

(** Source for [euclidean_block_section_diameter_bound]: supporting
    Euclidean section cutoff in Federer 3.2.45,
    p. 280. Use the already proved actual
    Euclidean Cartesian product laws, with either
    empty coordinate block allowed. *)
Corollary euclidean_block_section_diameter_bound (R : realType) m n
    (A : set (inner_metric_space (@euclidean_inner_productP R (m+n))))
    (y : inner_metric_space (@euclidean_inner_productP R m)) :
  extended_metric_diameter [set z | A (@euclidean_block_join R m n (y,z))]<=
    extended_metric_diameter A.
Proof. exact: metric_cartesian_section_diameter_bound (@euclidean_blocks_are_metric_product R m n) A y. Qed.

(** Source for [euclidean_bounded_block_section]: supporting
    bounded original convex sections in the first
    Fubini calculation of Federer 3.2.45, p. 279.
    The exact preceding diameter comparison retains
    boundedness without requiring compactness, closedness,
    nonempty fibres or source measurability. *)
Corollary euclidean_bounded_block_section (R : realType) m n
    (A : set (inner_metric_space (@euclidean_inner_productP R (m+n))))
    (y : inner_metric_space (@euclidean_inner_productP R m)) :
  metric_set_bounded A -> metric_set_bounded [set z | A (@euclidean_block_join R m n (y,z))].
Proof. move=> hBound; exact: le_lt_trans (euclidean_block_section_diameter_bound A y) hBound. Qed.
