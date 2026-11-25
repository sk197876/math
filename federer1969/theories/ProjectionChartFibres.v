(** Federer (1969), 2.10.46, p. 203: the fibres used in the projected-volume
    estimate have diameter at most that of the set. Derive this from the
    abstract orthogonal chart, rather than its selected implementation.
    Source context: EuclideanRightBlockProjection.v and
    ProjectionChartFubini.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  OrthogonalMaps OrthogonalProjectionChartUP OrthogonalProjectionChartLaws
  EuclideanBlockCoordinates EuclideanSquaredProduct SquaredMetricProductLaws
  ProductSections MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Fibres.
Variable R : realType.
Variables m k : nat.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Variables p : {linear R_n R (m+k) -> R_n R k}.
Variables f g : {linear R_n R (m+k) -> R_n R (m+k)}.
Hypothesis hc : is_orthogonal_projection_chart p f g.
Local Notation H := ((g : E (m+k) -> E (m+k)) \o (@euclidean_block_join R m k)).

(** Source for [projection_chart_fibre_distance]: supporting
    isometry of each fibre coordinate in the Fubini argument
    of 2.10.46, p. 203, from the orthogonal chart laws. *)
Lemma projection_chart_fibre_distance (x u : E m) (y : E k) :
  mdist (H (x,y)) (H (u,y))=mdist x u.
Proof.
change (mdist (g (euclidean_block_join (x,y)) : E (m+k)) (g (euclidean_block_join (u,y)) : E (m+k))=mdist x u).
rewrite inner_metric_distanceE -linearB
  (orthogonal_map_norm (@euclidean_inner_productP R (m+k))
    (@euclidean_inner_productP R (m+k)) (projection_chart_backward_orthogonal hc)).
change (mdist (euclidean_block_join (x,y)) (euclidean_block_join (u,y))=mdist x u).
exact (squared_metric_product_first_slice
  (euclidean_blocks_are_squared_metric_product R m k) y x u).
Qed.

(** Source for [projection_chart_fibre_diameter]: supporting
    diameter bound for sections in 2.10.46, p. 203.
    The bound also includes empty sections and infinite diameters. *)
Lemma projection_chart_fibre_diameter (S : set (E (m+k))) (y : E k) :
  (extended_metric_diameter (product_horizontal_section (H @^-1` S) y)<=
    extended_metric_diameter S)%E.
Proof.
apply: (metric_diameter_least (extended_metric_diameter_specification _)).
- exact: metric_diameter_nonnegative (extended_metric_diameter_specification S).
- move=> x u hx hu.
  rewrite -(projection_chart_fibre_distance x u y).
  exact (@metric_diameter_upper R [the metricType R of E (m+k)] S _
    (extended_metric_diameter_specification S) (H (x,y)) (H (u,y)) hx hu).
Qed.

(** Source for [projection_chart_fibre_outside_image]: supporting
    vanishing of fibres off p(S) in the Fubini estimate of
    2.10.46, p. 203. It follows from the projection equation. *)
Lemma projection_chart_fibre_outside_image (S : set (E (m+k))) (y : E k) :
  ~ (p @` S) y -> product_horizontal_section (H @^-1` S) y=set0.
Proof.
move=> hy; apply/seteqP; split=> x // hx; apply: hy.
exists (H (x,y)); first exact hx.
exact (@projection_chart_fibre_coordinate R m k p f g hc x y).
Qed.
End Fibres.
