(** Federer (1969), 2.10.46, p. 203: the common-factor observation gives the
    first displayed volume estimate for every projected rectangle. The
    outer-measure Fubini bound is used without additional measurability
    hypotheses. Taking the supremum then compares the projected-volume
    gauges of 2.10.4, p. 172. Source context:
    EuclideanRightBlockProjection.v and OrthogonalProjectionVolumeBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  CoordinateProjection EuclideanProjectionSpace EuclideanBlockCoordinates
  EuclideanProductProjectionFactor ProductProjectionImage OrthogonalProjectionVolumeBound
  MetricProductRectangles MetricDiameterUP MetricDiameter MetricDiameterMaps
  HausdorffDiameterCost ExtendedSupremumPowers EuclideanLebesgueDimensions
  MeasureUP MeasureBasic ProjectedVolumeGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_projection_diameter_cost_bound]: supporting
    nonincrease of the m-dimensional diameter cost under any
    orthogonal projection, used in 2.10.46, p. 203. *)
Lemma orthogonal_projection_diameter_cost_bound (R : realType) n l m
    (f : {linear R_n R n -> R_n R l})
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  O_star f -> (hausdorff_diameter_cost m
    ((f : inner_metric_space (@euclidean_inner_productP R n) ->
      inner_metric_space (@euclidean_inner_productP R l)) @` A)<=hausdorff_diameter_cost m A)%E.
Proof.
move=> hf; have [q hq] := euclidean_projection_linear_complete hf.
rewrite /hausdorff_diameter_cost /hausdorff_power_cost.
apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW (hausdorff_normalisation_positive R m).
apply: nonnegative_extended_power_monotone; first exact: metric_diameter_nonnegative (extended_metric_diameter_specification _).
apply: extended_metric_diameter_nonexpanding=> x y.
rewrite -!(hq _); exact: euclidean_projection_nonexpanding.
Qed.

(** Source for [product_projection_volume_bound]: direct
    first inequality in the display of 2.10.46, p. 203,
    with existence of p and q discharged by 1.7.4. The
    nonempty first factor is generalised from the printed ball. *)
Theorem product_projection_volume_bound (R : realType) m n k
    (f : {linear R_n R (m+n) -> R_n R (m+k)})
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (T : set (inner_metric_space (@euclidean_inner_productP R n))) :
  O_star f -> S !=set0 -> exists q : {linear R_n R n -> R_n R k}, O_star q /\
  (euclidean_lebesgue_measure (m+k) (f @` (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) S T))<=
   euclidean_lebesgue_measure k (q @` T)*hausdorff_diameter_cost m
    (metric_product_rectangle (fun z=>(@euclidean_block_split R m n z).1)
      (fun z=>(@euclidean_block_split R m n z).2) S T))%E.
Proof.
move=> hf hS; have [p [q [hp [hq he]]]] := euclidean_product_projection_factor hf.
exists q; split=> //.
pose A := metric_product_rectangle (fun z=>(@euclidean_block_split R m n z).1)
  (fun z=>(@euclidean_block_split R m n z).2) S T.
have hh := @orthogonal_projection_outer_volume_bound R m k p (f @` A) hp.
have him := @product_projection_factor_image R m n k f p q S T he hS.
rewrite him in hh.
apply: le_trans hh _; apply: lee_wpmul2l;
  first exact (measure_nonnegative (euclidean_lebesgue_is_measure R k) (q @` T)).
exact: orthogonal_projection_diameter_cost_bound hf.
Qed.

(** Source for [product_projected_volume_gauge_bound]: supporting
    supremum over f of the projection estimate in 2.10.46,
    p. 203. It is the common generator bound for the
    Gross and convex Caratheodory product estimates. *)
Theorem product_projected_volume_gauge_bound (R : realType) m n k
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (T : set (inner_metric_space (@euclidean_inner_productP R n))) : S !=set0 ->
  (projected_volume_gauge (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) S T)<=
   projected_volume_gauge k T*hausdorff_diameter_cost m
    (metric_product_rectangle (fun z=>(@euclidean_block_split R m n z).1)
      (fun z=>(@euclidean_block_split R m n z).2) S T))%E.
Proof.
move=> hS; apply: projected_volume_gauge_least_bound=> f hf.
have [q [hq hb]] := @product_projection_volume_bound R m n k f S T hf hS.
apply: le_trans hb _; apply: lee_wpmul2r; first exact: hausdorff_diameter_cost_nonnegative.
exact (@projected_volume_gauge_projection_bound R n k T q hq).
Qed.
