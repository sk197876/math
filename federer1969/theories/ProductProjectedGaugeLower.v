(** Federer (1969), 2.10.46, p. 204: supporting projected-volume lower bound
    for the Gross product equality. The block projection (x,y) maps to
    (x,q(y)) has rectangle image, whose volume factors by 2.6.2(2), p. 115,
    and the block identification of 2.6.5, p. 120. Projection images of
    Borel sets are measurable by 2.2.13, pp. 69–70; they are not assumed
    Borel. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanBlockProjection EuclideanBlockMeasure MetricProductRectangles
  EuclideanLebesgueDimensions EuclideanProjectionSpace ProjectionMultiplicityIntegral
  CoordinateProjection TopologicalBorel ProjectedVolumeGauge MeasureUP MeasurePushforward ProductRectangleValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [block_projected_rectangle_volume]: supporting
    exact volume of a block-projected rectangle in the
    lower inequality of 2.10.46, p. 204. The first
    factor is Lebesgue measurable; the second is Borel so
    that its continuous projection is Lebesgue measurable. *)
Lemma block_projected_rectangle_volume (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n)))
    (q : {linear R_n R n -> R_n R k}) :
  measure_measurable (@euclidean_lebesgue_measure R m) U -> borel_set V -> O_star q ->
  euclidean_lebesgue_measure (m+k) ((@euclidean_block_projection R m n k q) @`
    metric_product_rectangle (fun z=>(@euclidean_block_split R m n z).1)
      (fun z=>(@euclidean_block_split R m n z).2) U V)=
  (euclidean_lebesgue_measure m U*euclidean_lebesgue_measure k (q @` V))%E.
Proof.
move=> hU hV hq.
have [p hp] := euclidean_projection_linear_complete hq.
have heq : (euclidean_projection_linear p : _ -> _)=q := funext hp.
have hqV := euclidean_projection_borel_image_measurable p hV.
rewrite heq in hqV.
rewrite euclidean_block_projection_rectangle.
change (measure_pushforward (@euclidean_block_split R m k) (@euclidean_lebesgue_measure R (m+k))
  (U `*` (q @` V))=(euclidean_lebesgue_measure m U*euclidean_lebesgue_measure k (q @` V))%E).
rewrite euclidean_block_measure.
exact: product_measure_rectangle_value hU hqV.
Qed.

(** Source for [product_projected_gauge_lower_finite_first]:
    supporting gauge lower bound for the opposite inequality
    of 2.10.46, p. 204. Positive finite first volume
    allows passage through the projection supremum; the subsequent
    Borel partition argument produces the Gross measure. *)
Theorem product_projected_gauge_lower_finite_first (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) (u : R) :
  measure_measurable (@euclidean_lebesgue_measure R m) U -> borel_set V ->
  0<u -> euclidean_lebesgue_measure m U=u%:E ->
  (u%:E*@projected_volume_gauge R n k V<=
    @projected_volume_gauge R (m+n) (m+k) (metric_product_rectangle
      (fun z=>(@euclidean_block_split R m n z).1)
      (fun z=>(@euclidean_block_split R m n z).2) U V))%E.
Proof.
move=> hU hV hu hvol.
rewrite -lee_pdivlMl //; apply: projected_volume_gauge_least_bound=> q hq.
rewrite lee_pdivlMl //.
have hh := @projected_volume_gauge_projection_bound R (m+n) (m+k)
  (metric_product_rectangle (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)
  (GRing.Linear.clone _ _ _ _ (@euclidean_block_projection R m n k q) _)
  (@euclidean_block_projection_orthogonal R m n k q hq).
rewrite (@block_projected_rectangle_volume R m n k U V q hU hV hq) hvol in hh.
exact hh.
Qed.
