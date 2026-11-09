(** Federer (1969), 3.3.20, p. 306:
    the original square of a compact null line set is purely length unrectifiable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanRealPlane EuclideanOneCoordinate PlanePairNormGeometry
  EuclideanCantorProduct CantorSquareCompactMass EuclideanCantorProductRegular CoordinateProjection ExteriorIndices
  EuclideanLebesgueDimensions EuclideanScalarLength LebesgueScalarMeasure
  RectifiableSetUP ClosedNullCoordinatePure MeasureUP MeasureAlmostBasic HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_null_factor_square_pure_length]:
    the original-coordinate argument on p. 306
    of 3.3.20. Both coordinate images of
    the actual compact square lie in the original
    null line set. Closed rectifiable test hulls
    discharge the existing 3.2.27 qualification,
    preserving arbitrary original test subsets. *)
Theorem compact_null_factor_square_pure_length (R:realType)
    (A:set (real_line_metric R)):
  compact A ->lebesgue_scalar_measure A=0 ->
  is_purely_measure_m_unrectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R 2)) 1) 1 (euclidean_cantor_product A A).
Proof.
move=>hCompact hNull.
have hCoordinates x:euclidean_cantor_product A A x ->forall i:'I_2,A (x i).
  move=>[hx hy] [i hi];case:i hi=>[|[|i]] hi;last by [].
  - have hIndex:(Ordinal hi:'I_2)=ord0 by apply:val_inj.
    by rewrite hIndex -real_plane_first_coordinateE.
  - have hIndex:(Ordinal hi:'I_2)=ord_max by apply:val_inj.
    by rewrite hIndex -real_plane_second_coordinateE.
apply:(@closed_null_coordinate_images_pure R 1 2 (erefl true)).
- exact:compact_closed (@metric_hausdorff R _) (euclidean_cantor_product_compact hCompact hCompact).
- move=>lambda;rewrite euclidean_one_measure_scalar_image image_comp.
  apply:(@measure_null_subset R [the choiceType of real_line_metric R]
    (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ A _ hNull).
  move=>t [x hx <-].
  change (A ((@coordinate_projection R 2 1 lambda x) ord0)).
  rewrite coordinate_projectionE.
  exact:(@hCoordinates x hx (tnth (val lambda) ord0)).
Qed.
