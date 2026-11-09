(** Federer (1969), 3.3.20, p. 306:
    coordinate-null original rectifiable sets have zero length. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExteriorIndices
  CoordinateProjection EuclideanLebesgueDimensions RectifiableSetUP
  RectifiableCoordinateMassUP RectifiableCoordinateProjectionBounds NullImageMultiplicityIntegral
  MeasureUP MeasureBasic HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_null_coordinate_images_mass_zero]:
    the application of 3.2.27 used in 3.3.20,
    p. 306. Every original coordinate image being
    null makes every original coordinate multiplicity
    integral zero. The proved coordinate upper bound
    then gives zero Hausdorff mass. Its existing
    source-measurability qualification is kept explicit;
    closed test hulls discharge it in the application. *)
Theorem rectifiable_null_coordinate_images_mass_zero (R:realType) m n
    (hmn:(m<=n)%N) (W:set (R_n R n)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  (forall lambda:Lambda n m,euclidean_lebesgue_measure m
    ((@coordinate_projection R n m lambda) @` W)=0) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W=0.
Proof.
move=>hRect hW hImages.
have hMasses:@is_rectifiable_coordinate_masses R m n W (fun _=>(0:R)%R).
  move=>lambda;exact:(@null_image_original_multiplicity_integral R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    (@euclidean_lebesgue_measure R m) (@coordinate_projection R n m lambda) W
    (euclidean_lebesgue_is_measure R m) (hImages lambda)).
have [_ hUpper]:=@federer_3_2_27 R m n hmn W (fun _=>0%R) hRect hW hMasses.
rewrite big1 // in hUpper.
apply/eqP;rewrite eq_le hUpper andTb.
exact:(@measure_nonnegative R [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
  (hausdorff_measure_is_measure _ _) W).
Qed.
