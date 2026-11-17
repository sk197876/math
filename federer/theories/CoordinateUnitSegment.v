(** Federer 3.2.26, pp. 261-262: actual finite rectifiable
    coordinate segments. This supporting connection tests the
    exponent comparison in 3.2.45, p. 279, using an original
    geometric set rather than an abstract convex function. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanCoordinateMetric EuclideanCoordinateLineTopology EuclideanOneCoordinate
  EuclideanLebesgueBoxes EuclideanLebesgueHaar EuclideanCoordinateTopology HausdorffMeasure HausdorffLengthCompatibility
  HausdorffCoordinateLines RectifiableSetUP RectifiableFiniteHausdorffMass
  EuclideanLipschitzRectifiableImage LipschitzUP CoveringFamilyUP CompactMetricBounded
  CompactSetDistanceProfile LebesgueScalarMeasure MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coordinate_unit_segment_rectifiable]: supporting
    original line-segment case of Federer 3.2.14(1), p. 251,
    used through the full equality 3.2.26 in the regression for
    3.2.45, p. 279. Reuse the bounded Euclidean parameter and
    already proved coordinate-line isometry in every ambient dimension. *)
Lemma coordinate_unit_segment_rectifiable (R:realType) n (i:'I_n)
    (v:inner_metric_space (@euclidean_inner_productP R n)):
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) 1
    (@euclidean_coordinate_line R n i v @` `[(0%R:R),1%R]).
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose L:=@euclidean_coordinate_line R n i v.
pose Q:set X:=[set x|forall j,(0<=x j<= 1)%R].
pose F (x:X):Y:=L (euclidean_one_project x).
have hCompact:@compact X Q:=@euclidean_closed_box_compact R 1%N
  (fun _:'I_1=>0%R) (fun _:'I_1=>1%R).
have hNonempty:Q!=set0.
  exists (0%R:X);move=> j;by rewrite ffunE ler01 lexx.
pose C:compact_metric_set X:=exist _ Q (mem_set (conj hCompact hNonempty)).
have hBounded:metric_set_bounded Q:=compact_metric_diameter_finite C.
have hLip:@is_metric_lipschitz R X Y Q F.
  exists 1%R;split;first exact:ltr01;split;first exact:ler01.
  move=>x y _ _;rewrite /F euclidean_coordinate_line_distance mul1r.
  exact:(@euclidean_coordinate_nonexpanding R 1 ord0 x y).
have hRect:=euclidean_lipschitz_bounded_image_rectifiable hBounded hLip.
have hImage:F @` Q=L @` `[(0%R:R),1%R].
  apply/seteqP;split.
  - move=>y [x hx <-];exists (euclidean_one_project x);last reflexivity.
    exact:(hx ord0).
  - move=>y [t ht <-];exists (euclidean_one_embed t);last by rewrite /F euclidean_one_embedK.
    move=>j;by rewrite /euclidean_one_embed ffunE.
by rewrite -hImage.
Qed.

(** Source for [coordinate_unit_segment_measure_rectifiable]:
    finite (H^1,1)-rectifiability required by Federer 3.2.26,
    pp. 261-262, for the source-estimate test in 3.2.45, p. 279.
    Finiteness follows from the existing rectifiable-mass theorem. *)
Lemma coordinate_unit_segment_measure_rectifiable (R:realType) n (i:'I_n)
    (v:inner_metric_space (@euclidean_inner_productP R n)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) 1) 1
    (@euclidean_coordinate_line R n i v @` `[(0%R:R),1%R]).
Proof. exact:rectifiable_hausdorff_measure_rectifiable (coordinate_unit_segment_rectifiable i v). Qed.

(** Source for [coordinate_unit_segment_hausdorff_mass]: the
    actual unit length from Federer 2.10.7, p. 175, via the
    coordinate-line measure law, used to test 3.2.45, p. 279. *)
Lemma coordinate_unit_segment_hausdorff_mass (R:realType) n (i:'I_n)
    (v:inner_metric_space (@euclidean_inner_productP R n)):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 1
    (@euclidean_coordinate_line R n i v @` `[(0%R:R),1%R])= 1.
Proof.
rewrite hausdorff_measure_one_length (hausdorff_coordinate_segment_measure _ _ ler01).
by rewrite subr0.
Qed.
