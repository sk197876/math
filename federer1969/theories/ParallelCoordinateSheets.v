(** Federer (1969), 3.2.27, pp. 262–263: local
    source-measurability correction, absent from the working
    erratum. These supporting line computations construct
    the two-sheet counterexample from 2.2.4, p. 62.
    The coordinate lines themselves are those already
    formalised for 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanCoordinateMetric EuclideanCoordinateLineTopology EuclideanOneCoordinate
  EuclideanLebesgueBoxes EuclideanLebesgueHaar EuclideanCoordinateTopology
  HausdorffMeasure HausdorffLengthCompatibility HausdorffCoordinateLines HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel
  CoveringFamilyUP CompactMetricBounded CompactSetDistanceProfile
  RectifiableSetUP RectifiableElementary RectifiableUnion EuclideanLipschitzRectifiableImage
  LipschitzUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [parallel_coordinate_line_first]: supporting
    coordinate identity for the local counterexample to
    the unrestricted upper bound in 3.2.27, pp. 262–263.
    The horizontal coordinate of the height-h line is t. *)
Lemma parallel_coordinate_line_first (R:realType) (h:R) (t:real_line_metric R):
  @euclidean_coordinate_line R 2 ord0 (h*:@coordinate_basis R 2 ord_max)%R t ord0=t.
Proof.
rewrite /euclidean_coordinate_line /coordinate_basis !ffunE /=.
change ((h*0+t*1)%R=t); by rewrite mulr0 mulr1 add0r.
Qed.

(** Source for [parallel_coordinate_line_second]: supporting
    coordinate identity for the local counterexample to
    3.2.27, pp. 262–263. The vertical coordinate
    of the height-h line is exactly h. *)
Lemma parallel_coordinate_line_second (R:realType) (h:R) (t:real_line_metric R):
  @euclidean_coordinate_line R 2 ord0 (h*:@coordinate_basis R 2 ord_max)%R t ord_max=h.
Proof.
rewrite /euclidean_coordinate_line /coordinate_basis !ffunE /=.
change ((h*1+t*0)%R=h); by rewrite mulr1 mulr0 addr0.
Qed.

(** Source for [parallel_coordinate_line_separation]: the
    disjoint horizontal sheets used to test 3.2.27,
    pp. 262–263. Equal points on parallel coordinate
    lines must have the same height. *)
Lemma parallel_coordinate_line_separation (R:realType) (h k:R) (s t:real_line_metric R):
  @euclidean_coordinate_line R 2 ord0 (h*:@coordinate_basis R 2 ord_max)%R s=
  @euclidean_coordinate_line R 2 ord0 (k*:@coordinate_basis R 2 ord_max)%R t ->h=k.
Proof.
move=>he; have hEqual:=congr1 (fun x:R_n R 2=>x ord_max) he.
by rewrite !parallel_coordinate_line_second in hEqual.
Qed.

(** Source for [parallel_coordinate_sheet_mass]: exact
    outer length of each sheet in the local counterexample
    to 3.2.27, pp. 262–263, by the all-set
    coordinate-line identity of 2.10.7, p. 175. No
    source measurability is assumed or deduced. *)
Lemma parallel_coordinate_sheet_mass (R:realType) (h:R) (A:set (real_line_metric R)):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
    (@euclidean_coordinate_line R 2 ord0 (h*:@coordinate_basis R 2 ord_max)%R @` A)=
    @lebesgue_scalar_measure R A.
Proof.
rewrite hausdorff_measure_one_length; exact:hausdorff_coordinate_line_measure.
Qed.

(** Source for [parallel_coordinate_segment_rectifiable]:
    actual one-rectifiability of each containing segment
    in the local correction to 3.2.27, pp. 262–263.
    The bounded one-coordinate Euclidean parameter and the
    isometric line map satisfy 3.2.14(1), p. 251. *)
Lemma parallel_coordinate_segment_rectifiable (R:realType) (h:R):
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R 2)) 1
    (@euclidean_coordinate_line R 2 ord0 (h*:@coordinate_basis R 2 ord_max)%R @` `[(0%R:R),1%R]).
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose Y:=inner_metric_space (@euclidean_inner_productP R 2).
pose L:=@euclidean_coordinate_line R 2 ord0 (h*:@coordinate_basis R 2 ord_max)%R.
pose Q:set X:=[set x|forall i,0<=x i<=1]%R.
pose F (x:X):Y:=L (euclidean_one_project x).
have hCompact:@compact X Q:=@euclidean_closed_box_compact R 1%N (fun _:'I_1=>0%R) (fun _:'I_1=>1%R).
have hNonempty:Q!=set0.
  exists (0%R:X); move=>i; by rewrite ffunE ler01 lexx.
pose C:compact_metric_set X:=exist _ Q (mem_set (conj hCompact hNonempty)).
have hBounded:metric_set_bounded Q:=compact_metric_diameter_finite C.
have hLip:@is_metric_lipschitz R X Y Q F.
  exists 1%R; split; first exact:ltr01; split; first exact:ler01.
  move=>x y _ _; rewrite /F euclidean_coordinate_line_distance mul1r.
  exact:(@euclidean_coordinate_nonexpanding R 1 ord0 x y).
have hRect:=euclidean_lipschitz_bounded_image_rectifiable hBounded hLip.
have hImage:F @` Q=L @` `[(0%R:R),1%R].
  apply/seteqP; split.
  - move=>y [x hx <-]; exists (euclidean_one_project x); last reflexivity.
    exact:(hx ord0).
  - move=>y [t ht <-]; exists (euclidean_one_embed t); last by rewrite /F euclidean_one_embedK.
    move=>i; by rewrite /euclidean_one_embed ffunE.
by rewrite -hImage.
Qed.

(** Source for [parallel_coordinate_sheets_union_mass]: the
    exact outer length in the local counterexample to
    the unrestricted upper inequality in 3.2.27,
    pp. 262–263. A closed containing segment separates
    the two possibly nonmeasurable sheets, so the measure
    splitting law applies without assuming either sheet
    measurable. *)
Lemma parallel_coordinate_sheets_union_mass (R:realType)
    (V Z:set (real_line_metric R)):
  V `<=` `[(0%R:R),1%R] ->
  let L0:=@euclidean_coordinate_line R 2 ord0 (0%R:R_n R 2) in
  let L1:=@euclidean_coordinate_line R 2 ord0 (@coordinate_basis R 2 ord_max) in
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
    ((L0 @` V) `|` (L1 @` Z))=lebesgue_scalar_measure V+lebesgue_scalar_measure Z.
Proof.
move=>hV L0 L1.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose H:=@hausdorff_measure R X 1.
pose W:=(L0 @` V) `|` (L1 @` Z).
pose C:=L0 @` `[(0%R:R),1%R].
change (H W=lebesgue_scalar_measure V+lebesgue_scalar_measure Z).
have hC:measure_measurable H C.
  apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R X 1)
    (@hausdorff_measure_borel_regular R X 1)).
  exact:euclidean_coordinate_segment_borel.
have hFirst t:(L0 t) ord_max=0%R.
  have h:=@parallel_coordinate_line_second R 0%R t; by rewrite scale0r in h.
have hSecond t:(L1 t) ord_max= 1%R.
  have h:=@parallel_coordinate_line_second R 1%R t; by rewrite scale1r in h.
have hApart s t:L0 s<>L1 t.
  move=>he; have h:=congr1 (fun x:X=>x ord_max) he.
  rewrite hFirst hSecond in h.
  have hBad:(0%R:R)!=1%R by rewrite eq_sym oner_eq0.
  by rewrite h eqxx in hBad.
have hIntersection:W `&` C=L0 @` V.
  apply/seteqP; split.
  - move=>x [[hx|hx] hc]; first exact hx.
    have [s hs hS]:=hc; have [t ht hT]:=hx.
    exfalso; exact:(hApart s t (eq_trans hS (esym hT))).
  - move=>x [s hs <-]; split.
    + left; by exists s.
    + exists s; first exact:hV s hs; reflexivity.
have hDifference:W `\` C=L1 @` Z.
  apply/seteqP; split.
  - move=>x [[hx|hx] hn]; last exact hx.
    have [s hs hS]:=hx; exfalso; apply:hn; exists s; first exact:hV s hs; exact hS.
  - move=>x hx; split; first by right.
    move=>[s hs hS]; have [t ht hT]:=hx.
    exact:(hApart s t (eq_trans hS (esym hT))).
have hMass:=hC W; rewrite hIntersection hDifference in hMass.
have hMass0:=@parallel_coordinate_sheet_mass R 0%R V.
rewrite scale0r in hMass0.
change (H (L0 @` V)=lebesgue_scalar_measure V) in hMass0.
have hMass1:=@parallel_coordinate_sheet_mass R 1%R Z.
rewrite scale1r in hMass1.
change (H (L1 @` Z)=lebesgue_scalar_measure Z) in hMass1.
by rewrite hMass hMass0 hMass1.
Qed.
