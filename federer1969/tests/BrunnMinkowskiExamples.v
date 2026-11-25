(** Federer (1969), 3.2.41, printed pp. 277--278:
    actual positive-volume boxes, genuinely nonmeasurable
    positive-volume sources, and the excluded zero-dimensional
    unit atom test the full theorem and its necessary scope. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanOpenCoordinateBoxUP
  EuclideanOpenCoordinateBoxMeasure EuclideanOpenCoordinateBoxSum VectorSetSum
  BrunnMinkowski EuclideanVolumeRootSum ExtendedPositivePower RealPower PointMassMeasure
  BernsteinNonmeasurableSubset EuclideanMetricCompleteness EuclideanMetricSeparability
  ApproximateDifferentialAffine FiniteOpenBoxUnionBounds MeasureUP MeasureBasic
  MeasureAlmostBasic MeasureFiniteClosure BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [brunn_minkowski_positive_interval_example]:
    Federer 3.2.41, p. 277, tested on the original open
    unit interval in R^1. Its actual sum has volume two;
    the whole numbered theorem attains its positive-volume
    bound, without any independently assumed sum volume. *)
Example brunn_minkowski_positive_interval_example (R:realType):
  let X:=inner_metric_space (@euclidean_inner_productP R 1) in
  let A:set X:=[set x|forall i,0<x i<1]%R in
  @euclidean_lebesgue_measure R 1 A= 1%E /\
    @euclidean_lebesgue_measure R 1 (vector_set_sum A A)=(2:R)%:E /\
    euclidean_volume_root_sum_bound A A.
Proof.
move=> X A.
pose a:R_n R 1:=0.
pose b:R_n R 1:=[ffun _=>(1:R)].
have hBox:is_euclidean_open_coordinate_box a b A.
  split; first by move=> i; rewrite /a /b !ffunE ltr01.
  move=>x; split=> hx i; have hi:=hx i.
  - rewrite /a /b !ffunE; exact hi.
  - by move:hi; rewrite /a /b !ffunE.
have hNe:=open_coordinate_box_nonempty hBox.
have hA:@euclidean_lebesgue_measure R 1 A= 1%E:=euclidean_unit_cube R 1.
have hSum:=open_coordinate_box_sum hBox hBox.
have hVolume:=open_coordinate_box_volume hSum.
have hSumMass:@euclidean_lebesgue_measure R 1 (vector_set_sum A A)=(2:R)%:E.
  rewrite hVolume big_ord1 /a /b !ffunE; congr (_%:E); lra.
have hFull:=@federer_3_2_41 R 1 A A (erefl true) hNe hNe.
split; first exact hA.
split; first exact hSumMass.
exact hFull.
Qed.

(** Source for [brunn_minkowski_nonmeasurable_example]:
    the arbitrary-source scope of Federer 3.2.41, pp. 277--278,
    tested on an actual nonmeasurable positive finite-volume
    subset of the unit interval. Existence follows from
    already proved 2.2.4, p. 62. Both factors in the actual
    sum are this original source; no measurable replacement
    is inserted into the conclusion. *)
Example brunn_minkowski_nonmeasurable_example (R:realType):
  exists W:set (inner_metric_space (@euclidean_inner_productP R 1)),
    ~measure_measurable (@euclidean_lebesgue_measure R 1) W /\
    (0<@euclidean_lebesgue_measure R 1 W < +oo)%E /\
    euclidean_volume_root_sum_bound W W.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose mu:=@euclidean_lebesgue_measure R 1.
pose A:set X:=[set x|forall i,0<x i<1]%R.
have hm:=euclidean_lebesgue_is_measure R 1.
have hMass:mu A= 1%E:=euclidean_unit_cube R 1.
have hPositive:(0<mu A)%E by rewrite hMass lte_fin ltr01.
have hFinite:(mu A < +oo)%E by rewrite hMass ltry.
have [W [hWA hNot]]:=@borel_regular_nonmeasurable_subset R X mu hm
  (euclidean_lebesgue_borel_regular R 1) A (@euclidean_metric_complete R 1)
  (@euclidean_metric_separable R 1) hPositive hFinite
  (fun x _=>@positive_euclidean_singleton_null R 0 x).
have hWPositive:(0<mu W)%E.
  rewrite lt_neqAle (measure_nonnegative hm W) andbT; apply/negP=>/eqP hZero.
  apply:hNot; exact:(@measure_null_measurable R X mu hm W (esym hZero)).
have hWFinite:(mu W < +oo)%E:=le_lt_trans (@measure_mono R X mu hm _ _ hWA) hFinite.
have hNe:=positive_measure_set_nonempty hm hWPositive.
have hFull:=@federer_3_2_41 R 1 W W (erefl true) hNe hNe.
exists W; split; first exact hNot.
split; first by apply/andP.
exact hFull.
Qed.

(** Source for [brunn_minkowski_zero_dimension_exclusion_example]:
    supporting positive-dimension qualification of Federer
    3.2.41, p. 277. Under the project's explicit empty-product
    extension the actual R^0 atom and its sum both have volume
    one. Substituting the totalized reciprocal zero would assert
    two<=one, so the numbered theorem must retain positive n. *)
Example brunn_minkowski_zero_dimension_exclusion_example (R:realType):
  let X:=inner_metric_space (@euclidean_inner_productP R 0) in
  let A:set X:=setT in
  @euclidean_lebesgue_measure R 0 A= 1%E /\
    @euclidean_lebesgue_measure R 0 (vector_set_sum A A)= 1%E /\
    ~euclidean_volume_root_sum_bound A A.
Proof.
move=> X A.
have hSum:vector_set_sum A A=A.
  apply/seteqP; split=>z _; first exact Logic.I.
  have hz:z=z+(0:X) by rewrite addr0.
  rewrite hz; exact:vector_set_sum_contains Logic.I Logic.I.
have hMass:@euclidean_lebesgue_measure R 0 A= 1%E.
  rewrite /euclidean_lebesgue_measure /A; exact:point_mass_in.
split; first exact hMass.
split; first by rewrite hSum.
rewrite /euclidean_volume_root_sum_bound hSum hMass /extended_positive_power
  !real_power_one_base -EFinD lee_fin.
move=>h.
have hStrict:(1:R)<1+1 by rewrite ltrDl ltr01.
have hBad:=lt_le_trans hStrict h.
by rewrite ltxx in hBad.
Qed.
