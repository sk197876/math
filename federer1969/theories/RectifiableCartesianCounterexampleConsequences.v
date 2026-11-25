(** Federer (1969), 3.2.24, p. 260: both conclusions of
    3.2.23 fail for the null Cantor-power factors. This file
    derives the failures only from independent counterexample laws,
    and proves that the first factor cannot be genuinely rectifiable. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap RectifiableSetUP HausdorffMeasure
  RectifiableCartesianCounterexampleUP RectifiableCartesianProduct
  MeasureUP MeasureBasic MeasureSplit MeasureRestriction MeasurePushforward
  ProductMeasure ProductRectangleValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_cartesian_counterexample_not_rectifiable]:
    failure of the rectifiability conclusion of 3.2.23 under
    the weakened hypothesis in 3.2.24, p. 260. The product
    has infinite mass, so it fails the finite-mass convention
    in 3.2.14(4), p. 252. *)
Lemma rectifiable_cartesian_counterexample_not_rectifiable (R:realType)
    (W Z:set (R_n R 4)):
  is_rectifiable_cartesian_counterexample W Z ->
  ~is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (4+4))) (2+2))
    (2+2) (euclidean_cartesian_set W Z).
Proof.
move=>hExample [_ hFinite].
by move:hFinite; rewrite (cartesian_counterexample_product_infinite hExample) ltxx.
Qed.

(** Source for [rectifiable_cartesian_counterexample_not_measure_identity]:
    failure of the displayed restricted-measure equality of 3.2.23
    for the example of 3.2.24, p. 260. Evaluating a
    purported whole-measure equality gives infinity=zero. *)
Lemma rectifiable_cartesian_counterexample_not_measure_identity (R:realType)
    (W Z:set (R_n R 4)):
  is_rectifiable_cartesian_counterexample W Z ->
  measure_pushforward (@euclidean_block_split R 4 4)
    (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R (4+4))) (2+2))
      (euclidean_cartesian_set W Z)) <>
  product_measure
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R 4)) 2) W)
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R 4)) 2) Z).
Proof.
move=>hExample hIdentity.
have hMass:=rectifiable_cartesian_total_mass_from_identity hIdentity.
by move:hMass; rewrite (cartesian_counterexample_product_infinite hExample)
  (cartesian_counterexample_factor_null hExample).1
  (cartesian_counterexample_factor_null hExample).2 mul0e.
Qed.

(** Source for [rectifiable_cartesian_counterexample_not_genuine_first]:
    the first factor in 3.2.24, p. 260, cannot satisfy
    the genuinely rectifiable hypothesis of 3.2.23. This
    follows from the whole theorem, not from an unproved
    assertion about the shape of the Cantor set. *)
Lemma rectifiable_cartesian_counterexample_not_genuine_first (R:realType)
    (W Z:set (R_n R 4)):
  is_rectifiable_cartesian_counterexample W Z ->
  ~(@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R 4)) 2 W).
Proof.
move=>hExample hActual.
have hWhole:=federer_3_2_23 hActual (cartesian_counterexample_borel hExample).1
  (cartesian_counterexample_factor_rectifiability hExample).2
  (cartesian_counterexample_borel hExample).2.
exact:(rectifiable_cartesian_counterexample_not_rectifiable hExample
  (rectifiable_cartesian_rectifiability_law hWhole)).
Qed.

(** Source for [rectifiable_cartesian_counterexample_reference_zero]:
    the product of the restricted factor measures in 3.2.24,
    p. 260, is zero on every test subset. Its whole-space
    rectangle has zero mass; monotonicity proves the result
    without measurability of the test set. *)
Lemma rectifiable_cartesian_counterexample_reference_zero (R:realType)
    (W Z:set (R_n R 4)):
  is_rectifiable_cartesian_counterexample W Z ->forall S,
  product_measure
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R 4)) 2) W)
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R 4)) 2) Z) S=0.
Proof.
move=>hExample S.
pose X:=inner_metric_space (@euclidean_inner_productP R 4).
pose hA:=measure_restrict_is_measure (@hausdorff_measure_is_measure R X 2) W.
pose hB:=measure_restrict_is_measure (@hausdorff_measure_is_measure R X 2) Z.
pose nu:=product_measure hA hB.
have hNu:=product_measure_is_measure hA hB.
have hWhole:(@setT X) `*` (@setT X)=setT.
  by apply/seteqP; split=>p; [move=>_|move=>_;split].
have hMass:=product_measure_rectangle_value hA hB
  (measure_measurable_whole hA) (measure_measurable_whole hB).
rewrite hWhole /measure_restrict !setIT
  (cartesian_counterexample_factor_null hExample).1
  (cartesian_counterexample_factor_null hExample).2 mul0e in hMass.
apply/eqP; rewrite eq_le (measure_nonnegative hNu S) andbT.
have hBound:=measure_mono hNu (subsetT S).
by rewrite hMass in hBound.
Qed.
