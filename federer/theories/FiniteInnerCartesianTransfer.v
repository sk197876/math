(** Federer (1969), 3.2.47(1),(2), p. 283: genuine
    product rectifiability and product nullity in the actual
    finite inner-product ambient spaces. Independent isometric
    coordinate laws discharge the Euclidean product hypotheses;
    arbitrary original subsets and all natural degrees remain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric ProductInner FiniteInnerChartUP
  FiniteInnerChartCompact FiniteInnerCartesianGeometry FiniteInnerChartHausdorff
  EuclideanCartesianMap EuclideanCartesianBorel EuclideanCartesianSwap
  GenuineRectifiableCartesianProduct RectifiableProductNullFactor
  LipschitzUP LipschitzBasic LipschitzRectifiableImages RectifiableSetUP
  NormMetricScaleContinuity HausdorffMeasure HausdorffRestrictedLipschitz
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ProductTransfer.
Variable R:realType.
Variables V W:lmodType R.
Variables (B:V->V->R) (C:W->W->R).
Variables (hB:is_inner_product B) (hC:is_inner_product C).
Variables n v:nat.
Variables (e:Hom (R_n R n) V) (p:Hom V (R_n R n)).
Variables (f:Hom (R_n R v) W) (q:Hom W (R_n R v)).
Hypotheses (hV:is_finite_inner_chart B e p) (hW:is_finite_inner_chart C f q).
Local Notation X:=(inner_metric_space hB).
Local Notation Y:=(inner_metric_space hC).
Local Notation P:=(inner_metric_space (product_inner_productP hB hC)).
Local Notation Q:=(inner_metric_space (@euclidean_inner_productP R (n+v))).

(** Source for [finite_inner_cartesian_rectifiable]: the genuine
    product assertion used in 3.2.47(1), p. 283,
    proved in the actual Cartesian metric, with no measurability,
    finite-mass or positive-degree premise. *)
Theorem finite_inner_cartesian_rectifiable r mu (E:set V) (Z:set W):
  @is_m_rectifiable R X r E ->@is_m_rectifiable R Y mu Z ->
  @is_m_rectifiable R P (r+mu)%N [set z:V*W|E z.1 /\Z z.2].
Proof.
move=>hE hZ.
have hEcoord:=rectifiable_lipschitz_image
  (@finite_inner_chart_inverse_lipschitz R V B hB n e p E hV) hE.
have hZcoord:=rectifiable_lipschitz_image
  (@finite_inner_chart_inverse_lipschitz R W C hC v f q Z hW) hZ.
have hProduct:=genuine_rectifiable_cartesian_product hEcoord hZcoord.
have hMap:=@finite_inner_cartesian_parametrization_lipschitz R V W B C hB hC n v e p f q hV hW.
have [L [hL hBound]]:=hMap.
have hRestricted:@is_metric_lipschitz R Q P
    (euclidean_cartesian_set (p @` E) (q @` Z)) (finite_inner_cartesian_parametrization e f).
  exists L; split; first exact hL.
  exact:metric_lipschitz_bound_restrict (fun x _=>I) hBound.
have hResult:=rectifiable_lipschitz_image hRestricted hProduct.
by rewrite (@finite_inner_cartesian_parametrization_image R V W B C n v e p f q E Z hV hW) in hResult.
Qed.

(** Source for [finite_inner_cartesian_null]: the null-product
    step in 3.2.47(2), p. 283, by 2.10.45,
    pp. 199–200. The second factor is genuinely rectifiable;
    the first need only have zero actual Hausdorff outer measure. *)
Theorem finite_inner_cartesian_null r mu (E:set V) (Z:set W):
  @hausdorff_measure R X r E=0%E ->@is_m_rectifiable R Y mu Z ->
  @hausdorff_measure R P (r+mu)%N [set z:V*W|E z.1 /\Z z.2]=0%E.
Proof.
move=>hE hZ.
have hEcoord:=@finite_inner_chart_inverse_hausdorff R V B hB n e p hV r E.
rewrite hE in hEcoord.
have hZcoord:=rectifiable_lipschitz_image
  (@finite_inner_chart_inverse_lipschitz R W C hC v f q Z hW) hZ.
have hReverse:=rectifiable_product_null_factor hZcoord hEcoord.
rewrite (addnC mu r) in hReverse.
have hZero:@hausdorff_measure R Q (r+mu)%N (euclidean_cartesian_set (p @` E) (q @` Z))=0%E.
  rewrite (@euclidean_cartesian_swap_hausdorff R n v (r+mu)%N (p @` E) (q @` Z)).
  exact hReverse.
have [L [_ hBound]]:=@finite_inner_cartesian_parametrization_lipschitz R V W B C hB hC n v e p f q hV hW.
have hEstimate:=@hausdorff_lipschitz_on_bound R Q P setT
  (finite_inner_cartesian_parametrization e f) L (r+mu)%N
  (euclidean_cartesian_set (p @` E) (q @` Z)) hBound (fun x _=>I).
rewrite hZero mule0
  (@finite_inner_cartesian_parametrization_image R V W B C n v e p f q E Z hV hW) in hEstimate.
apply/eqP; by rewrite eq_le hEstimate (measure_nonnegative (@hausdorff_measure_is_measure R P (r+mu))).
Qed.

(** Source for [finite_inner_cartesian_compact]: actual compact
    base core times the whole compact isotropy fibre, supporting
    the finite local Lipschitz argument in 3.2.47, p. 283. *)
Theorem finite_inner_cartesian_compact (E:set V) (Z:set W):
  @compact X E ->@compact Y Z ->@compact P [set z:V*W|E z.1 /\Z z.2].
Proof.
move=>hE hZ.
have hEcoord:=@finite_inner_chart_compact R V B hB n e p E hV hE.
have hZcoord:=@finite_inner_chart_compact R W C hC v f q Z hW hZ.
have hProduct:=euclidean_cartesian_compact hEcoord hZcoord.
have [L [_ hBound]]:=@finite_inner_cartesian_parametrization_lipschitz R V W B C hB hC n v e p f q hV hW.
have hContinuous:continuous (fun z:Q=>(finite_inner_cartesian_parametrization e f z:P)).
  exact (metric_fixed_lipschitz_continuous hBound.1 (fun x y=>hBound.2 x y I I)).
have hImage:=continuous_compact (continuous_subspaceT hContinuous) hProduct.
by rewrite (@finite_inner_cartesian_parametrization_image R V W B C n v e p f q E Z hV hW) in hImage.
Qed.
End ProductTransfer.
