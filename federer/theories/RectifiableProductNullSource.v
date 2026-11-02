(** Federer (1969), 3.2.23, p. 260: a null subset of
    the genuinely rectifiable first factor contributes no sum-dimensional
    product mass. The regular target pieces use the reversed 2.10.45
    argument; the omitted target part still uses actual first-factor
    rectifiability. This distinction is essential for 3.2.24. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanCartesianSwap RectifiableSetUP RectifiableProductNullFactor
  HausdorffMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_product_null_source]: supporting
    removal of source-null chart remainders in Federer 3.2.23,
    p. 260. Retain actual m-rectifiability of the first factor;
    replacing it by mere (H^m,m) rectifiability would make this
    assertion false, as explained by 3.2.24 on the same page. *)
Theorem rectifiable_product_null_source (R:realType) m mu n v
    (W:set (R_n R n)) (Z:set (R_n R v)):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W=0 ->
  is_countably_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+v)))
    (m+mu) (euclidean_cartesian_set W Z)=0.
Proof.
move=>hW hZero [_ [S [[C [hCount [hC hUnion]]] hNull]]].
pose P:=inner_metric_space (@euclidean_inner_productP R (n+v)).
pose rho:=@hausdorff_measure R P (m+mu).
have hr:=@hausdorff_measure_is_measure R P (m+mu).
have hPiece A:C A ->rho (euclidean_cartesian_set W A)=0.
  move=>hA.
  have h:=rectifiable_product_null_factor (hC A hA) hZero.
  rewrite (addnC mu m) in h.
  have hSwap:=@euclidean_cartesian_swap_hausdorff R n v (m+mu) W A.
  exact:(eq_trans hSwap h).
have hGood:rho (\bigcup_(A in C) euclidean_cartesian_set W A)=0.
  exact:(measure_null_countable_union hr hCount hPiece).
have hBad:rho (euclidean_cartesian_set W (Z `\` S))=0.
  exact:(rectifiable_product_null_factor hW hNull).
apply:(measure_null_subset hr _ (measure_null_union hr hGood hBad))=>p [hpW hpZ].
have [hSp|hSp]:=pselect (S (euclidean_block_split p).2).
- left; rewrite hUnion in hSp; have [A hA hpA]:=hSp.
  exists A; first exact hA; by split.
- right; split; first exact hpW; by split.
Qed.
