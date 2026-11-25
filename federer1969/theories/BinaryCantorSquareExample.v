(** Federer (1969), 3.3.20, pp. 306–309: the actual original binary Cantor-square example. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanCantorProduct
  CantorSquareCompactMass BinaryCantorSetUP BinaryCantorSetSealed BinaryCantorSetProperties PowerCantorSquareRealMassBounds
  PowerCantorPairUP PowerCantorSquarePure CriticalCantorSquareSharpLength CriticalCantorSquareGross
  SupercriticalCantorSquareInfinity RealHausdorffMeasure RealHausdorffNormalisation RealPower
  HausdorffMeasure ProjectionMeasure IntegralGeometricMeasure RectifiableSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_3_20]: principal assertions of the complete
    original example, 3.3.20, pp. 306–309. The opaque original factor
    is used only through its independent laws. Its real-degree
    normalization is the actual Euler Gamma coefficient. All original
    nonmeasurable subsets remain in the finite-I-infinity assertion.
    The corrected projection and finite-stage supporting assertions are
    proved in the accompanying modules; no desired conclusion is an
    object-defining assumption. *)
Theorem federer_3_3_20 (R:realType) (m:R) (hm:0<m) (hm1:m<1)
    (hDegree:0<=2 * m):
  1/2<=m ->
  let A:=@BinaryPowerCantor.value R m hm hm1 in
  let E:=euclidean_cantor_product A A in
  let X:=inner_metric_space (@euclidean_inner_productP R 2) in
  let b:=real_hausdorff_normalisation hDegree in
  compact E /\
  (b%:E<=@real_hausdorff_measure R X (2 * m) hDegree E)%E /\
  (@real_hausdorff_measure R X (2 * m) hDegree E<=(b * real_power 2 m)%R%:E)%E /\
  is_purely_measure_m_unrectifiable (@hausdorff_measure R X 1) 1 E /\
  is_purely_measure_m_unrectifiable (@real_hausdorff_measure R X (2 * m) hDegree) 1 E /\
  (forall F,F `<=` E ->(@integral_geometric_measure R 2 1 (erefl true) +oo F< +oo)%E ->
    @integral_geometric_measure R 2 1 (erefl true) +oo F=0%E) /\
  (1/2<m ->@integral_geometric_measure R 2 1 (erefl true) +oo E=+oo%E) /\
  (m= 1/2 ->@hausdorff_measure R X 1 E=(Num.sqrt (2:R))%:E /\
    @gross_measure R 2 1 E=(3/Num.sqrt (5:R))%:E).
Proof.
move=>hHalf A E X b.
have hOriginal:=@BinaryPowerCantor.laws R m hm hm1.
change (is_binary_power_cantor_set m A) in hOriginal.
have [f hPair]:=hOriginal.
have [hCompact _]:=binary_power_cantor_original_properties hm hm1 hOriginal.
have [hLower hUpper]:=@power_cantor_square_real_mass_bounds R 1 m hDegree (fun _:nat=>2%N) A f
  ltr01 hm hm1 hPair.
have hPure:=@power_cantor_original_square_pure_length R 1 m (fun _:nat=>2%N) A f
  ltr01 hm hm1 hPair.
have [hPureReal hNoFinite]:=@power_cantor_original_square_pure_consequences R 1 m hDegree
  (fun _:nat=>2%N) A f ltr01 hHalf hm1 hPair.
split;first exact:(euclidean_cantor_product_compact hCompact hCompact).
split;first exact:hLower.
split;first exact:hUpper.
split;first exact:hPure.
split;first exact:hPureReal.
split;first exact:hNoFinite.
split.
- move=>hSuper.
  have hProof:(leqnSn 1)=(erefl true):=bool_irrelevance _ _.
  have h:=@supercritical_original_cantor_square_infinity R 1 m A f ltr01 hSuper hm1 hPair.
  by rewrite hProof in h.
- move=>hCritical.
  have hPairCritical:is_power_cantor_pair 1 (1/2:R) (fun _:nat=>2%N) A f by rewrite -hCritical.
  split.
  + exact:critical_original_cantor_square_sharp_length ltr01 hPairCritical.
  + exact:critical_original_cantor_square_gross ltr01 hPairCritical.
Qed.
