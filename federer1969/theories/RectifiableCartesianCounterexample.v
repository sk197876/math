(** Federer (1969), 3.2.24, p. 260: genuine counterexample
    from 2.10.29. Take scalar exponent 1/4 and fourth powers;
    finite H^1 factor mass gives zero H^2 factor mass, whereas
    the Cartesian product has infinite H^4 mass. All measures
    are the existing naturally normalized Hausdorff measures. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Export RectifiableCartesianCounterexampleUP.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealMetricBackground RealPower HausdorffDiameterCost HausdorffMeasure HausdorffDimensionDrop
  MetricRealPowerMeasure NaturalRealPowerMeasureAgreement EuclideanSetPowers EuclideanSetPowerBorel
  EuclideanPairPowerShuffle EuclideanCartesianMap CantorPowerProductTheorem PowerCantorPair
  PowerCantorPairUP InterleavedCantorScalesUP RectifiableSetUP CountablyMeasureRectifiableOperations
  MeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_24]: the full existential
    counterexample of Federer 3.2.24, p. 260. The proof
    specializes the printed 2.10.29 construction to fourth
    powers and scalar exponent 1/4, so the factor nullity
    uses only natural-degree dimension drop from 1 to 2.
    The product degree is 4, strictly below 4(1+1/4)=5. *)
Theorem federer_3_2_24 (R:realType):
  exists W Z:set (R_n R 4),is_rectifiable_cartesian_counterexample W Z.
Proof.
pose s:R:=((4:R)^-1)%R.
have hc:(0<(1:R))%R:=ltr01.
have hs:(0<s)%R by rewrite /s invr_gt0 ltr0n.
have hs1:(s<1)%R by rewrite /s invf_lt1 ?ltr0n // ltr1n.
have hDegree:(4%:R*s=(1:R))%R by rewrite /s mulfV ?pnatr_eq0.
have hGap:(4<4%:R*(s+1))%R.
  rewrite mulrDr mulr1 hDegree; lra.
have [D [A [B [f [g [hD [hA [hB hPowers]]]]]]]]:=federer_2_10_29_positive_powers hc hs hs1.
pose W:=euclidean_set_power 4 A.
pose Z:=euclidean_set_power 4 B.
pose X:=inner_metric_space (@euclidean_inner_productP R 4).
pose T:=inner_metric_space (@euclidean_inner_productP R (4+4)).
have hWFinite:@hausdorff_measure R X 1 W< +oo.
  have hBound:=(hPowers 3%N (hausdorff_normalisation R 1) (@hausdorff_normalisation_positive R 1)).1.
  rewrite hDegree natural_real_power_measure_agreement in hBound.
  exact:(le_lt_trans hBound (ltry _)).
have hZFinite:@hausdorff_measure R X 1 Z< +oo.
  have hBound:=(hPowers 3%N (hausdorff_normalisation R 1) (@hausdorff_normalisation_positive R 1)).2.1.
  rewrite hDegree natural_real_power_measure_agreement in hBound.
  exact:(le_lt_trans hBound (ltry _)).
have hWNull:=@hausdorff_finite_mass_higher_degree_zero R X 1 2 W (erefl true) hWFinite.
have hZNull:=@hausdorff_finite_mass_higher_degree_zero R X 1 2 Z (erefl true) hZFinite.
have hInfinite:@hausdorff_measure R T 4 (euclidean_cartesian_set W Z)=+oo.
  have h:=(hPowers 3%N (hausdorff_normalisation R 4) (@hausdorff_normalisation_positive R 4)).2.2
    4%R (ler0n R 4) hGap.
  rewrite natural_real_power_measure_agreement in h; exact h.
have hCompactA:=(power_cantor_pair_properties hc hs hs1 hA).1.
have hCompactB:=(power_cantor_pair_properties hc hs hs1 hB).1.
have hWBorel:=euclidean_set_power_borel 4%N
  (closed_borel_set (compact_closed (@metric_hausdorff R [the metricType R of real_line_metric R]) hCompactA)).
have hZBorel:=euclidean_set_power_borel 4%N
  (closed_borel_set (compact_closed (@metric_hausdorff R [the metricType R of real_line_metric R]) hCompactB)).
have hRect U:@hausdorff_measure R X 2 U=0 ->
    is_measure_m_rectifiable (@hausdorff_measure R X 2) 2 U.
  move=>hNull; split.
  - exact:(@countably_measure_rectifiable_null R X (@hausdorff_measure R X 2) 2%N U
      (@hausdorff_measure_is_measure R X 2) hNull).
  - by rewrite hNull ltry.
exists W,Z; constructor; [by split|by split|split;exact:hRect|exact hInfinite].
Qed.
