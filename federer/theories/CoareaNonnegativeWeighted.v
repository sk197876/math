(** Federer (1969), 3.2.12, p. 250: the
    nonnegative characteristic expansion proves weighted coarea
    before the signed reduction. Infinite integral values are allowed. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  CoareaJacobianMeasure EuclideanCoareaFormula CoareaFibreIntegral CoareaSourceFibreMeasurable
  CoareaCharacteristicExpansion HausdorffMeasure MappingMultiplicity LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension MeasureUP MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureTotalPositiveScale TotalNonnegativeSeriesIntegral
  WeightedCharacteristicExpansionUP WeightedCharacteristicExpansion PositiveVanishingWeightsSealed
  WeightedCharacteristicIntegral ParameterizedIntegralLaws NonnegativeSum ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_nonnegative_weighted_integral]:
    the 2.3.3 and 2.4.8 steps in Federer
    3.2.12, p. 250. Both the source
    density integral and the actual inner-fibre integral
    exist with the same value; fibre measurability and
    all inner integrability premises are proved from Lipschitzness. *)
Theorem coarea_nonnegative_weighted_integral (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (u:R_n R m->extended_real_line R):
  (n<m)%N ->is_metric_lipschitz setT f ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) (partial_function_total u) ->
  (forall x,0<=u x) ->exists a,
    is_measure_integral (euclidean_coarea_measure f) (partial_function_total u) a /\
    is_measure_integral (@euclidean_lebesgue_measure R n) (coarea_fibre_integral f (partial_function_total u)) a.
Proof.
move=>hnm hf hu hp.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R m.
pose nu:=euclidean_coarea_measure f.
pose alpha:=@euclidean_lebesgue_measure R n.
pose beta:=@hausdorff_measure R X (m-n).
pose ha:=euclidean_lebesgue_is_measure R n.
pose hb:=@hausdorff_measure_is_measure R X (m-n).
pose hn:=euclidean_coarea_measure_is_measure hf.
pose r:=@PositiveVanishingWeights.value R.
have hw:=@PositiveVanishingWeights.laws R.
have hr:=expansion_weights_positive hw.
have [E [s [hExp _]]]:=@measurable_weighted_characteristic_expansion R [the choiceType of X] mu
  (euclidean_lebesgue_is_measure R m) u r hu hp hw.
have hNuRep:is_weighted_characteristic_expansion nu u r E s.
  constructor.
  - move=>j; exact (euclidean_coarea_measure_measurable hf (expansion_sets_measurable hExp j)).
  - exact (expansion_characteristic_laws hExp).
  - exact (expansion_pointwise_sum hExp).
pose theta j y:extended_real_line R:=beta (mapping_fibre f (E j) y).
have hTheta j:is_measure_integral alpha (partial_function_total (theta j)) (nu (E j)).
  exact (euclidean_coarea_formula hnm hf (expansion_sets_measurable hExp j)).
have hScaled j:is_measure_integral alpha (partial_function_total (fun y=>(r j)%:E*theta j y))
    ((r j)%:E*nu (E j)).
  exact (measure_total_positive_scale_integral ha (hr j) (hTheta j)).
have hPositive j y:0<=(r j)%:E*theta j y.
  apply:mule_ge0; first by rewrite lee_fin; exact:ltW (hr j).
  exact (@measure_nonnegative R [the choiceType of X] beta hb (mapping_fibre f (E j) y)).
have hOuter:=@total_nonnegative_series_integral R [the choiceType of Y] alpha ha
  (fun j y=>(r j)%:E*theta j y) (fun j=>(r j)%:E*nu (E j)) hPositive hScaled.
have hInner:=coarea_characteristic_expansion_inner_integral hb ha hr hExp
  (fun j=>coarea_source_fibre_measurable_almost (ltnW hnm) hf (expansion_sets_measurable hExp j)).
exists (nonnegative_sum setT (fun j=>(r j)%:E*nu (E j))); split.
- exact (weighted_characteristic_expansion_integral hn hr hNuRep).
- exact (parameterized_integral_total_outer_transfer ha hInner hOuter).
Qed.
