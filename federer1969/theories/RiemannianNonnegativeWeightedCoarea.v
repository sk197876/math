(** Federer (1969), 3.2.12, p. 250, extended
    by 3.2.46, p. 282: characteristic expansions
    give weighted coarea for actual Riemannian metrics.
    Original fibre measurability and every inner integral
    are proved from the original hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  RiemannianPathLipschitz RiemannianJacobianDensityMeasure RiemannianCoareaFormula
  RiemannianCoareaFibreIntegral RiemannianCoareaFibreMeasurable
  CoareaCharacteristicExpansion MappingMultiplicity PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureTotalPositiveScale TotalNonnegativeSeriesIntegral
  WeightedCharacteristicExpansionUP WeightedCharacteristicExpansion PositiveVanishingWeightsSealed
  WeightedCharacteristicIntegral ParameterizedIntegralLaws NonnegativeSum ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_nonnegative_weighted_coarea]:
    the characteristic-expansion proof of 3.2.12,
    p. 250, for the actual metrics of
    3.2.46, p. 282. Source-measurable
    nonnegative extended weights, infinite values and
    whole original fibres are included. No summability,
    fibre-integrability or selected derivative-field premise
    is added. The signed reduction is a later step. *)
Theorem riemannian_nonnegative_weighted_coarea (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpSource : (0<=m%:R :> R)%R) (hpTarget : (0<=n%:R :> R)%R)
    (hpFibre : (0<=(m-n)%:R :> R)%R)
    (u : riemannian_metric_space hg -> extended_real_line R) :
  (n<m)%N -> is_riemannian_path_lipschitz f ->
  is_measure_measurable_function (riemannian_hausdorff_measure hg m%:R hpSource)
    (partial_function_total u) -> (forall x, 0<=u x) ->
  exists a, is_measure_integral (riemannian_jacobian_measure f hpSource n)
      (partial_function_total u) a /\
    is_measure_integral (riemannian_hausdorff_measure hh n%:R hpTarget)
      (riemannian_coarea_fibre_integral f hpFibre (partial_function_total u)) a.
Proof.
move=> hnm hLip hMeas hPositive.
pose X := [the choiceType of riemannian_metric_space hg].
pose Y := [the choiceType of riemannian_metric_space hh].
pose mu := riemannian_hausdorff_measure hg m%:R hpSource.
pose nu := riemannian_jacobian_measure f hpSource n.
pose alpha := riemannian_hausdorff_measure hh n%:R hpTarget.
pose sigma := riemannian_hausdorff_measure hg (m-n)%:R hpFibre.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hpSource.
have hNu := @riemannian_jacobian_measure_is_measure R m n A B g h hg hh f hpSource n hLip.
have hAlpha := @riemannian_hausdorff_is_measure R n B h hh n%:R hpTarget.
have hSigma := @riemannian_hausdorff_is_measure R m A g hg (m-n)%:R hpFibre.
pose r := @PositiveVanishingWeights.value R.
have hWeights := @PositiveVanishingWeights.laws R.
have hr := expansion_weights_positive hWeights.
have [E [s [hExpansion hExtra]]] := @measurable_weighted_characteristic_expansion R X mu
  hMu u r hMeas hPositive hWeights.
have hNuExpansion : is_weighted_characteristic_expansion nu u r E s.
  constructor.
  - move=> j; exact:(@riemannian_jacobian_measure_measurable R m n A B g h hg hh f hpSource n
      (E j) hLip (expansion_sets_measurable hExpansion j)).
  - exact:expansion_characteristic_laws hExpansion.
  - exact:expansion_pointwise_sum hExpansion.
pose theta j y : extended_real_line R := sigma (mapping_fibre f (E j) y).
have hTheta j : is_measure_integral alpha (partial_function_total (theta j)) (nu (E j)).
  exact:(@riemannian_coarea_formula R m n A B g h hg hh f hpSource hpTarget hpFibre
    (E j) hnm hLip (expansion_sets_measurable hExpansion j)).
have hScaled j : is_measure_integral alpha
    (partial_function_total (fun y=>(r j)%:E*theta j y)) ((r j)%:E*nu (E j)).
  exact (@measure_total_positive_scale_integral R Y alpha hAlpha (theta j) (r j)
    (nu (E j)) (hr j) (hTheta j)).
have hNonnegative j y : 0<=(r j)%:E*theta j y.
  apply:mule_ge0; first by rewrite lee_fin; exact:ltW (hr j).
  exact:(measure_nonnegative hSigma _).
have hOuter := @total_nonnegative_series_integral R Y alpha hAlpha
  (fun j y=>(r j)%:E*theta j y) (fun j=>(r j)%:E*nu (E j)) hNonnegative hScaled.
have hInner := @coarea_characteristic_expansion_inner_integral R X Y f mu sigma alpha hSigma hAlpha
  u r E s hr hExpansion (fun j=>
    @riemannian_coarea_source_fibres_measurable R m n A B g h hg hh f
      hpSource hpTarget hpFibre (E j) (ltnW hnm) hLip (expansion_sets_measurable hExpansion j)).
exists (nonnegative_sum setT (fun j=>(r j)%:E*nu (E j))); split.
- exact (weighted_characteristic_expansion_integral hNu hr hNuExpansion).
- exact (parameterized_integral_total_outer_transfer hAlpha hInner hOuter).
Qed.
