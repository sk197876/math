(** Federer (1969), 3.2.3(2), pp. 243–244:
    the weighted area formula for nonnegative total functions,
    by characteristic expansions as prescribed in the proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  ExtendedRealOrderTopology PartialFunctionBasic MeasurableFunctionUP MeasureUP MeasureIntegralUP
  MeasureIntegralUniqueness MeasureSubsetIntegral JacobianDensityMeasure EuclideanAreaFormula
  HausdorffMeasure LipschitzUP MappingMultiplicity FibreNonnegativeSum WeightedFibreIntegral
  WeightedCharacteristicExpansionUP WeightedCharacteristicExpansion PositiveVanishingWeightsSealed
  WeightedCharacteristicIntegral NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_nonnegative_weighted_integral]: the
    characteristic-function and nonnegative-series argument of
    Federer 3.2.3(2), p. 243, using 2.3.3 and 2.4.8.
    Both integrals may be infinite. *)
Theorem area_nonnegative_weighted_integral (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (u:R_n R m->extended_real_line R):
  is_metric_lipschitz setT f ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) (partial_function_total u) ->
  (forall x, 0<=u x) ->
  exists a,is_measure_integral (euclidean_jacobian_measure f) (partial_function_total u) a /\
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (partial_function_total (fun y=>(fibre_nonnegative_sum f u y:extended_real_line R))) a.
Proof.
move=>hLip hu hp.
pose r:=@PositiveVanishingWeights.value R.
have hw:=@PositiveVanishingWeights.laws R.
have [E [s [hExp _]]]:=@measurable_weighted_characteristic_expansion R _ _
  (euclidean_lebesgue_is_measure R m) u r hu hp hw.
have hNu:=euclidean_jacobian_measure_is_measure hLip.
have hRep:is_weighted_characteristic_expansion (euclidean_jacobian_measure f) u r E s.
  constructor.
  - move=>k; exact (euclidean_jacobian_measure_measurable hLip (expansion_sets_measurable hExp k)).
  - exact (expansion_characteristic_laws hExp).
  - exact (expansion_pointwise_sum hExp).
have hMult k:is_measure_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (partial_function_total (fun y=>(@mapping_multiplicity R _ _ f (E k) y:extended_real_line R)))
    (euclidean_jacobian_measure f (E k)).
  have hEk:=expansion_sets_measurable hExp k.
  have [a [hJa hNa]]:=euclidean_area_formula hLip hEk.
  have hJnu:=euclidean_jacobian_measure_integral hLip hEk.
  have heq:=measure_integral_unique hJa hJnu.
  by rewrite heq in hNa.
exists (nonnegative_sum setT (fun k=>(r k)%:E*euclidean_jacobian_measure f (E k))); split.
- exact (weighted_characteristic_expansion_integral hNu (expansion_weights_positive hw) hRep).
- exact (@weighted_fibre_integral R _ _ f _ _ hNu (@hausdorff_measure_is_measure R _ m)
    u r E s (expansion_weights_positive hw) hRep hMult).
Qed.
