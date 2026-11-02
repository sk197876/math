(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPreimages PartialAbsolutePartsGraph PartialExtendedOrderLoci MeasurableFunctionUP
  MeasurableRealEmbedding MeasurableGraphEquivalence BorelFunctionBasic TopologicalBorel
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP
  MeasureDerivationContext BoundedSupportContinuous CoveringFamilyUP
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureCharacteristicIntegral
  MeasureIntegralUP MeasureAbsoluteSummability SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_support_continuous_summable]: supporting
    summability of the lattice L in Federer 2.9.10, p. 157.
    Borel regularity makes continuous tests measurable. The bounded
    closed support has finite measure in the original M; a scalar
    multiple of its characteristic function dominates the absolute
    value. This does not require compact supports or local compactness. *)
Theorem bounded_support_continuous_summable (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  is_derivation_measure phi ->
  @bounded_support_continuous_functions R X `<=` summable_real_functions phi.
Proof.
move=> hphi f hf.
have hm := derivation_measure_law hphi.
have hr := derivation_measure_borel_regular hphi.
have hfm : is_measure_measurable_function phi (real_total_integrand f).
  have ht : is_measure_measurable_function phi (partial_function_total (f : X -> real_line_metric R)).
    constructor.
    - rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
    - move=> U hU; rewrite partial_function_total_preimage.
      exact (@borel_regular_borel_measurable R X phi hm hr _ (@continuous_borel_function X
        (real_line_metric R) f hf.1 U hU)).
  have hi := @measurable_total_real_embedding R X phi hm f ht.
  apply: (@measurable_function_graph_equivalent R X (extended_real_line R) phi _ _ _ hi)=> x z.
  by rewrite real_total_integrand_graph.
pose S := closure [set x | f x!=0%R].
have hSb := @bounded_support_continuous_support R X f hf.
have hSm := @borel_regular_borel_measurable R X phi hm hr S (@closed_borel_set X S (@closed_closure X _)).
have hSfin : phi S \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm S)); exact: derivation_measure_bounded_finite hphi S hSb.
pose s := @CharacteristicFunction.value R X S.
have hs := @CharacteristicFunction.laws R X S.
have hsi := @measure_characteristic_integral R X phi hm S s hs hSm.
have hss : summable_real_functions phi s.
  exists (fine (phi S)); by rewrite fineK.
have [M hM] := hf.2.1.
pose H x := (M*s x)%R.
have hHs := @summable_real_scale R X phi hm s M hss.
have hdom x : (`|f x|<=H x)%R.
  case: (pselect (S x))=> hx.
  - by rewrite /H /s (characteristic_on_set hs hx) mulr1; exact: hM.
  - have hf0 : f x=0%R.
      apply: contrapT=> hn; apply: hx.
      apply: (@subset_closure X [set z | f z!=0%R] x).
      by apply/negP=> /eqP.
    by rewrite /H /s (characteristic_off_set hs hx) mulr0 hf0 normr0.
apply: (@measure_dominated_summable R X phi hm (real_total_integrand f) (real_total_integrand H) hfm hHs _).1.
apply: (@measure_almost_everywhere_mono R X phi hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
exists (`|f x|%R)%:E,(H x)%:E; split.
- exists (f x)%:E; split; first by apply/real_total_integrand_graph.
  by rewrite abse_EFin.
- split; first by apply/real_total_integrand_graph.
  rewrite lee_fin; exact: hdom.
Qed.
