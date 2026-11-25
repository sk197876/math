(** Federer (1969), 2.7.16, p. 134, uses that L^n is a Haar measure, that
    is, the K(R^n) regular measure associated with a Haar integral (2.7.2,
    p. 122). The integral is u |-> int u dL^n on K(R^n) of 2.5.13, p. 106;
    it is defined because every member of K(R^n) is L^n summable. This
    module proves the general fact behind this: if the Borel sets of a
    topological space X are phi measurable and the compact sets have finite
    phi measure, then every u in K(X) is phi summable, since u is Borel
    measurable and |u| <= M chi_{spt u} (2.4.4, p. 83, and 2.5.1, p. 91). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology TopologicalBorel BorelFunctionBasic MeasureIntegralGraphEquivalence
  CompactSupportFunctionUP CompactSupportUniformBound CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureAbsoluteSummability
  MeasureCharacteristicIntegral PartialFunctionBasic PartialFunctionPreimages PartialExtendedOrderLoci
  PartialAbsolutePartsGraph MeasurableFunctionUP MeasurableRealEmbedding MeasurableGraphEquivalence
  SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactSummability.
Variable R : realType.
Variable X : topologicalType.
Variable phi : set X -> \bar R.
Hypothesis hm : is_measure phi.
Hypothesis hB : forall A, borel_set A -> measure_measurable phi A.
Hypothesis hK : forall K, compact K -> (phi K < +oo)%E.

(** Source for [continuous_real_integrand_measurable]: supporting
    lemma for Federer 2.7.16, p. 134: a continuous real function u on X
    is phi measurable when the Borel sets are phi measurable (2.3.2,
    p. 73, for Borel functions). *)
Lemma continuous_real_integrand_measurable (u : X -> R) :
  continuous (u : X -> real_line_metric R) -> is_measure_measurable_function phi (real_total_integrand u).
Proof.
move=> hu.
have ht : is_measure_measurable_function phi (partial_function_total (u : X -> real_line_metric R)).
  constructor.
  - rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
  - move=> U hU; rewrite partial_function_total_preimage; apply: hB.
    exact (@continuous_borel_function X (real_line_metric R) u hu U hU).
have hi := measurable_total_real_embedding hm ht.
apply: (@measurable_function_graph_equivalent R X (extended_real_line R) phi _ _ _ hi)=> x z.
by rewrite real_total_integrand_graph.
Qed.

(** Source for [compactly_supported_summable]: supporting lemma for
    Federer 2.7.16, p. 134, with 2.5.13, p. 106: every member of K(X) is
    phi summable, so that u |-> int u dphi is defined on K(X). *)
Theorem compactly_supported_summable (u : X -> R) :
  compactly_supported_continuous_functions u -> summable_real_functions phi u.
Proof.
move=> hu.
pose S := real_function_support u.
have hSb : borel_set S := closed_borel_set (@real_function_support_closed R X u).
pose s := @CharacteristicFunction.value R X S.
have hs : is_characteristic_function S s := @CharacteristicFunction.laws R X S.
have hsi := @measure_characteristic_integral R X phi hm S s hs (hB hSb).
have hfin : phi S \is a fin_num.
  by rewrite ge0_fin_numE ?(measure_nonnegative hm) //; exact: hK hu.2.
have hss : summable_real_functions phi s.
  by exists (fine (phi S)); rewrite fineK //; exact: hsi.
have [M [hM hbound]] := compact_support_uniform_bound hu.
pose H x := M * s x.
have hHs : summable_real_functions phi H := summable_real_scale hm M hss.
have hdom x : `|u x| <= H x.
  case: (pselect (S x))=> hx.
  - by rewrite /H (characteristic_on_set hs hx) mulr1; exact: hbound.
  - by rewrite (real_function_zero_off_support hx) normr0 /H (characteristic_off_set hs hx) mulr0.
refine (proj1 (@measure_dominated_summable R X phi hm (real_total_integrand u) (real_total_integrand H)
  (continuous_real_integrand_measurable hu.1) hHs _)).
apply: (@measure_almost_everywhere_mono R X phi hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
exists (`|u x|)%:E, (H x)%:E; split.
- exists (u x)%:E; split; first by apply/real_total_integrand_graph.
  by rewrite abse_EFin.
- split; first by apply/real_total_integrand_graph.
  rewrite lee_fin; exact: hdom.
Qed.

End CompactSummability.
