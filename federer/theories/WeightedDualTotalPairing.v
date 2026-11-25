(** Federer (1969), 4.1.7, p. 359:
    normalizing the actual exterior-image density
    transfers its pairing to the exact
    mass-weighted measure. This is the original
    change-of-density law 2.4.10, p. 85,
    applied to finite scalar evaluations. *)
From mathcomp Require Import boolp all_boot all_order all_algebra functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousDualUP WeakEvaluationTopologyUP
  OpenFamilyTopologyMathcomp VectorDaniellHypotheses AbstractUnitDualPairingMeasurable AbstractDualPartialPairing
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP PartialExtendedOrderLoci
  MeasurableFunctionUP MeasurableGraphEquivalence MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureDensityUP RealFiniteDensityIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_dual_total_pairing_integral]:
    the unit density under the original
    mass-weighted measure has the same scalar
    integral as the unnormalized original density,
    supporting Federer 4.1.7, p. 359.
    Only pointwise reconstruction and the earlier
    change-of-density theorem are used. *)
Theorem weighted_dual_total_pairing_integral (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hSep:is_separable_normed_space hNY) (D:lmodType R)
    (ed:Hom D (Hom Y R^o)) (DN:D->R) (hD:is_continuous_dual hNY ed DN)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun d y=>ed d y) O)
    (mu lambda:set X->\bar R) (hm:is_measure mu) (w:X->R) (delta u:X->D)
    (eta:X->real_norm_metric_space hNY):
  is_measure_density mu (real_total_integrand w) lambda->
  is_measure_measurable_function mu (real_total_integrand w)->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (real_total_integrand w))->
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(u x:open_family_topological_space hO.1)))->
  (forall x,DN (u x)<=1)->(forall x,w x*:u x=delta x)->
  is_measure_measurable_function mu (partial_function_total eta)->forall a,
  is_measure_integral lambda (abstract_dual_partial_pairing ed u (partial_function_total eta)) a<->
  is_measure_integral mu (real_total_integrand (fun x=>ed (delta x) (eta x))) a.
Proof.
move=>hDensity hW hPositive hU hUnit hReconstruct hEta a.
have hPair:=@abstract_unit_dual_pairing_measurable R X Y NY hNY hSep D ed DN hD O hO
  mu hm u (partial_function_total eta) hU hUnit hEta.
have hGraph:=@abstract_dual_partial_pairing_total_graph R X Y D ed u eta.
have hScalar:=measurable_function_graph_equivalent hGraph hPair.
have hIff:=@real_finite_density_integral_iff R X mu lambda hm w
  (fun x=>ed (u x) (eta x)) hDensity hW hPositive hScalar a.
have hValues:(fun x=>ed (u x) (eta x)*w x)=(fun x=>ed (delta x) (eta x)).
  apply:funext=>x.
  rewrite -(hReconstruct x) linearZ hom_scaleE /= mulrC;by [].
rewrite hValues in hIff.
split=>hIntegral.
- exact:(hIff.1 (measure_integral_graph_equivalent hGraph hIntegral)).
- apply:(@measure_integral_graph_equivalent R X lambda _ _ a _ (hIff.2 hIntegral))=>x z.
  exact:iff_sym (hGraph x z).
Qed.
