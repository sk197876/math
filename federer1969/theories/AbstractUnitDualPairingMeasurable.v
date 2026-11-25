(** Federer (1969), 4.1.7, p. 359:
    the weighted image pairing remains measurable
    before summability is asserted. This supporting
    adapter applies 2.5.12, pp. 103–105,
    to the original abstract continuous dual,
    with every original partial domain retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousDualUP WeakEvaluationTopologyUP
  OpenFamilyTopologyMathcomp VectorDaniellHypotheses AbstractDualWeakEncoding AbstractDualPartialPairing
  PartialFunctionUP PartialFunctionBasic PartialDualPairing MeasureUP MeasurableFunctionUP
  MeasurableTotalBasic MeasurableGraphEquivalence BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [abstract_unit_dual_pairing_measurable]:
    weak measurability of a unit dual field
    suffices for the original measurable pairing,
    supporting the Baire extension in Federer
    4.1.7, p. 359, by 2.5.12,
    pp. 103–105. No L1 premise or
    finite total measure is needed here. *)
Theorem abstract_unit_dual_pairing_measurable (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hSep:is_separable_normed_space hNY) (D:lmodType R)
    (ed:Hom D (Hom Y R^o)) (DN:D->R) (hD:is_continuous_dual hNY ed DN)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun d y=>ed d y) O)
    (mu:set X->\bar R) (hm:is_measure mu) (xi:X->D)
    (f:partial_function X (real_norm_metric_space hNY)):
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1)))->
  (forall x,DN (xi x)<=1)->is_measure_measurable_function mu f->
  is_measure_measurable_function mu (abstract_dual_partial_pairing ed xi f).
Proof.
move=>hXi hUnit hF.
pose k:=fun x=>@abstract_dual_weak_point R Y NY hNY D ed DN hD (xi x).
have hK:is_measure_measurable_function mu (partial_function_total k).
  exact:(@measurable_total_borel_postcomposition R X (open_family_topological_space hO.1)
    (weak_dual_space hNY) mu hm (fun x=>(xi x:open_family_topological_space hO.1))
    (@abstract_dual_weak_point R Y NY hNY D ed DN hD) hXi
    (continuous_borel_function (@abstract_dual_weak_point_continuous R Y NY hNY D ed DN hD O hO))).
have hKUnit x:dual_norm NY (val (k x))<=1.
  by rewrite /k abstract_dual_weak_point_norm;exact:hUnit.
have hGraph x z:partial_function_graph (partial_dual_pairing k f) x z<->
    partial_function_graph (abstract_dual_partial_pairing ed xi f) x z.
  by rewrite partial_dual_pairing_graph abstract_dual_partial_pairing_graph /k /abstract_dual_weak_point /=.
have [hMeas _]:=@partial_dual_pairing_measurable_summable R X Y NY hNY hSep mu hm k f hK hKUnit hF.
exact:(measurable_function_graph_equivalent hGraph hMeas).
Qed.
