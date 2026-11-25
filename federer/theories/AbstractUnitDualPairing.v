(** Federer (1969), 4.1.5, p. 350: the
    integral extension on the original L1 partial
    functions. Apply the earlier partial pairing
    theorem of 2.5.12 to the actual abstract dual,
    preserving its evaluation, norm and weak topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousDualUP WeakEvaluationTopologyUP
  OpenFamilyTopologyMathcomp VectorDaniellHypotheses AbstractDualWeakEncoding AbstractDualPartialPairing
  PartialFunctionUP PartialFunctionBasic PartialNormPower PartialDualPairing
  MeasureUP MeasurableFunctionUP MeasurableTotalBasic MeasurableGraphEquivalence
  BorelFunctionBasic MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureLpNorm
  MeasureLpMembershipUP MeasureLoneNormIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section AbstractUnitDualPairing.
Variable R:realType.
Variable X:choiceType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hSep:is_separable_normed_space hNY.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Hypothesis hD:is_continuous_dual hNY ed DN.
Variable O:set (set D).
Hypothesis hO:is_weak_evaluation_topology (fun a y=>ed a y) O.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Variable xi:X->D.
Hypothesis hXi:is_measure_measurable_function mu
  (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))).
Hypothesis hUnit:forall x,DN (xi x)<= 1.

(** Source for [abstract_unit_dual_pairing_summable]:
    the literal partial-domain pairing is measurable
    and its integral is bounded by the L1 norm,
    Federer 4.1.5, p. 350, using the last
    sentence of 2.5.12, p. 103. *)
Theorem abstract_unit_dual_pairing_summable
    (f:partial_function X (real_norm_metric_space hNY)):
  is_measure_lp_function mu 1 f ->
  is_measure_measurable_function mu (abstract_dual_partial_pairing ed xi f) /\
  exists c:R,is_measure_integral mu (abstract_dual_partial_pairing ed xi f) c%:E /\
    (`|c|%:E<=measure_lp_norm mu NY 1 f)%E.
Proof.
move=>hf.
pose k:=fun x=>@abstract_dual_weak_point R Y NY hNY D ed DN hD (xi x).
have hK:is_measure_measurable_function mu (partial_function_total k).
  exact:(@measurable_total_borel_postcomposition R X (open_family_topological_space hO.1)
    (weak_dual_space hNY) mu hm (fun x=>(xi x:open_family_topological_space hO.1))
    (@abstract_dual_weak_point R Y NY hNY D ed DN hD) hXi
    (continuous_borel_function (@abstract_dual_weak_point_continuous R Y NY hNY D ed DN hD O hO))).
have hKUnit x:dual_norm NY (val (k x))<= 1.
  by rewrite /k abstract_dual_weak_point_norm; exact:hUnit.
have hGraph x z:partial_function_graph (partial_dual_pairing k f) x z <->
    partial_function_graph (abstract_dual_partial_pairing ed xi f) x z.
  by rewrite partial_dual_pairing_graph abstract_dual_partial_pairing_graph /k /abstract_dual_weak_point /=.
have[hM hIntegral]:=@partial_dual_pairing_measurable_summable R X Y NY hNY hSep mu hm k f hK hKUnit hf.2.1.1.
split.
- exact:(measurable_function_graph_equivalent hGraph hM).
have hNonnegative:=@measure_lp_norm_nonnegative R X Y NY hNY mu 1 f hm hf.1 hf.2.1.1.
have hFinite:measure_lp_norm mu NY 1 f \is a fin_num.
  by rewrite (ge0_fin_numE hNonnegative); exact:hf.2.2.1.
have hNormIntegral:=@measure_lone_norm_integral R X Y NY hNY mu hm f hf.
have hNormValue:measure_lp_norm mu NY 1 f=(fine (measure_lp_norm mu NY 1 f))%:E by rewrite fineK.
rewrite hNormValue in hNormIntegral.
have[c [hC hBound]]:=hIntegral _ hNormIntegral.
exists c; split.
- exact:(measure_integral_graph_equivalent hGraph hC).
- by rewrite hNormValue lee_fin.
Qed.
End AbstractUnitDualPairing.
