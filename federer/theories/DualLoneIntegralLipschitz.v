(** Federer (1969), 4.1.5, p. 350:
    continuity of the integral extension for the
    original L1 seminorm, including conull partial
    domains. Its Lipschitz bound follows from the
    earlier unit-dual pairing estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousDualUP WeakEvaluationTopologyUP
  OpenFamilyTopologyMathcomp VectorDaniellHypotheses PartialFunctionUP PartialFunctionBasic
  PartialNormedArithmetic MeasureUP MeasurableFunctionUP MeasureLpNorm MeasureLpMembershipUP
  MeasureLpConvergence MeasureLpDifferenceMembership MeasureIntegralUP MeasureIntegralUniqueness
  AbstractUnitDualPairing DualLoneIntegralUP AbstractDualPairingDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DualLoneIntegralLipschitz.
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
Variable I:partial_function X (real_norm_metric_space hNY)->R.
Hypothesis hI:@is_dual_lone_integral R X Y NY hNY D ed xi mu I.

(** Source for [dual_lone_integral_lipschitz]: the L1
    extension has operator bound at most one,
    supporting its stated continuity in Federer
    4.1.5, p. 350. *)
Theorem dual_lone_integral_lipschitz (f g:partial_function X (real_norm_metric_space hNY)):
  is_measure_lp_function mu 1 f ->is_measure_lp_function mu 1 g ->
  (`|I f-I g|%:E<=measure_lp_distance mu NY 1 f g)%E.
Proof.
move=>hf hg.
have hDifference:=@measure_lp_function_subtract R X Y NY hNY mu hm 1 f g hf hg.
have[_ [c [hC hBound]]]:=@abstract_unit_dual_pairing_summable R X Y NY hNY hSep
  D ed DN hD O hO mu hm xi hXi hUnit _ hDifference.
have hIntegral:=@abstract_dual_pairing_difference_integral R X Y D ed xi mu hm f g
  (I f) (I g) (@hI f hf) (@hI g hg).
have hEq:=measure_integral_unique hC hIntegral.
have hCValue:c=I f-I g by injection hEq.
by rewrite -hCValue.
Qed.

(** Source for [dual_lone_integral_continuity]: the original
    L1 seminorm continuity of the extension, Federer
    4.1.5, p. 350. The same epsilon
    is a valid distance threshold. *)
Theorem dual_lone_integral_continuity (f:partial_function X (real_norm_metric_space hNY)):
  is_measure_lp_function mu 1 f ->forall epsilon:R,0<epsilon ->
  exists delta:R,0<delta /\ forall g,is_measure_lp_function mu 1 g ->
    (measure_lp_distance mu NY 1 g f<delta%:E)%E ->`|I g-I f|<epsilon.
Proof.
move=>hf epsilon hEpsilon; exists epsilon; split=>//.
move=>g hg hDistance.
have hBound:=dual_lone_integral_lipschitz hg hf.
have hStrict:=le_lt_trans hBound hDistance.
by move:hStrict; rewrite lte_fin.
Qed.
End DualLoneIntegralLipschitz.
