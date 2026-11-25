(** Federer (1969), 4.1.5, p. 350:
    existence of the integral extension on L1,
    using the partial-domain pairing theorem already
    proved in 2.5.12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousDualUP WeakEvaluationTopologyUP
  OpenFamilyTopologyMathcomp VectorDaniellHypotheses PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasurableFunctionUP MeasureLpMembershipUP MeasureIntegralUP AbstractDualPartialPairing
  AbstractUnitDualPairing DualLoneIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dual_lone_integral_exists]: every weakly
    measurable unit-dual density has its integral
    pairing on the whole original L1 space,
    Federer 4.1.5, p. 350. *)
Theorem dual_lone_integral_exists (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hSep:is_separable_normed_space hNY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (hm:is_measure mu) (xi:X->D)
    (hXi:is_measure_measurable_function mu
      (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))))
    (hUnit:forall x,DN (xi x)<= 1):
  exists I,@is_dual_lone_integral R X Y NY hNY D ed xi mu I.
Proof.
have hAt (f:partial_function X (real_norm_metric_space hNY)):
    exists c:R,is_measure_lp_function mu 1 f ->
      is_measure_integral mu (abstract_dual_partial_pairing ed xi f) c%:E.
  case:(pselect (is_measure_lp_function mu 1 f))=>hf.
  - have[_ [c [hC _]]]:=@abstract_unit_dual_pairing_summable R X Y NY hNY hSep
      D ed DN hD O hO mu hm xi hXi hUnit f hf.
    by exists c.
  - exists 0; by move=>h; exact:(False_ind _ (hf h)).
have[I hI]:=choice hAt.
by exists I.
Qed.
