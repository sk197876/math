(** Federer (1969), 4.1.7, p. 359:
    the normalized exterior-image pairing extends
    to the whole original target L1 space.
    This supporting existence theorem composes the
    proved source unit-dual integral of 4.1.5,
    p. 350, with the exact image L1
    pullback of 2.4.18, pp. 90–91. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionBasic Hom RealNormUP NormMetric ContinuousDualUP WeakEvaluationTopologyUP
  OpenFamilyTopologyMathcomp VectorDaniellHypotheses PartialFunctionUP PartialFunctionPrecomposition
  MeasureUP MeasurePushforward RadonMeasureUP CountablyMeasurableUP MeasurableFunctionUP
  MeasureLpMembershipUP MeasureLpConvergence MeasureIntegralUP AbstractDualPartialPairing
  DualLoneIntegralUP DualLoneIntegralSealed DualLoneIntegralLipschitz RadonImageLpPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RadonImageUnitPairing.
Variable R:realType.
Variables A B:topologicalType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hSep:is_separable_normed_space hNY.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Hypothesis hDual:is_continuous_dual hNY ed DN.
Variable O:set (set D).
Hypothesis hO:is_weak_evaluation_topology (fun d y=>ed d y) O.
Variable mu:set A->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hr:is_radon_measure mu.
Variable f:A->B.
Hypothesis hf:continuous f.
Local Notation nu := (measure_pushforward f mu).
Hypothesis hNu:is_radon_measure nu.
Hypothesis hCountable:measure_countably_measurable nu setT.
Variable xi:A->D.
Hypothesis hXi:is_measure_measurable_function mu
  (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))).
Hypothesis hUnit:forall x,DN (xi x)<=1.

(** Source for [radon_image_unit_pairing_exists]:
    the original source pairing defines a
    one-Lipschitz functional on every original
    partial L1(nu) field, supporting the
    Baire projection argument in Federer 4.1.7,
    p. 359. Existence and the bound
    are conclusions of the earlier integral
    laws, not premises about a pushforward. *)
Theorem radon_image_unit_pairing_exists:
  exists J:partial_function B (real_norm_metric_space hNY)->R,
    (forall eta,is_measure_lp_function nu 1 eta->
      is_measure_integral mu (abstract_dual_partial_pairing ed xi (partial_function_precompose f eta))
        (J eta)%:E) /\
    forall eta zeta,is_measure_lp_function nu 1 eta->is_measure_lp_function nu 1 zeta->
      (`|J eta-J zeta|%:E<=measure_lp_distance nu NY 1 eta zeta)%E.
Proof.
have [C [hCount hDense]]:=hSep.
pose I:=@DualLoneIntegral.value R A Y NY hNY hSep D ed DN hDual O hO mu hm xi hXi hUnit.
have hI:=@DualLoneIntegral.laws R A Y NY hNY hSep D ed DN hDual O hO mu hm xi hXi hUnit.
pose J eta:=I (partial_function_precompose f eta).
exists J;split.
- move=>eta hEta.
  have [hPull _]:=@radon_image_lp_pullback R A B Y NY hNY mu hm hr f hf hNu C hCount hDense
    hCountable 1 eta hEta.
  exact:(hI _ hPull).
- move=>eta zeta hEta hZeta.
  have [hPullEta _]:=@radon_image_lp_pullback R A B Y NY hNY mu hm hr f hf hNu C hCount hDense
    hCountable 1 eta hEta.
  have [hPullZeta _]:=@radon_image_lp_pullback R A B Y NY hNY mu hm hr f hf hNu C hCount hDense
    hCountable 1 zeta hZeta.
  have hBound:=@dual_lone_integral_lipschitz R A Y NY hNY hSep D ed DN hDual O hO mu hm xi
    hXi hUnit I hI _ _ hPullEta hPullZeta.
  have hDistance:=@radon_image_lp_pullback_distance R A B Y NY hNY mu hm hr f hf hNu C hCount hDense
    hCountable 1 eta zeta hEta hZeta.
  by rewrite hDistance in hBound.
Qed.
End RadonImageUnitPairing.
