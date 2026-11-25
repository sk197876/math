(** Federer (1969), 4.1.5, p. 350: the
    opaque integral pairing on the original L1
    partial functions. The independent integral laws
    and their existence proof precede this choice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousDualUP WeakEvaluationTopologyUP
  OpenFamilyTopologyMathcomp VectorDaniellHypotheses PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasurableFunctionUP DualLoneIntegralUP DualLoneIntegralExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type DualLoneIntegralSignature.
(** Source for [value]: the integral extension on L1, Federer 4.1.5, p. 350. *)
Parameter value:forall (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hSep:is_separable_normed_space hNY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (hm:is_measure mu) (xi:X->D)
    (hXi:is_measure_measurable_function mu
      (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))))
    (hUnit:forall x,DN (xi x)<= 1),partial_function X (real_norm_metric_space hNY)->R.
(** Source for [laws]: the original partial-domain integral, Federer 4.1.5, p. 350. *)
Parameter laws:forall (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hSep:is_separable_normed_space hNY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (hm:is_measure mu) (xi:X->D)
    (hXi:is_measure_measurable_function mu
      (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))))
    (hUnit:forall x,DN (xi x)<= 1),@is_dual_lone_integral R X Y NY hNY D ed xi mu (@value R X Y NY hNY hSep D ed DN hD O hO mu hm xi hXi hUnit).
End DualLoneIntegralSignature.
Module DualLoneIntegral:DualLoneIntegralSignature.
(** Source for [value]: a hidden witness of the proved integral extension, Federer 4.1.5, p. 350. *)
Definition value (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hSep:is_separable_normed_space hNY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (hm:is_measure mu) (xi:X->D)
    (hXi:is_measure_measurable_function mu
      (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))))
    (hUnit:forall x,DN (xi x)<= 1):partial_function X (real_norm_metric_space hNY)->R:=
  projT1 (cid (@dual_lone_integral_exists R X Y NY hNY hSep D ed DN hD O hO mu hm xi hXi hUnit)).
(** Source for [laws]: the hidden witness satisfies the independent integral law, Federer 4.1.5, p. 350. *)
Lemma laws (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hSep:is_separable_normed_space hNY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (hm:is_measure mu) (xi:X->D)
    (hXi:is_measure_measurable_function mu
      (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))))
    (hUnit:forall x,DN (xi x)<= 1):@is_dual_lone_integral R X Y NY hNY D ed xi mu (@value R X Y NY hNY hSep D ed DN hD O hO mu hm xi hXi hUnit).
Proof. exact:(projT2 (cid (@dual_lone_integral_exists R X Y NY hNY hSep D ed DN hD O hO mu hm xi hXi hUnit))). Qed.
End DualLoneIntegral.
