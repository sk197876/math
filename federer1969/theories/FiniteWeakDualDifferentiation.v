(** Federer (1969), 4.1.5, p. 350:
    differentiation of the original scalar pairings
    holds simultaneously for every target vector.
    Apply 2.9.8 on a countable dense subset
    and use the closed limit locus from the
    proved uniformly Lipschitz mean family. Only
    the target Y is required to be separable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousDualUP WeakEvaluationTopologyUP
  OpenFamilyTopologyMathcomp VectorDaniellHypotheses WeakDualScalarEvaluation PartialFunctionUP
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureDerivationContext CoveringRelationUP CoveringRelationLimits CoveringLipschitzFamily
  MeasureMeanFunction SummableRealFunctionUP FiniteBoundedRealDifferentiation
  ScalarEvaluationMeanFamily NormClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_weak_dual_simultaneous_differentiation]:
    the simultaneous y quantifier in the
    integral-mean identity of Federer 4.1.5,
    p. 350. This finite localized statement
    retains all original partial quotient domains. *)
Theorem finite_weak_dual_simultaneous_differentiation (R:realType) (X:metricType R)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (hSep:is_separable_normed_space hNY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (V:X->set X->Prop) (xi:X->D):
  is_measure_derivation_context mu V ->(mu setT< +oo)%E ->
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))) ->
  (forall x,DN (xi x)<= 1) ->
  measure_almost_everywhere mu [set x|forall y:Y,
    partial_function_graph
      (covering_relation_limit V (measure_mean_function mu (real_total_integrand (fun z=>ed (xi z) y))))
      x (ed (xi x) y)%:E].
Proof.
move=>hContext hFinite hXi hUnit.
have hm:=derivation_measure_law (derivation_context_measure hContext).
have hMeasurable:=@weak_dual_scalar_evaluation_measurable R X Y D ed xi O hO mu hm hXi.
have hBound:=@unit_dual_scalar_evaluation_bound R X Y NY hNY D ed DN hD xi hUnit.
have hDifference:=@unit_dual_scalar_evaluation_difference R X Y NY hNY D ed DN hD xi hUnit.
pose f:=fun (y:real_norm_metric_space hNY) x=>ed (xi x) y.
have hLocal y:=@finite_bounded_real_locally_absolutely_integrable R X mu hm (f y) (NY y)
  hFinite (hMeasurable y) (fun x=>hBound x y).
have hFamily:=@scalar_evaluation_mean_family R X (real_norm_metric_space hNY)
  mu V hContext f hMeasurable hLocal (fun y z x=>hDifference x y z).
have[C [hCountable hDense]]:=hSep.
pose P y:=partial_function_agreement
  (covering_relation_limit V (measure_mean_function mu (real_total_integrand (f y))))
  (real_total_integrand (f y)).
have hAlmost:measure_almost_everywhere mu (\bigcap_(y in C) P y).
  apply:(@measure_almost_everywhere_countable R X (real_norm_metric_space hNY)
    mu hm C P hCountable)=>y _.
  exact:(@finite_bounded_real_differentiation R X mu V (f y) (NY y)
    hContext hFinite (hMeasurable y) (fun x=>hBound x y)).
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hAlmost)=>x hAt y.
pose l:=fun z:real_norm_metric_space hNY=>ed (xi x) z.
pose T: set (real_norm_metric_space hNY):=[set z|
  partial_function_graph (covering_relation_limit V (measure_mean_function mu (real_total_integrand (f z)))) x (l z)%:E].
have hClosed:closed T.
  exact:(@covering_lipschitz_limit_locus_closed R X (real_norm_metric_space hNY) V
    (fun y=>measure_mean_function mu (real_total_integrand (f y))) 1 l x ltr01 hFamily
    (fun z w=>hDifference x z w)).
have hContains:C `<=` T.
  move=>z hz; have[a [hA hValue]]:=hAt z hz.
  have hScalar: (f z x)%:E=a:=(real_total_integrand_graph (f z) x a).1 hValue.
  by rewrite /T /l /f -hScalar in hA *.
exact:(@dense_closed_superset_all (real_norm_metric_space hNY) C T hDense hClosed hContains y).
Qed.
