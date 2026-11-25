(** Federer (1969), 4.1.5, p. 350:
    the original scalar evaluations of the unit
    weak-dual density are measurable and uniformly
    bounded. These estimates give the target-vector
    continuity used in the simultaneous formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousDualUP RealFunctionalNormUP
  WeakEvaluationTopologyUP OpenFamilyTopologyMathcomp WeakEvaluationMeasurableCoordinates
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasurableRealEmbedding
  MeasurableGraphEquivalence SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section WeakDualScalarEvaluation.
Variable R:realType.
Variable X:choiceType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Hypothesis hD:is_continuous_dual hNY ed DN.
Variable xi:X->D.
Hypothesis hUnit:forall x,DN (xi x)<= 1.

(** Source for [unit_dual_scalar_evaluation_bound]: the
    original unit dual bound for the scalar
    functions in Federer 4.1.5, p. 350. *)
Lemma unit_dual_scalar_evaluation_bound x y:`|ed (xi x) y|<=NY y.
Proof.
have hBound:=real_functional_norm_bound (continuous_dual_norm_laws hD (xi x)) y.
change (is_true (`|ed (xi x) y|<=DN (xi x)*NY y)) in hBound.
have hNorm:0<=NY y:=real_seminorm_nonnegative hNY.1 y.
have hUpper:=ler_wpM2r hNorm (hUnit x).
rewrite mul1r in hUpper; exact:le_trans hBound hUpper.
Qed.

(** Source for [unit_dual_scalar_evaluation_difference]: the
    original evaluations are uniformly one-Lipschitz
    in y, Federer 4.1.5, p. 350. *)
Lemma unit_dual_scalar_evaluation_difference x (y z:real_norm_metric_space hNY):
  `|ed (xi x) y-ed (xi x) z|<=mdist y z.
Proof.
change (is_true (`|ed (xi x) y-ed (xi x) z|<=NY (y-z))).
rewrite -linearB; exact:unit_dual_scalar_evaluation_bound.
Qed.

(** Source for [weak_dual_scalar_evaluation_measurable]: the
    literal finite scalar integrand used in
    Federer 4.1.5, p. 350, is measurable
    for the original weak evaluation topology. *)
Theorem weak_dual_scalar_evaluation_measurable (O:set (set D))
    (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (hm:is_measure mu):
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))) ->
  forall y,is_measure_measurable_function mu (real_total_integrand (fun x=>ed (xi x) y)).
Proof.
move=>hXi y.
have hCoordinate:=@weak_evaluation_measurable_coordinates R X Y D (fun a y=>ed a y) O hO mu hm xi hXi y.
have hEmbedded:=measurable_total_real_embedding hm hCoordinate.
apply:(@measurable_function_graph_equivalent R X _ mu _ _ _ hEmbedded)=>x z.
change ((ed (xi x) y)%:E=z <->partial_function_graph (real_total_integrand (fun x=>ed (xi x) y)) x z).
by rewrite real_total_integrand_graph.
Qed.
End WeakDualScalarEvaluation.
