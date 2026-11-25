(** Federer (1969), 4.1.4, p. 349, using 2.4.12,
    p. 87: evaluation of the actual vector integral by a
    continuous scalar functional is the original scalar
    integral. This adapter preserves the total integrand graph. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousRealFunctional
  PartialFunctionBasic MeasureVectorIntegralUP MeasureIntegralUP SummableRealFunctionUP
  MeasureIntegralGraphEquivalence MeasureIntegralUniqueness WeakDerivativeFieldVectorIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [vector_total_integral_functional_evaluation]:
    the original dual evaluation rule of 2.4.12, p. 87,
    applied to the unit-mass tests in 4.1.4, p. 349. *)
Lemma vector_total_integral_functional_evaluation (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (f:X->Y) (v:Y) (alpha:Hom Y R^o):
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) v ->
  is_continuous_real_functional hNY (hom_as_linear alpha) ->
  is_measure_integral mu (real_total_integrand (fun x=>alpha (f x))) (alpha v)%:E.
Proof.
move=>hI hAlpha.
apply:(measure_integral_graph_equivalent _ (hI.2 (hom_as_linear alpha) hAlpha))=>x z.
by rewrite total_functional_evaluation_graph real_total_integrand_graph hom_as_linearE.
Qed.

(** Source for [vector_total_integral_functional_value]: the
    unique scalar value of the original unit-test integral
    used in the last displayed limit of 4.1.4, p. 349. *)
Lemma vector_total_integral_functional_value (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (f:X->Y) (v:Y) (alpha:Hom Y R^o) (b:R):
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) v ->
  is_continuous_real_functional hNY (hom_as_linear alpha) ->
  is_measure_integral mu (real_total_integrand (fun x=>alpha (f x))) b%:E ->b=alpha v.
Proof.
move=>hI hAlpha hScalar.
have hEq:=measure_integral_unique hScalar (vector_total_integral_functional_evaluation hI hAlpha).
by injection hEq.
Qed.
