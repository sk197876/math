(** Federer (1969), 4.1.4, p. 349: once g_e is constant
    on a test support, its distribution integral is that
    constant dual functional applied to the vector integral.
    This uses the original dual characterization of 2.4.12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousDualUP
  PartialFunctionBasic MeasureIntegralUP SummableRealFunctionUP
  MeasureIntegralGraphEquivalence MeasureIntegralUniqueness MeasureVectorIntegralUP WeakDerivativeFieldVectorIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [distribution_constant_density_action]: the
    integral of <f,g_e> reduces to <integral f,alpha_e>
    when g_e=alpha_e on the support, the first limit formula
    in Federer 4.1.4, p. 349. The actual vector integral and
    original scalar integral are retained. *)
Theorem distribution_constant_density_action (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (YD:lmodType R) (ed:Hom YD (Hom Y R^o)) (DN:YD->R)
    (hYD:is_continuous_dual hNY ed DN)
    (mu:set X->\bar R) (f:X->Y) (v:Y) (g:X->YD) (a:YD) (b:R):
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) v ->
  (forall x,f x<>0 ->g x=a) ->
  is_measure_integral mu (real_total_integrand (fun x=>ed (g x) (f x))) b%:E ->
  b=ed a v.
Proof.
move=>hVector hConst hIntegral.
have hFunctional:=hVector.2 (hom_as_linear (ed a)) (@continuous_dual_continuous R Y NY hNY YD ed DN hYD a).
have hSame:is_measure_integral mu
    (real_total_integrand (fun x=>ed (g x) (f x))) (ed a v)%:E.
  apply:(measure_integral_graph_equivalent _ hFunctional)=>x z.
  rewrite total_functional_evaluation_graph real_total_integrand_graph.
  have hValue:ed (g x) (f x)=ed a (f x).
    case:(pselect (f x=0))=>[hZero|hNot].
    - by rewrite hZero !linear0.
    - by rewrite (@hConst x hNot).
  by rewrite hom_as_linearE hValue.
have hEq:=measure_integral_unique hIntegral hSame.
by injection hEq.
Qed.
