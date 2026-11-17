(** Cancellation of the positive ball coefficient in
    Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  SummableRealFunctionUP MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureFiniteRealScaleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_coefficient_integral_unscale]: supporting
    cancellation of alpha(n-m-k) in Federer 3.2.45,
    p. 279, by the original scalar integral law,
    2.4.4(3), p. 82. Actual finite integrand
    values and their original scalar coefficient are
    identified pointwise before scalar multiplication.
    No measurability or integral premise is imposed
    on the unscaled target function; its ordinary
    integral is the conclusion. *)
Lemma finite_coefficient_integral_unscale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (u : X -> real_line_metric R) (alpha a : R) :
  alpha!=0 -> (forall x, f x=(fine (f x))%:E) ->
  (forall x, u x=fine (f x)*alpha) ->
  is_measure_integral mu (real_total_integrand u) a%:E ->
  is_measure_integral mu (partial_function_total f) (alpha^-1*a)%:E.
Proof.
move=> hAlpha hFinite hCoefficient hIntegral.
have hScaled := @measure_finite_real_total_scale_integral R X mu hm u a alpha^-1 hIntegral.
have hFunction : (fun x : X => alpha^-1*u x)=(fun x : X => fine (f x)).
  apply: funext=> x; by rewrite hCoefficient mulrCA mulVf // mulr1.
rewrite hFunction in hScaled.
have hGraph x y : partial_function_graph (real_total_integrand (fun x : X => fine (f x))) x y <->
    partial_function_graph (partial_function_total f) x y.
  rewrite real_total_integrand_graph -hFinite; reflexivity.
exact: measure_integral_graph_equivalent hGraph hScaled.
Qed.
