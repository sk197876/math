(** Federer (1969), 4.1.2, p. 347: scalar
    integrals are unchanged under the measure-preserving
    substitution used in convolution. The existing
    injective pushforward integral theorem is reused. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasurePushforward MeasureIntegralUP MeasureIntegralGraphEquivalence
  PartialFunctionUP PartialFunctionPrecomposition SummableRealFunctionUP InjectivePushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [invariant_real_total_integral]: exact integral
    substitution through an injective measure-preserving map,
    supporting Federer 4.1.2, p. 347. *)
Theorem invariant_real_total_integral (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (u:X->X) (f:X->R) a:
  injective u ->measure_pushforward u mu=mu ->
  is_measure_integral mu (real_total_integrand f) a%:E ->
  is_measure_integral mu (real_total_integrand (fun x=>f (u x))) a%:E.
Proof.
move=>hInj hInvariant hi.
have hPull:=(@injective_pushforward_integral_iff R X X mu hm u
  (real_total_integrand f) hInj a%:E).2.
rewrite hInvariant in hPull; have h:=hPull hi.
apply:(measure_integral_graph_equivalent _ h)=>x y.
change (partial_function_graph (real_total_integrand f) (u x) y <->
  partial_function_graph (real_total_integrand (fun x=>f (u x))) x y).
by rewrite !real_total_integrand_graph.
Qed.
