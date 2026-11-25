(** Federer (1969), 4.1.1, p. 346: integration
    of translated compactly supported functions
    uses the translation invariance already proved
    in 2.7.16, p. 135, and the signed
    image-integral theorem 2.4.18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasurePushforward MeasureIntegralUP MeasureIntegralGraphEquivalence
  PartialFunctionUP PartialFunctionPrecomposition SummableRealFunctionUP InjectivePushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [real_translation_integral]: a translated
    real integrand has its original signed integral
    for a translation-invariant measure, supporting
    Federer 4.1.1, p. 346. No positivity
    of the integrand is assumed. *)
Theorem real_translation_integral (R:realType) (X:lmodType R)
    (mu:set X->\bar R) (hm:is_measure mu) (c:X) (f:X->R) a:
  measure_pushforward (fun x=>x+c) mu=mu ->
  is_measure_integral mu (real_total_integrand f) a%:E ->
  is_measure_integral mu (real_total_integrand (fun x=>f (x+c))) a%:E.
Proof.
move=>hInvariant hi.
have hInj:injective (fun x:X=>x+c).
  move=>x y h; have h':=congr1 (fun z:X=>z-c) h; by rewrite !addrK in h'.
have hPull:=(@injective_pushforward_integral_iff R X X mu hm (fun x=>x+c)
  (real_total_integrand f) hInj a%:E).2.
rewrite hInvariant in hPull; have h:=hPull hi.
apply:(measure_integral_graph_equivalent _ h)=>x y.
change (partial_function_graph (real_total_integrand f) (x+c) y <->
  partial_function_graph (real_total_integrand (fun x=>f (x+c))) x y).
by rewrite !real_total_integrand_graph.
Qed.
