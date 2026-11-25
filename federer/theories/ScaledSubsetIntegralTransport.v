(** Federer (1969), 4.1.8, p. 362: the
    original affine interval change of parameter uses
    the signed image integral of 2.4.18(1),
    p. 90, and positive measure scaling. This
    supporting form preserves arbitrary partial graphs
    and every original integration subset. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition
  PartialZeroExtension PartialZeroExtensionPrecomposition MeasureUP MeasurePushforward MeasureScaleIntegral
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence InjectivePushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scaled_subset_integral_transport]: the
    actual subset integral pulled back by an injection
    whose image measure is c times the target
    measure is multiplied by c, supporting the
    interval change of parameter in Federer 4.1.8,
    p. 362, by 2.4.18(1), p. 90. No
    finite-mass or total-integrand premise is added. *)
Lemma scaled_subset_integral_transport (R:realType) (X Y:choiceType)
    (mu:set X->\bar R) (nu:set Y->\bar R) (hMu:is_measure mu) (hNu:is_measure nu)
    (u:X->Y) (c:R) (A:set Y) (f:partial_function Y (extended_real_line R)) v:
  injective u ->(0<c)%R->measure_pushforward u mu=measure_scale c nu ->
  is_measure_subset_integral nu A f v ->
  is_measure_subset_integral mu (u @^-1` A) (partial_function_precompose u f) (c%:E*v).
Proof.
move=>hInj hc hPush hIntegral.
have hScaled:=@measure_scale_integral R Y nu hNu c hc
  (partial_function_zero_extension (0:extended_real_line R) A f) v hIntegral.
rewrite -hPush in hScaled.
have hSource:=(@injective_pushforward_integral_iff R X Y mu hMu u
  (partial_function_zero_extension (0:extended_real_line R) A f) hInj (c%:E*v)).2 hScaled.
exact:(measure_integral_graph_equivalent
  (@partial_zero_extension_precompose_graph X Y (extended_real_line R) u 0 A f) hSource).
Qed.
