(** Federer (1969), 4.1.8, p. 362: moving
    interval integrals between the original scalar
    line and its Euclidean or full-domain copy.
    Reuse the original signed image-integral theorem
    of 2.4.18(1), p. 90, and the exact
    subset graph of 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition
  PartialZeroExtension PartialZeroExtensionPrecomposition MeasureUP MeasurePushforward
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence InjectivePushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [injective_image_subset_integral_iff]: the
    original target subset integral is exactly its
    inverse-image subset integral under a measure-preserving
    injection, supporting Federer 4.1.8, p. 362,
    by 2.4.18(1), p. 90. Both definedness
    directions retain the actual partial graph and
    every signed integral value. *)
Lemma injective_image_subset_integral_iff (R:realType) (X Y:choiceType)
    (mu:set X->\bar R) (nu:set Y->\bar R) (hMu:is_measure mu)
    (u:X->Y) (A:set Y) (f:partial_function Y (extended_real_line R)) v:
  injective u->measure_pushforward u mu=nu->
  (is_measure_subset_integral nu A f v <->
    is_measure_subset_integral mu (u @^-1` A) (partial_function_precompose u f) v).
Proof.
move=>hInj hPush.
have hIff:=@injective_pushforward_integral_iff R X Y mu hMu u
  (partial_function_zero_extension (0:extended_real_line R) A f) hInj v.
rewrite hPush in hIff.
have hGraph:=@partial_zero_extension_precompose_graph X Y (extended_real_line R) u 0 A f.
split=>hIntegral.
- exact:(measure_integral_graph_equivalent hGraph (hIff.2 hIntegral)).
- apply:hIff.1.
  exact:(measure_integral_graph_equivalent (fun x z=>iff_sym (hGraph x z)) hIntegral).
Qed.
