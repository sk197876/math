(** Federer (1969), 2.4.18(1), p. 90: integral transport
    along a measure-preserving injection. The inverse-image
    cutoff is kept explicit; no finite total measure or
    global completion equivalence is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionPrecomposition PartialZeroExtension PartialZeroExtensionPrecomposition
  MeasureUP MeasurePushforward MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence InjectivePushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [invariant_subset_integral_transport]: the
    subset form of the integral identity in Federer 2.4.18(1),
    p. 90, used for curve parameters in 3.2.46, p. 281.
    Values and definedness are preserved for the actual partial graph. *)
Lemma invariant_subset_integral_transport (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> X)
    (A : set X) (f : partial_function X (extended_real_line R)) v :
  injective u -> measure_pushforward u mu = mu ->
  is_measure_subset_integral mu A f v ->
  is_measure_subset_integral mu (u @^-1` A) (partial_function_precompose u f) v.
Proof.
move=> hInj hPush hIntegral.
have hTransport := (@injective_pushforward_integral_iff R X X mu hm u
  (partial_function_zero_extension (0 : extended_real_line R) A f) hInj v).2.
rewrite hPush in hTransport.
exact: measure_integral_graph_equivalent (@partial_zero_extension_precompose_graph X X (extended_real_line R) u 0 A f)
  (hTransport hIntegral).
Qed.
