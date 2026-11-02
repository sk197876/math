(** Federer (1969), 2.3.8, p. 78: common separable linear subspaces
    supporting additive closure and automatic essential separability. The
    countable-family form also supports 2.3.9, pp. 79–80. Only the sealed
    closed-span laws are used here. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric MetricSubsetBackground
  MetricSubsetDenseImage ClosedLinearSpanUP ClosedLinearSpanSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_separable_sets_linear_envelope]: supporting common
    closed separable linear envelope for Federer 2.3.8, p. 78, and 2.3.9,
    pp. 79–80 This background result works for separable subsets, without
    assuming they are linear. *)
Theorem countable_separable_sets_linear_envelope (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (A : nat -> set (real_norm_metric_space hN)) :
  (forall n, exists D : set (metric_subset (A n)), countable D /\ dense D) ->
  exists Z : subspace V, is_separable_linear_envelope (\bigcup_n A n) Z.
Proof.
move=> hs.
pose D n := projT1 (cid (hs n)).
have hD n := projT2 (cid (hs n)).
pose E n := (fun z : metric_subset (A n) => (val z : real_norm_metric_space hN)) @` D n.
pose H := \bigcup_n E n.
have hc : countable H.
  apply: bigcup_countable; first exact: countableP.
  move=> n _; exact: metric_subset_dense_image_countable (hD n).1.
pose Z := ClosedLinearSpan.value H.
have hZ := ClosedLinearSpan.laws H.
exists Z; split; first exact: closed_linear_span_closed hZ.
split; last exact: ClosedLinearSpan.countable_separable hc.
move=> x [n _ hx].
have he : closure (E n) x := @metric_subset_dense_image_closure R _ (A n) (D n) (hD n).2 x hx.
apply: (closed_linear_span_closed hZ).
have hsub : E n `<=` (fun y : real_norm_metric_space hN => Z y).
  move=> y hy; apply: (closed_linear_span_contains hZ); by exists n.
exact (@closureS [the topologicalType of real_norm_metric_space hN] _ _ hsub x he).
Qed.

(** Source for [separable_set_linear_envelope]: supporting
    closed separable linear envelope for the automatic-separability
    assertion of Federer 2.3.8, p. 78. *)
Theorem separable_set_linear_envelope (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (A : set (real_norm_metric_space hN)) :
  (exists D : set (metric_subset A), countable D /\ dense D) ->
  exists Z : subspace V, is_separable_linear_envelope A Z.
Proof.
move=> hs; have [Z [hc [hi hd]]] :=
  @countable_separable_sets_linear_envelope R V N hN (fun _ => A) (fun _ => hs).
exists Z; split=> //; split=> // x hx; apply: hi; by exists 0%N.
Qed.
