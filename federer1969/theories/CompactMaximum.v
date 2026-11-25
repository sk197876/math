(** Federer (1969), 1.7.3, p. 29: supporting attainment of the maximum on
    each compact constrained unit sphere. This general topological lemma is
    proved from compact images, closedness, and the real supremum. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_compact_maximum]: Federer 1.7.3,
    p. 29, supporting extreme-value fact: a continuous real function
    on a nonempty compact set attains its maximum. This is the
    general topology used to choose successive principal axes. *)
Theorem continuous_compact_maximum (R : realType) (T : topologicalType)
    (A : set T) (f : T -> R^o) : A !=set0 -> compact A ->
    continuous f -> exists x, A x /\ forall y, A y -> f y <= f x.
Proof.
move=> hA hc hf.
have hne : f @` A !=set0 := image_nonempty f hA.
have hic : compact (f @` A).
  apply: continuous_compact hc; exact: continuous_subspaceT hf.
have hs : has_sup (f @` A) := compact_has_sup hne hic.
have hsup : supremums (f @` A) (sup (f @` A)).
  split; first exact: sup_upper_bound hs.
  move=> b hb; exact: ge_sup hne hb.
have [x hx hfx] := itv_closed_supremums hne (compact_closed (@norm_hausdorff R _) hic) hsup.
exists x; split=> // y hy; rewrite hfx.
apply: (@sup_upper_bound R (f @` A) hs); by exists y.
Qed.
