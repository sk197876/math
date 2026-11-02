(** Supporting uniform bounds for the elementary primitive estimates in
    Federer (1969), 2.6.3(2), pp. 117–118 This is the usual general-topology
    compactness argument: the continuous image of a compact segment is
    compact and bounded. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology normedtype lra.
From Federer Require Import StieltjesDaniellIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_positive_segment_bound]: supporting finite
    positive bound on a continuous integrand or primitive in Federer
    2.6.3(2), pp. 117–118 Empty segments are permitted. *)
Lemma continuous_positive_segment_bound (R : realType) (f : R -> R) (a b : R) :
  continuous f -> exists M : R, 0 < M /\ forall x, a <= x <= b -> `|f x| <= M.
Proof.
move=> hf.
have hc : compact (f @` `[a,b]).
  apply: continuous_compact _ (@segment_compact R a b); exact: continuous_subspaceT hf.
have [M hM] := @compact_real_bounded R _ hc.
exists (`|M|+1); split; first by have := normr_ge0 M; lra.
move=> x hx; have hfx : (f @` `[a,b]) (f x).
  exists x; first by rewrite /= in_itv /=; exact hx.
  by [].
have hb := hM _ hfx; have hm := ler_norm M; lra.
Qed.
