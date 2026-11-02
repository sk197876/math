(** Federer (1969), 3.2.35, pp. 271--272:
    the actual projected sets retain convexity. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanProjectionSpace EuclideanProjectionMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_projection_convex_image]:
    convexity of p(S) in Cauchy's fibre
    argument and Steiner's induction, Federer
    3.2.35, p. 272. Actual linearity
    transports every original convex combination. *)
Lemma euclidean_projection_convex_image (R:realType) n m
    (p:orthogonal_projection_metric_space R n m) (S:set (R_n R n)):
  is_inner_convex S ->is_inner_convex (euclidean_projection_linear p @` S).
Proof.
move=>hS y z [u hu <-] [v hv <-] t ht0 ht1.
exists ((1-t)*:u+t*:v); first exact:hS u v hu hv t ht0 ht1.
by rewrite linearD !linearZ.
Qed.
