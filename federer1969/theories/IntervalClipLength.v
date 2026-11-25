(** Federer (1969), 2.10.28(1), proof p. 192: supporting scalar lengths for
    interval intersections. The nonnegative clipped length handles empty
    intersections and singletons uniformly. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_interval_clip_length]: supporting
    diameter of [a,b] intersect [c,d] in
    2.10.28(1), p. 192, with zero
    length for an empty or point intersection. *)
Definition real_interval_clip_length (R : realType) (a b c d : R) :=
  Order.max 0 (Order.min b d-Order.max a c).

(** Source for [interval_clip_length_full]: supporting
    unchanged length of a whole family member
    inside the test interval in 2.10.28(1),
    p. 192. *)
Lemma interval_clip_length_full (R : realType) (a b c d : R) :
  a<=c -> c<=d -> d<=b -> real_interval_clip_length a b c d=d-c.
Proof.
move=> hac hcd hdb; rewrite /real_interval_clip_length (min_r hdb) (max_r hac) max_r //.
by rewrite subr_ge0.
Qed.

(** Source for [interval_clip_length_left_zero]: supporting
    zero clipped cost for a member wholly
    to the left in 2.10.28(1), p. 192,
    including possible endpoint contact. *)
Lemma interval_clip_length_left_zero (R : realType) (a b c d : R) :
  d<=a -> real_interval_clip_length a b c d=0.
Proof.
move=> hda.
have hmin : Order.min b d<=d by rewrite ge_min lexx orbT.
have hmax : a<=Order.max a c by rewrite le_max lexx.
have hlen : Order.min b d-Order.max a c<=0 by lra.
by rewrite /real_interval_clip_length (max_l hlen).
Qed.

(** Source for [interval_clip_length_right_zero]: supporting
    zero clipped cost for a member wholly
    to the right in 2.10.28(1), p. 192,
    including possible endpoint contact. *)
Lemma interval_clip_length_right_zero (R : realType) (a b c d : R) :
  b<=c -> real_interval_clip_length a b c d=0.
Proof.
move=> hbc.
have hmin : Order.min b d<=b by rewrite ge_min lexx.
have hmax : c<=Order.max a c by rewrite le_max lexx orbT.
have hlen : Order.min b d-Order.max a c<=0 by lra.
by rewrite /real_interval_clip_length (max_l hlen).
Qed.

(** Source for [interval_clip_length_left_boundary]: supporting
    length of the left boundary intersection
    in 2.10.28(1), p. 192, including
    a zero-length endpoint placeholder. *)
Lemma interval_clip_length_left_boundary (R : realType) (a b c d : R) :
  c<=a -> a<=d -> d<=b -> real_interval_clip_length a b c d=d-a.
Proof.
move=> hca had hdb; rewrite /real_interval_clip_length (min_r hdb) (max_l hca) max_r //.
by rewrite subr_ge0.
Qed.

(** Source for [interval_clip_length_right_boundary]: supporting
    length of the right boundary intersection
    in 2.10.28(1), p. 192, including
    a zero-length endpoint placeholder. *)
Lemma interval_clip_length_right_boundary (R : realType) (a b c d : R) :
  a<=c -> c<=b -> b<=d -> real_interval_clip_length a b c d=b-c.
Proof.
move=> hac hcb hbd; rewrite /real_interval_clip_length (min_l hbd) (max_r hac) max_r //.
by rewrite subr_ge0.
Qed.
