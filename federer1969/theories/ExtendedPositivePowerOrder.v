(** Federer (1969), 2.4.12, pp. 86–87: scalar power comparisons supporting
    the integral-root formula and lower semicontinuity. These are supporting
    order lemmas, not additional claims separately stated by either author. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedPositivePower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_positive_power_order_embedding]: supporting
    order reflection for the positive roots in Federer 2.4.12,
    p. 86. Both endpoints, including positive infinity, are
    covered by the inverse-power law. *)
Lemma extended_positive_power_order_embedding (R : realType) (x y : \bar R) (p : R) :
  0 <= x -> 0 <= y -> (0 < p)%R ->
  (extended_positive_power x p <= extended_positive_power y p) = (x <= y).
Proof.
move=> hx hy hp; apply/idP/idP; last by move=> hxy; exact (@extended_positive_power_monotone R x y p hx hxy hp).
move=> hxy.
have hi : (0 < p^-1)%R by rewrite invr_gt0.
have h := @extended_positive_power_monotone R _ _ p^-1
  (extended_positive_power_nonnegative x p) hxy hi.
by rewrite !extended_positive_power_root_cancel // in h.
Qed.

(** Source for [extended_positive_power_strict_order]: supporting
    strict threshold comparison in the lower-semicontinuity
    argument of Federer 2.4.12, p. 87. *)
Lemma extended_positive_power_strict_order (R : realType) (x y : \bar R) (p : R) :
  0 <= x -> 0 <= y -> (0 < p)%R ->
  (extended_positive_power x p < extended_positive_power y p) = (x < y).
Proof.
move=> hx hy hp.
by rewrite ltNge extended_positive_power_order_embedding // -ltNge.
Qed.

(** Source for [extended_positive_power_inverse_cancel]: the
    reverse root cancellation supporting Federer 2.4.12,
    p. 86; no finiteness of the argument is needed. *)
Lemma extended_positive_power_inverse_cancel (R : realType) (x : \bar R) (p : R) :
  0 <= x -> (0 < p)%R ->
  extended_positive_power (extended_positive_power x p^-1) p = x.
Proof.
move=> hx hp.
have hi : (0 < p^-1)%R by rewrite invr_gt0.
have h := @extended_positive_power_root_cancel R x p^-1 hx hi.
by rewrite invrK in h.
Qed.
