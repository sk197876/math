(** Federer (1969), 1.7.13, p. 37: d=dist(a,C) is the infimum of |a-x| for x
    in the nonempty set C. The specification separates lower bounds and
    approximation from existence of this real number. Neither closedness nor
    convexity is needed to define distance. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import InnerProductUP InnerNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_inner_set_distance]: Federer 1.7.13,
    p. 37, defining infimum: a nonnegative lower bound for
    all distances, approximated within every positive error by
    a point of C. These laws specify the number without selecting
    an approximating point or assuming a nearest point exists. *)
Record is_inner_set_distance (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (a : V) (C : set V) (d : R) : Prop := {
  inner_set_distance_nonnegative_law : 0 <= d;
  inner_set_distance_lower_law : forall x, C x -> d <= inner_norm hB (a-x);
  inner_set_distance_approx_law : forall eps, 0 < eps ->
    exists x, C x /\ inner_norm hB (a-x) < d+eps
}.

(** Source for [inner_set_distance_greatest_lower_bound]: Federer
    1.7.13, p. 37, supporting infimum property derived from
    the approximation law: every lower bound is at most d. *)
Lemma inner_set_distance_greatest_lower_bound (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    a C d (hd : is_inner_set_distance hB a C d) l :
  (forall x, C x -> l <= inner_norm hB (a-x)) -> l <= d.
Proof.
move=> hl; case: (leP l d) => // hdl.
have he : 0 < l-d by rewrite subr_gt0.
have [x [hx hnear]] := inner_set_distance_approx_law hd he.
rewrite [d+(l-d)]addrC subrK in hnear.
have hh := lt_le_trans hnear (hl x hx).
by rewrite ltxx in hh.
Qed.

(** Source for [inner_set_distance_unique]: Federer 1.7.13,
    p. 37, supporting uniqueness of the number d specified
    as the infimum, before the nearest-point theorem is proved. *)
Theorem inner_set_distance_unique (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) a C d e :
  is_inner_set_distance hB a C d -> is_inner_set_distance hB a C e -> d=e.
Proof.
move=> hd he; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@inner_set_distance_greatest_lower_bound R V B hB a C e he d (inner_set_distance_lower_law hd)).
- exact (@inner_set_distance_greatest_lower_bound R V B hB a C d hd e (inner_set_distance_lower_law he)).
Qed.
