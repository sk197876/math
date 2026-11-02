(** Federer (1969), 2.10.2(1), p. 171: closed nonempty covers give the same
    Hausdorff measure as all nonempty covers. We prove equality from the two
    abstract specifications, using explicit cover maps in both directions.
    Source context: HausdorffLengthUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameter MetricDiameterClosure
  CaratheodoryLimitUP CaratheodoryTransport HausdorffLengthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonempty_closed_hull_member]: closure
    preserves nonemptiness and gives a closed cover member,
    supporting Federer 2.10.2(1), p. 171. *)
Lemma nonempty_closed_hull_member (R : realType) (X : metricType R)
    (A : @nonempty_metric_sets R X) :
  closed (closure (val A)) /\ closure (val A) !=set0.
Proof.
split; first exact: closed_closure.
have [x hx] := set_valP A; exists x; exact: subset_closure hx.
Qed.

(** Source for [nonempty_closed_hull]: the closure replacement of a cover
    member in Federer 2.10.2(1), p. 171 *)
Definition nonempty_closed_hull (R : realType) (X : metricType R)
    (A : @nonempty_metric_sets R X) : @nonempty_closed_metric_sets R X :=
  Sub (closure (val A)) (mem_set (nonempty_closed_hull_member A)).

(** Source for [nonempty_closed_forget]: each closed
    nonempty cover is also an unrestricted nonempty cover,
    the reverse comparison in Federer 2.10.2(1), p. 171. *)
Definition nonempty_closed_forget (R : realType) (X : metricType R)
    (A : @nonempty_closed_metric_sets R X) : @nonempty_metric_sets R X :=
  Sub (val A) (mem_set (set_valP A).2).

(** Source for [hausdorff_length_closed_cover_equality]: equality with the
    closed-cover construction in Federer 2.10.2(1), p. 171 Countable
    repetitions after taking closures are handled by the nonnegative-sum
    image inequality. *)
Theorem hausdorff_length_closed_cover_equality (R : realType) (X : metricType R)
    (mu rho : set X -> \bar R) :
  is_hausdorff_length mu -> is_closed_hausdorff_length rho -> forall A, mu A=rho A.
Proof.
move=> hm hr A.
have hclosed : rho (id @` A)<=mu A.
  apply: (@caratheodory_limit_transport R X X
    (@nonempty_metric_sets R X) (@nonempty_closed_metric_sets R X)
    (fun j => val j) (fun j => val j)
    (fun j => extended_metric_diameter (val j))
    (fun j => extended_metric_diameter (val j)) id (@nonempty_closed_hull R X)
    mu rho hm hr _ _ _ _ A).
  - move=> j; exact: metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
  - move=> j x hx; exact: subset_closure hx.
  - move=> j; change (extended_metric_diameter (closure (val j))<=extended_metric_diameter (val j)).
    by rewrite extended_metric_diameter_closure.
  - move=> j; change (extended_metric_diameter (closure (val j))<=extended_metric_diameter (val j)).
    by rewrite extended_metric_diameter_closure.
have hall : mu (id @` A)<=rho A.
  apply: (@caratheodory_limit_transport R X X
    (@nonempty_closed_metric_sets R X) (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => val j)
    (fun j => extended_metric_diameter (val j))
    (fun j => extended_metric_diameter (val j)) id (@nonempty_closed_forget R X)
    rho mu hr hm _ _ _ _ A).
  - move=> j; exact: metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
  - by move=> j x hx.
  - by move=> j.
  - by move=> j.
rewrite image_id in hclosed hall.
by apply/eqP; rewrite eq_le hall hclosed.
Qed.
