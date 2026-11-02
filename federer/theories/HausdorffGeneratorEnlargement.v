(** Federer (1969), 2.10.24, p. 188: containing-enlargement laws for all
    nonempty Hausdorff generators, including nonclosed and unbounded sets.
    Apply the sealed closed-generator enlargement to the closure of the
    source. Closure preserves diameter and cost by 2.10.2(1), p. 171;
    closing each intersecting set also gives the needed containment of the
    original diameter enlargement. Source context:
    ClosedHausdorffEnlargementUP.v. This extends only proved weak laws,
    leaving the sealed witness opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameterClosure DiameterEnlargements CaratheodoryWeakEnlargementUP
  HausdorffDiameterCost ClosedHausdorffEnlargementUP ClosedHausdorffEnlargement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_generator_enlargement]: supporting
    containing map for the original nonempty-set family
    of 2.10.2(1), p. 171, in the weighted
    application of 2.10.24, p. 188. Only composition
    with closure is exposed; the underlying closed
    enlargement remains behind its opaque interface. *)
Definition hausdorff_generator_enlargement (R : realType) (X : metricType R) (m : nat) (S : set X) :=
  @closed_hausdorff_enlargement R X m (closure S).

(** Source for [hausdorff_generator_enlargement_laws]: supporting
    weak growth laws for the all-nonempty-set Hausdorff
    application of 2.10.24, p. 188. Zero costs,
    zero diameters and unbounded sets are retained;
    finite costs are needed only at finite cutoffs. *)
Theorem hausdorff_generator_enlargement_laws (R : realType) (X : metricType R) (m : nat) :
  is_weak_caratheodory_enlargement [set S : set X | S!=set0]
    (@hausdorff_diameter_cost R X m) (@hausdorff_generator_enlargement R X m)
    (closed_hausdorff_enlargement_control R m).
Proof.
pose F := [set S : set X | closed S /\ S!=set0].
have hE := @closed_hausdorff_enlargement_specification R X m.
have hcl S (hS : S!=set0) : F (closure S).
  split; first exact: closed_closure.
  have [x hx] := hS; exists x; exact: subset_closure hx.
constructor.
- exact: weak_enlargement_constant_positive hE.
- move=> S hS; exact: hausdorff_diameter_cost_nonnegative.
- move=> S hS; exact: (weak_enlargement_member hE (hcl S hS)).2.
- move=> S hS x [U [hU [hmeet hdiam]] hxU].
  apply: (@weak_enlargement_contains R X F (@hausdorff_diameter_cost R X m)
    (@closed_hausdorff_enlargement R X m) (closed_hausdorff_enlargement_control R m) hE (closure S) (hcl S hS) x).
  exists (closure U); last exact: subset_closure hxU.
  split; first exact: hcl U hU.
  split.
  + move=> he; apply: hmeet; apply/seteqP; split=> [a [haU haS]|a []].
    have hbad : (closure U `&` closure S) a by split; exact: subset_closure.
    by rewrite he in hbad.
  + by rewrite !extended_metric_diameter_closure.
- move=> S hS.
  have hh := weak_enlargement_diameter hE (hcl S hS).
  by rewrite extended_metric_diameter_closure in hh.
- move=> S hS.
  have hh := weak_enlargement_cost hE (hcl S hS).
  by rewrite hausdorff_diameter_cost_closure in hh.
Qed.
