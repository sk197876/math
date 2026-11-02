(** Federer (1969), 1.7.13, p. 37: a closest point of a nonempty closed
    convex set. Its defining laws are separated from the completeness proof
    and from selection of a witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import InnerProductUP InnerNorm InnerSetDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_inner_nearest]: Federer 1.7.13, p. 37,
    a point c of C minimises the distance to a. The specification
    neither chooses c nor assumes its existence. *)
Record is_inner_nearest (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (a : V) (C : set V) (c : V) : Prop := {
  inner_nearest_member_law : C c;
  inner_nearest_minimal_law : forall x, C x ->
    inner_norm hB (a-c) <= inner_norm hB (a-x)
}.

(** Source for [inner_nearest_distance]: Federer 1.7.13,
    p. 37, the equation d=|a-c| for a nearest point. This
    follows from the lower-bound and approximation laws for d. *)
Lemma inner_nearest_distance (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) a C d c :
    is_inner_set_distance hB a C d -> is_inner_nearest hB a C c ->
    d = inner_norm hB (a-c).
Proof.
move=> hd hc; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@inner_set_distance_lower_law R V B hB a C d hd c (inner_nearest_member_law hc)).
- exact (@inner_set_distance_greatest_lower_bound R V B hB a C d hd
    (inner_norm hB (a-c)) (inner_nearest_minimal_law hc)).
Qed.
