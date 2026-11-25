(** Federer (1969), 2.10.28(3), p. 192: supporting laws of the limit A given
    by intersection of the finite level unions. Prove uniqueness and
    compactness directly from its abstract membership specification before
    choosing an implementation. These topological facts do not require the
    special cost identities or the single-root hypothesis, because every
    level is already a finite family of compact intervals. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [interval_tree_limit_unique]: supporting
    uniqueness of A in 2.10.28(3),
    p. 192, by its pointwise intersection
    of unions specification. *)
Lemma interval_tree_limit_unique (R : realType) (H : nat -> {fset compact_real_intervals R}) A B :
  is_special_interval_tree_limit H A -> is_special_interval_tree_limit H B -> A=B.
Proof.
move=> hA hB; apply/seteqP; split=> x hx.
- apply/(hB x); exact: (hA x).1 hx.
- apply/(hA x); exact: (hB x).1 hx.
Qed.

(** Source for [interval_tree_limit_level_subset]: direct
    containment of the intersection in each
    finite level union in 2.10.28(3), p. 192. *)
Lemma interval_tree_limit_level_subset (R : realType) (H : nat -> {fset compact_real_intervals R}) A :
  is_special_interval_tree_limit H A -> forall j,
  A `<=` \bigcup_(S in [set` H j]) val S.
Proof.
move=> hA j x hx; have [S [hS hxS]] := (hA x).1 hx j.
exists S=> //; exact hS.
Qed.

(** Source for [interval_tree_limit_intersection]: direct
    equality A=intersection of unions of H_j
    in 2.10.28(3), p. 192, derived
    from the abstract limit membership laws. *)
Lemma interval_tree_limit_intersection (R : realType) (H : nat -> {fset compact_real_intervals R}) A :
  is_special_interval_tree_limit H A ->
  A=\bigcap_j (\bigcup_(S in [set` H j]) val S).
Proof.
move=> hA; apply/seteqP; split=> x hx.
- move=> j _; exact: interval_tree_limit_level_subset hA j x hx.
- apply/(hA x)=> j; have [S hS hxS] := hx j Logic.I; by exists S.
Qed.

(** Source for [interval_tree_limit_closed]: supporting
    closedness of A in 2.10.28(3),
    p. 192, as an intersection of
    finite unions of closed intervals. *)
Lemma interval_tree_limit_closed (R : realType) (H : nat -> {fset compact_real_intervals R}) A :
  is_special_interval_tree_limit H A -> closed A.
Proof.
move=> hA; rewrite (interval_tree_limit_intersection hA).
apply: closed_bigI=> j _.
apply: closed_bigcup; first exact: finite_fset.
move=> S _; exact: compact_real_interval_closed (set_valP S).
Qed.

(** Source for [interval_tree_limit_compact]: supporting compactness of A in
    2.10.28(3), p. 192 A closed subset of its compact initial finite level
    union is compact, including empty initial and limiting sets. *)
Lemma interval_tree_limit_compact (R : realType) (H : nat -> {fset compact_real_intervals R}) A :
  is_special_interval_tree_limit H A -> compact A.
Proof.
move=> hA.
pose U := \bigcup_(S in [set` H 0%N]) val S.
have hU : compact U.
  rewrite /U bigcup_fset; apply: bigsetU_compact=> S _.
  exact: compact_real_interval_compact (set_valP S).
have hsub : A `<=` U := interval_tree_limit_level_subset hA 0%N.
have heq : A=U `&` A.
  apply/seteqP; split=> x hx; first by split; [exact: hsub x hx | exact hx].
  exact hx.2.
rewrite heq; exact: compact_closedI hU (interval_tree_limit_closed hA).
Qed.
