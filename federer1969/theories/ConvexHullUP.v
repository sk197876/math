(** Federer (1969), 1.8.1, p. 38: C is the convex hull of S. A hull is
    specified as the least convex superset, independently of its
    finite-combination construction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_convex_hull]: Federer 1.8.1, p. 38,
    the term convex hull: a convex superset contained in every
    other convex superset. These are laws, not an unproved existence axiom. *)
Record is_convex_hull (R : realFieldType) (V : lmodType R)
    (S C : set V) : Prop := {
  convex_hull_includes_law : S `<=` C;
  convex_hull_convex_law : is_inner_convex C;
  convex_hull_least_law : forall D, S `<=` D -> is_inner_convex D -> C `<=` D
}.

(** Source for [convex_hull_unique]: Federer 1.8.1, p. 38,
    supporting uniqueness of the least convex superset. *)
Theorem convex_hull_unique (R : realFieldType) (V : lmodType R)
    (S C D : set V) : is_convex_hull S C -> is_convex_hull S D -> C=D.
Proof.
move=> hC hD; apply/seteqP; split.
- exact (@convex_hull_least_law R V S C hC D (convex_hull_includes_law hD) (convex_hull_convex_law hD)).
- exact (@convex_hull_least_law R V S D hD C (convex_hull_includes_law hC) (convex_hull_convex_law hC)).
Qed.
