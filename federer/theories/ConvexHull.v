(** Public hull laws supporting Federer (1969), 2.10.2(1), p. 171. The
    intersection witness is opaque; all later diameter arguments use only
    these universal laws. Source context and comparisons:
    ConvexHullConstruction.v. *)
From mathcomp Require Import all_boot all_algebra classical_sets.
From Federer Require Import InnerConvex ConvexHullUP ConvexHullSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [convex_hull]: convex hull in Federer
    2.10.2(1), p. 171, accessed through its sealed laws. *)
Definition convex_hull (R : realFieldType) (V : lmodType R) (A : set V) :=
  @ConvexHull.value R V A.

(** Source for [convex_hull_specification]: supporting least
    convex superset property for Federer 2.10.2(1), p. 171. *)
Lemma convex_hull_specification (R : realFieldType) (V : lmodType R) (A : set V) :
  is_convex_hull A (convex_hull A).
Proof. exact: ConvexHull.laws. Qed.

(** Source for [convex_hull_includes]: the hull contains the
    original generator in Federer 2.10.2(1), p. 171. *)
Lemma convex_hull_includes (R : realFieldType) (V : lmodType R) (A : set V) :
  A `<=` convex_hull A.
Proof. exact: convex_hull_includes_law (convex_hull_specification A). Qed.

(** Source for [convex_hull_convex]: convexity of the new
    generator used in Federer 2.10.2(1), p. 171. *)
Lemma convex_hull_convex (R : realFieldType) (V : lmodType R) (A : set V) :
  is_inner_convex (convex_hull A).
Proof. exact: convex_hull_convex_law (convex_hull_specification A). Qed.

(** Source for [convex_hull_least]: supporting least-superset
    law for the diameter proof in Federer 2.10.2(1), p. 171. *)
Lemma convex_hull_least (R : realFieldType) (V : lmodType R) (A C : set V) :
  A `<=` C -> is_inner_convex C -> convex_hull A `<=` C.
Proof. exact (@convex_hull_least_law R V A (convex_hull A)
  (convex_hull_specification A) C). Qed.
