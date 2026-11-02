(** Opaque hull witness supporting Federer (1969),
    2.10.2(1), p. 171. Source comparison and construction
    boundary: ConvexHullConstruction.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets.
From Federer Require Import ConvexHullUP ConvexHullConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type ConvexHullSignature.
(** Source for [value]: the convex hull used in Federer
    2.10.2(1), p. 171, specified by its universal property. *)
Parameter value : forall (R : realFieldType) (V : lmodType R), set V -> set V.
(** Source for [laws]: least convex superset laws supporting
    the hull replacement in Federer 2.10.2(1), p. 171. *)
Parameter laws : forall (R : realFieldType) (V : lmodType R) (A : set V),
  is_convex_hull A (@value R V A).
End ConvexHullSignature.

Module ConvexHull : ConvexHullSignature.
(** Source for [value]: choice from the proved hull-existence
    theorem supporting Federer 2.10.2(1), p. 171. *)
Definition value (R : realFieldType) (V : lmodType R) (A : set V) :=
  projT1 (cid (@convex_hull_exists R V A)).
(** Source for [laws]: proved universal laws of the selected
    hull supporting Federer 2.10.2(1), p. 171. *)
Lemma laws (R : realFieldType) (V : lmodType R) (A : set V) :
  is_convex_hull A (@value R V A).
Proof. exact: projT2 (cid (@convex_hull_exists R V A)). Qed.
End ConvexHull.
