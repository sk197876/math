(** Opaque enclosing-radius witness supporting Federer (1969), 2.10.31, pp.
    195–196. Expose only its independent nonnegativity, containment and
    least-bound specification. Source context: CompactEnclosingRadiusUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactSetDistanceProfile CompactEnclosingRadiusUP CompactEnclosingRadiusConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type COMPACT_ENCLOSING_RADIUS.
(** Source for [value]: supporting scalar radius
    used in 2.10.31, p. 195, specified
    independently of a maximizing-point construction. *)
Parameter value : forall (R : realType) (X : metricType R),
  X -> compact_metric_set X -> R.
(** Source for [laws]: supporting least containing-radius
    laws for 2.10.31, p. 195. *)
Parameter laws : forall (R : realType) (X : metricType R) (a : X) (C : compact_metric_set X),
  is_compact_enclosing_radius a C (@value R X a C).
End COMPACT_ENCLOSING_RADIUS.
Module CompactEnclosingRadius : COMPACT_ENCLOSING_RADIUS.
(** Source for [value]: proved radius witness
    supporting 2.10.31, p. 195, hidden
    by opaque module ascription. *)
Definition value (R : realType) (X : metricType R) (a : X) (C : compact_metric_set X) :=
  projT1 (cid (@compact_enclosing_radius_exists R X a C)).
(** Source for [laws]: proved supporting radius
    specification for 2.10.31, p. 195. *)
Lemma laws (R : realType) (X : metricType R) (a : X) (C : compact_metric_set X) :
  is_compact_enclosing_radius a C (@value R X a C).
Proof. exact: (projT2 (cid (@compact_enclosing_radius_exists R X a C))). Qed.
End CompactEnclosingRadius.
