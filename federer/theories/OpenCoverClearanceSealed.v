(** Opaque cover-clearance supremum from
    Federer (1969), 3.1.13, p. 224.
    Only its order laws are exported. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import OpenCoverClearanceUP OpenCoverClearanceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type OpenCoverClearanceSignature.
(** Source for [value]: the supremum
    of capped complement distances in
    Federer 3.1.13, p. 224. *)
Parameter value : forall (R : realType) (X : metricType R), set (set X)->X->R.
(** Source for [laws]: the exact
    supremum laws, Federer 3.1.13, p. 224. *)
Parameter laws : forall (R : realType) (X : metricType R) (Phi : set (set X)),
  is_open_cover_clearance Phi (@value R X Phi).
End OpenCoverClearanceSignature.

Module OpenCoverClearance : OpenCoverClearanceSignature.
(** Source for [value]: a proved
    supremum witness, Federer 3.1.13, p. 224. *)
Definition value (R : realType) (X : metricType R) (Phi : set (set X)) :=
  sval (constructive_indefinite_description (@open_cover_clearance_exists R X Phi)).
(** Source for [laws]: the selected
    supremum satisfies the abstract laws,
    Federer 3.1.13, p. 224. *)
Lemma laws (R : realType) (X : metricType R) (Phi : set (set X)) :
  is_open_cover_clearance Phi (@value R X Phi).
Proof. exact: (svalP (constructive_indefinite_description (@open_cover_clearance_exists R X Phi))). Qed.
End OpenCoverClearance.
