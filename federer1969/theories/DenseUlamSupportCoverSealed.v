(** Federer (1969), 2.2.16, p. 71: opaque Ulam-indexed open null cover of
    the support complement. Clients do not depend on the dense-ball
    construction. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureSupport UlamCardinalUP DenseUlamSupportCoverUP
  DenseUlamSupportCoverConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type DenseUlamSupportCoverSignature.
(** Source for [value]: abstract open null cover H
    of Federer 2.2.16, p. 71. *)
Parameter value : forall (R : realType) (X : metricType R) (mu : set X -> \bar R)
  (hm : is_measure mu) (D : set X), dense D -> is_ulam_set R D ->
  set (X * nat) * (X * nat -> set X).
(** Source for [laws]: Ulam-index, open-null and union
    laws of H in Federer 2.2.16, p. 71. *)
Parameter laws : forall (R : realType) (X : metricType R) (mu : set X -> \bar R)
  (hm : is_measure mu) (D : set X) (hd : dense D) (hu : is_ulam_set R D),
  is_ulam_open_null_cover mu (~` measure_support mu)
    (@value R X mu hm D hd hu).1 (@value R X mu hm D hd hu).2.
End DenseUlamSupportCoverSignature.
Module DenseUlamSupportCover : DenseUlamSupportCoverSignature.
(** Source for [value]: private witness selection for
    H in Federer 2.2.16, p. 71. *)
Definition value (R : realType) (X : metricType R) (mu : set X -> \bar R)
  (hm : is_measure mu) (D : set X) (hd : dense D) (hu : is_ulam_set R D) :=
  let w := cid (@dense_ulam_support_cover_exists R X mu hm D hd hu) in
  (projT1 w, projT1 (cid (projT2 w))).
(** Source for [laws]: the selected cover satisfies
    the laws used in Federer 2.2.16, p. 71. *)
Lemma laws (R : realType) (X : metricType R) (mu : set X -> \bar R)
  (hm : is_measure mu) (D : set X) (hd : dense D) (hu : is_ulam_set R D) :
  is_ulam_open_null_cover mu (~` measure_support mu)
    (@value R X mu hm D hd hu).1 (@value R X mu hm D hd hu).2.
Proof. exact: projT2 (cid (projT2 (cid (@dense_ulam_support_cover_exists R X mu hm D hd hu)))). Qed.
End DenseUlamSupportCover.
