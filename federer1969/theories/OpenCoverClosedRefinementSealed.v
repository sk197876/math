(** Federer (1969), 2.2.16, pp. 71–72: opaque separated closed refinement of
    an open family. The well-order witness is private. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import OpenCoverClosedRefinementUP OpenCoverClosedRefinementConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type OpenCoverClosedRefinementSignature.
(** Source for [value]: abstract C_n(V) family of
    Federer 2.2.16, pp. 71–72. *)
Parameter value : forall (R : realType) (X : metricType R) (J : choiceType)
  (D : set J) (U : J -> set X),
  (forall j, D j -> open (U j)) -> nat -> J -> set X.
(** Source for [laws]: closedness, inclusion, covering
    and separation of C_n(V), Federer 2.2.16, pp. 71–72. *)
Parameter laws : forall (R : realType) (X : metricType R) (J : choiceType)
  (D : set J) (U : J -> set X) (ho : forall j, D j -> open (U j)),
  is_separated_closed_open_refinement D U (@value R X J D U ho).
End OpenCoverClosedRefinementSignature.
Module OpenCoverClosedRefinement : OpenCoverClosedRefinementSignature.
(** Source for [value]: private witness selection for
    the C_n(V) refinement of Federer 2.2.16, pp. 71–72. *)
Definition value (R : realType) (X : metricType R) (J : choiceType)
  (D : set J) (U : J -> set X) (ho : forall j, D j -> open (U j)) :=
  projT1 (cid (@separated_closed_open_refinement_exists R X J D U ho)).
(** Source for [laws]: the selected refinement satisfies
    its abstract laws, Federer 2.2.16, pp. 71–72. *)
Lemma laws (R : realType) (X : metricType R) (J : choiceType)
  (D : set J) (U : J -> set X) (ho : forall j, D j -> open (U j)) :
  is_separated_closed_open_refinement D U (@value R X J D U ho).
Proof. exact: projT2 (cid (@separated_closed_open_refinement_exists R X J D U ho)). Qed.
End OpenCoverClosedRefinement.
