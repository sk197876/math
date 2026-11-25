(** Opaque maximal-chord frame for Federer (1969),
    2.10.38, printed pp. 198–199. Expose the data
    and proved intrinsic laws; conceal the implementation
    and all auxiliary finite-prefix choices. Source
    editions: GreedyChordFrameUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric
  GreedyChordFrameUP GreedyChordFrameConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type GREEDY_CHORD_FRAME.
(** Source for [value]: abstract chosen maximal-chord
    frame for 2.10.38, pp. 198–199. *)
Parameter value : forall (R : realType) n
  (S : set (inner_metric_space (@euclidean_inner_productP R n))),
  compact S -> S !=set0 -> greedy_chord_frame_data R n.
(** Source for [laws]: abstract maximality, recursion
    and orthogonality laws supporting 2.10.38, p. 199. *)
Parameter laws : forall (R : realType) n
  (S : set (inner_metric_space (@euclidean_inner_productP R n)))
  (hS : compact S) (hne : S !=set0),
  is_greedy_chord_frame S (@value R n S hS hne).
End GREEDY_CHORD_FRAME.

Module GreedyChordFrame : GREEDY_CHORD_FRAME.
(** Source for [value]: privately proved existence
    witness for 2.10.38, pp. 198–199,
    hidden by opaque module ascription. *)
Definition value (R : realType) n
  (S : set (inner_metric_space (@euclidean_inner_productP R n)))
  (hS : compact S) (hne : S !=set0) :=
  projT1 (cid (@greedy_chord_frame_exists R n S hS hne)).
(** Source for [laws]: proved intrinsic laws of
    the sealed frame supporting 2.10.38, p. 199. *)
Lemma laws (R : realType) n
  (S : set (inner_metric_space (@euclidean_inner_productP R n)))
  (hS : compact S) (hne : S !=set0) :
  is_greedy_chord_frame S (@value R n S hS hne).
Proof. exact: (projT2 (cid (@greedy_chord_frame_exists R n S hS hne))). Qed.
End GreedyChordFrame.
