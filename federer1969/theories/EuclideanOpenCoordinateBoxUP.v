(** Federer (1969), 3.2.41, printed p. 277, first proof paragraph:
    F is the family of products of nonempty bounded open intervals.
    Specify an actual coordinate box by its endpoints and membership
    laws; constructions serve only to prove local existence. The
    Brunn--Minkowski root theorem separately requires positive dimension. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_euclidean_open_coordinate_box]: direct box family
    in Federer 3.2.41, p. 277. Every coordinate interval is proper,
    nonempty, bounded and open; its real endpoints remain explicit.
    In dimension zero the empty product is the original one-point space. *)
Definition is_euclidean_open_coordinate_box (R : realType) n
    (a b : R_n R n)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) : Prop :=
  (forall i, a i<b i) /\ forall x, A x <-> forall i, a i<x i<b i.

(** Source for [euclidean_open_coordinate_box_exists]: local
    existence of the box family members in Federer 3.2.41, p. 277.
    The coordinate product is a witness, not a global chosen box. *)
Lemma euclidean_open_coordinate_box_exists (R : realType) n (a b : R_n R n) :
  (forall i, a i<b i) -> exists A, is_euclidean_open_coordinate_box a b A.
Proof.
move=> hab; exists [set x : inner_metric_space (@euclidean_inner_productP R n) |
  forall i, a i<x i<b i]; by split.
Qed.
