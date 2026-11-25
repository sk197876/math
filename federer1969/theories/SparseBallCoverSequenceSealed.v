(** Federer (1969), 2.9.18(1), p. 163: the finite off-target covers and
    recursively separated radius sequence. The specification records the
    printed laws before selecting a witness. Natural index n denotes printed
    positive index n+1. General topology supplies the finite-subcover
    background. The measure-formula erratum issue is treated separately in
    WeightedHitMeasure.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SparseBallCoverSequenceUP SparseBallCoverSequenceConstruction NowhereDenseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type SparseCoverWitnessSignature.
(** Source for [radii]: abstract positive radii c_j satisfying
    the displayed laws in Federer 2.9.18(1), p. 163.
    The particular recursive choice remains sealed. *)
Parameter radii : forall (R : realType) (X : metricType R) (T : set X),
  compact T -> is_nowhere_dense T -> T !=set0 -> nat -> R.
(** Source for [centers]: abstract finite center sets S_j
    in Federer 2.9.18(1), p. 163, for the
    same sealed choice of radii. *)
Parameter centers : forall (R : realType) (X : metricType R) (T : set X),
  compact T -> is_nowhere_dense T -> T !=set0 -> nat -> set X.
(** Source for [laws]: exposed sequence laws of Federer
    2.9.18(1), p. 163, rather than the
    witness's recursion equations. *)
Parameter laws : forall (R : realType) (X : metricType R) (T : set X)
  (hc : compact T) (hnd : is_nowhere_dense T) (hn : T !=set0),
  is_sparse_ball_cover_sequence T (@radii R X T hc hnd hn) (@centers R X T hc hnd hn).
End SparseCoverWitnessSignature.

Module SparseCoverWitness : SparseCoverWitnessSignature.
Section Selection.
(** Source for [choice]: private choice of the proved sequence
    witness in Federer 2.9.18(1), p. 163.
    This local binding is absent from the sealed signature. *)
Let choice (R : realType) (X : metricType R) (T : set X)
    (hc : compact T) (hnd : is_nowhere_dense T) (hn : T !=set0) :=
  cid (@sparse_ball_cover_sequence_exists R X T hc hnd hn).

(** Source for [radii]: private selection of c_j for
    Federer 2.9.18(1), p. 163. Only its
    abstract laws are exposed by opaque module ascription. *)
Definition radii (R : realType) (X : metricType R) (T : set X)
    (hc : compact T) (hnd : is_nowhere_dense T) (hn : T !=set0) :=
  proj1_sig (@choice R X T hc hnd hn).

(** Source for [centers]: private selection of the center
    sets in Federer 2.9.18(1), p. 163,
    from the same witness as the selected radii. *)
Definition centers (R : realType) (X : metricType R) (T : set X)
    (hc : compact T) (hnd : is_nowhere_dense T) (hn : T !=set0) :=
  proj1_sig (cid (proj2_sig (@choice R X T hc hnd hn))).

(** Source for [laws]: the selected witness satisfies the
    abstract sequence specification for Federer 2.9.18(1),
    p. 163. *)
Lemma laws (R : realType) (X : metricType R) (T : set X)
    (hc : compact T) (hnd : is_nowhere_dense T) (hn : T !=set0) :
  is_sparse_ball_cover_sequence T (@radii R X T hc hnd hn) (@centers R X T hc hnd hn).
Proof. exact: proj2_sig (cid (proj2_sig (@choice R X T hc hnd hn))). Qed.
End Selection.
End SparseCoverWitness.
