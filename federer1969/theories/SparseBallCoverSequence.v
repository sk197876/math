(** Federer (1969), 2.9.18(1), p. 163: the finite off-target covers and
    recursively separated radius sequence. The specification records the
    printed laws before selecting a witness. Natural index n denotes printed
    positive index n+1. General topology supplies the finite-subcover
    background. The measure-formula erratum issue is treated separately in
    WeightedHitMeasure.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SparseBallCoverSequenceUP SparseBallCoverSequenceSealed NowhereDenseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [sparse_ball_cover_radii]: public radii for
    Federer 2.9.18(1), p. 163, accessed solely
    through the sealed sequence interface. *)
Definition sparse_ball_cover_radii (R : realType) (X : metricType R) (T : set X)
    (hc : compact T) (hnd : is_nowhere_dense T) (hn : T !=set0) :=
  @SparseCoverWitness.radii R X T hc hnd hn.

(** Source for [sparse_ball_cover_centers]: public finite
    centers for Federer 2.9.18(1), p. 163,
    accessed through the same sealed interface as the radii. *)
Definition sparse_ball_cover_centers (R : realType) (X : metricType R) (T : set X)
    (hc : compact T) (hnd : is_nowhere_dense T) (hn : T !=set0) :=
  @SparseCoverWitness.centers R X T hc hnd hn.

(** Source for [sparse_ball_cover_sequence_laws]: public
    specification of the chosen sequence in Federer 2.9.18(1),
    p. 163. Later proofs use these laws without
    computing through the recursive construction or witness choice. *)
Lemma sparse_ball_cover_sequence_laws (R : realType) (X : metricType R) (T : set X)
    (hc : compact T) (hnd : is_nowhere_dense T) (hn : T !=set0) :
  is_sparse_ball_cover_sequence T (@sparse_ball_cover_radii R X T hc hnd hn)
    (@sparse_ball_cover_centers R X T hc hnd hn).
Proof. exact: SparseCoverWitness.laws. Qed.
