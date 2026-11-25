(** Federer (1969), 2.2.12, p. 69: the bounded-coordinate set K is compact.
    Natural coordinate codes represent positive integers minus one; a bound
    b(i) here means the positive bound b(i)+1 in the book. The proof uses
    the product of finite discrete intervals and the local coordinate
    realisation laws. General-topology Tychonoff compactness is background,
    already supplied by the topology import; no external measure theorem is
    used. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceCoordinateContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Import ArrowAsProduct.

(** Source for [sequence_coordinate_box]: direct bounded-coordinate
    set K in Federer 2.2.12, p. 69. All coordinates are
    bounded, with the positive-index convention stated in the header. *)
Definition sequence_coordinate_box (R : realType) (b : nat -> nat) :
    set (positive_sequence_space R) :=
  [set n | forall i, (positive_sequence_coordinates n i <= b i)%N].

(** Source for [sequence_coordinate_box_nonempty]: supporting boundary
    case for K in Federer 2.2.12, p. 69: the constant
    positive-one sequence belongs to every bounded-coordinate box,
    including a box whose every natural code bound is zero. *)
Lemma sequence_coordinate_box_nonempty (R : realType) (b : nat -> nat) :
  @sequence_coordinate_box R b (positive_sequence_default R).
Proof. by move=> i; rewrite /positive_sequence_default positive_sequence_coordinatesK leq0n. Qed.

(** Source for [sequence_realisation_product_continuous]: supporting
    product-topology map for the compactness assertion in Federer
    2.2.12, p. 69. Realising a sequence of discrete natural
    codes is continuous by the local coordinate criterion for 2.2.6. *)
Lemma sequence_realisation_product_continuous (R : realType) :
  continuous (@positive_sequence_from_coordinates R).
Proof.
apply/(proj2 (positive_sequence_coordinate_continuous _))=> f i.
have hn : nbhs (f i) [set j : nat | j = f i].
  rewrite nbhs_principalE; apply/principal_filterP; by [].
have hh : nbhs f [set g : nat -> nat | g i = f i].
  exact: (@proj_continuous _ _ i f _ hn).
apply: filterS hh=> g hg; by rewrite /= !positive_sequence_coordinatesK.
Qed.

(** Source for [sequence_coordinate_box_compact]: direct compactness
    assertion for K in Federer 2.2.12, p. 69. The box
    is the continuous image of the compact product of finite
    discrete coordinate intervals. No compactness assumption on
    the ambient space X of the Suslin set is introduced. *)
Theorem sequence_coordinate_box_compact (R : realType) (b : nat -> nat) :
  compact (@sequence_coordinate_box R b).
Proof.
pose A i : set nat := [set j | (j <= b i)%N].
have hA i : compact (A i).
  apply: finite_compact.
  have he : A i = [set` iota 0 (b i).+1].
    apply/seteqP; split=> j hj.
    - change (j \in iota 0 (b i).+1).
      by rewrite mem_iota add0n leq0n /= ltnS.
    - change (is_true (j \in iota 0 (b i).+1)) in hj.
      by move: hj; rewrite mem_iota add0n leq0n /= ltnS.
  rewrite he; exact: finite_seq.
pose P := [set f : nat -> nat | forall i, A i (f i)].
have hP : compact P := @tychonoff _ _ A hA.
have he : (@positive_sequence_from_coordinates R) @` P = sequence_coordinate_box b.
  apply/seteqP; split.
  - move=> n [f hf <-] i; rewrite positive_sequence_coordinatesK; exact: hf i.
  - move=> n hn; exists (positive_sequence_coordinates n)=> //; exact: positive_sequence_realisationK.
rewrite -he; apply: continuous_compact hP.
exact (continuous_subspaceT (@sequence_realisation_product_continuous R)).
Qed.
