(** Federer (1969), 2.2.9, p. 65: construct the real interval tree with
    countable loss. The first level is the sealed whole-line grid;
    subsequent levels use only the sealed bounded-interval refinement.
    Stored words are reversed, as in the general tree. Source context:
    NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground RealOpenIntervals
  ClosedCoverTreeUP OpenEmbeddingTreeUP OpenEmbeddingCountableComplement
  IntervalRefinementUP IntervalRefinementSealed RootIntervalsSealed RealIntervalTreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Construction.
Variable R : realType.

(** Source for [real_interval_piece]: private nonempty interval
    objects supporting the recursion in Federer 2.2.9, p. 65. *)
Definition real_interval_piece := { ab : R * R | ab.1 < ab.2 }.

(** Source for [real_interval_piece_set]: supporting interpretation
    of an interval object as the open set U(s) in Federer
    2.2.9, p. 65. *)
Definition real_interval_piece_set (C : real_interval_piece) :=
  real_open_interval (proj1_sig C).1 (proj1_sig C).2.

(** Source for [real_interval_first_family]: supporting first
    interval level for Federer 2.2.9, p. 65, with the
    printed strict scale bound 2^(-1-2). *)
Definition real_interval_first_family := @RootIntervals.value R
  (@closed_cover_tree_scale R 1) (@closed_cover_tree_scale_positive R 1).

(** Source for [real_interval_first_laws]: supporting abstract
    laws of the first interval level in Federer 2.2.9, p. 65. *)
Lemma real_interval_first_laws : is_real_interval_refinement
    (@setT (real_line_metric R)) (@closed_cover_tree_scale R 1) real_interval_first_family.
Proof. exact: RootIntervals.laws. Qed.

(** Source for [real_interval_first_piece]: supporting first-level
    interval object for the recursion in Federer 2.2.9, p. 65. *)
Definition real_interval_first_piece n : real_interval_piece :=
  exist _ (real_interval_first_family n)
    (@real_interval_refinement_ordered R _ _ _ real_interval_first_laws n).

(** Source for [real_interval_child_family]: supporting recursive
    interval refinement in Federer 2.2.9, p. 65, using
    only the laws of the sealed child family. *)
Definition real_interval_child_family (C : real_interval_piece) k :=
  @IntervalRefinement.value R (proj1_sig C).1 (proj1_sig C).2
    (@closed_cover_tree_scale R k.+1) (proj2_sig C)
    (@closed_cover_tree_scale_positive R k.+1).

(** Source for [real_interval_child_laws]: supporting refinement
    laws of a bounded interval at the next level in Federer
    2.2.9, p. 65. *)
Lemma real_interval_child_laws (C : real_interval_piece) k :
  is_real_interval_refinement (real_interval_piece_set C)
    (@closed_cover_tree_scale R k.+1) (real_interval_child_family C k).
Proof. exact: IntervalRefinement.laws. Qed.

(** Source for [real_interval_child_piece]: supporting child
    object in the interval-tree recursion, Federer 2.2.9, p. 65. *)
Definition real_interval_child_piece (C : real_interval_piece) k j : real_interval_piece :=
  exist _ (real_interval_child_family C k j)
    (@real_interval_refinement_ordered R _ _ _ (real_interval_child_laws C k) j).

(** Source for [real_interval_tree_piece]: supporting recursive
    witness for Federer 2.2.9, p. 65. The unused empty-word
    interval is a default only; the actual root open set is R. *)
Fixpoint real_interval_tree_piece (s : seq nat) : real_interval_piece :=
  if s is j::t then
    if t is [::] then real_interval_first_piece j
    else real_interval_child_piece (real_interval_tree_piece t) (size t) j
  else real_interval_first_piece 0%N.

(** Source for [real_interval_tree_witness]: private open-tree
    witness for the real-line construction in Federer 2.2.9,
    p. 65: the root is R, and every other node is the
    interval supplied by the recursive choices. *)
Definition real_interval_tree_witness (s : seq nat) : set (real_line_metric R) :=
  if s is [::] then setT else real_interval_piece_set (real_interval_tree_piece s).

(** Source for [real_interval_embedding_tree_exists]: the interval-tree
    existence needed for the special real-line assertion in Federer 2.2.9,
    p. 65. *)
Theorem real_interval_embedding_tree_exists : exists U : seq nat -> set (real_line_metric R),
  is_real_interval_embedding_tree U.
Proof.
exists real_interval_tree_witness; constructor.
- constructor.
  + by [].
  + move=> [|j s]; first exact: openT.
    exact: real_open_interval_open.
  + move=> [|j s].
    * by exists (0 : R).
    * apply: real_open_interval_nonempty; exact: proj2_sig (real_interval_tree_piece (j::s)).
  + move=> [|i s] j.
    * exact: (@real_interval_refinement_inside R _ _ _ real_interval_first_laws j).
    * exact: (@real_interval_refinement_inside R _ _ _
        (real_interval_child_laws (real_interval_tree_piece (i::s)) (size (i::s))) j).
  + move=> [|k s] i j hij.
    * exact: (@real_interval_refinement_disjoint R _ _ _ real_interval_first_laws i j hij).
    * exact: (@real_interval_refinement_disjoint R _ _ _
        (real_interval_child_laws (real_interval_tree_piece (k::s)) (size (k::s))) i j hij).
  + move=> [|j [|i s]] // _ x y hx hy.
    * apply: le_lt_trans (real_open_interval_diameter_bound hx hy) _.
      exact: (@real_interval_refinement_length R _ _ _ real_interval_first_laws j).
    * apply: le_lt_trans (real_open_interval_diameter_bound hx hy) _.
      exact: (@real_interval_refinement_length R _ _ _
        (real_interval_child_laws (real_interval_tree_piece (i::s)) (size (i::s))) j).
- move=> [|j s] // _.
  exists (proj1_sig (real_interval_tree_piece (j::s))).1,
    (proj1_sig (real_interval_tree_piece (j::s))).2.
  split=> //; exact: proj2_sig (real_interval_tree_piece (j::s)).
- move=> [|i s].
  + exact: (@real_interval_refinement_countable_loss R _ _ _ real_interval_first_laws).
  + exact: (@real_interval_refinement_countable_loss R _ _ _
      (real_interval_child_laws (real_interval_tree_piece (i::s)) (size (i::s)))).
Qed.
End Construction.
