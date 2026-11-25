(** Private existence proof for Federer (1969), 2.10.38, printed pp.
    198–199. The finite greedy projected-chord witness is converted to the
    public intrinsic frame laws and will be hidden by opaque module
    ascription. No downstream result imports this implementation. Source
    context: GreedyChordFrameUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  GreedyChordFrameUP GreedyChordPrefixConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [greedy_chord_frame_exists]: existence proof
    of the maximal projected-chord frame in 2.10.38,
    pp. 198–199. Compactness and nonemptiness are
    the only source hypotheses; zero-dimensional and
    zero-diameter cases are included. *)
Theorem greedy_chord_frame_exists (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact S -> S !=set0 -> exists D : greedy_chord_frame_data R n,
    is_greedy_chord_frame S D.
Proof.
move=> hS hne.
have [e [a [b [c [he [hab [hsel hmax]]]]]]] :=
  private_greedy_chord_prefix_exists hS hne (leqnn n).
pose D : greedy_chord_frame_data R n :=
  {| greedy_chord_axis := e; greedy_chord_length := c;
     greedy_chord_first := a; greedy_chord_second := b;
     greedy_chord_residual := fun l=>GRing.Linear.clone _ _ _ _ (private_chord_residual e l) _ |}.
exists D; constructor=> //.
- exact: private_chord_residual_zero.
- exact: private_chord_residual_successor.
Qed.
