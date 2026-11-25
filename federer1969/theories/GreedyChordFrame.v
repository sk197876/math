(** Public maximal-chord frame supporting Federer (1969), 2.10.38, printed
    pp. 198–199. Only the opaque data and proved intrinsic specification are
    exposed; downstream theorems use these laws. Source context:
    GreedyChordFrameUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric GreedyChordFrameUP GreedyChordFrameSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_greedy_chord_frame]: abstract
    chosen axes and endpoint chords in the induction
    of 2.10.38, p. 199. *)
Definition compact_greedy_chord_frame (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (hS : compact S) (hne : S !=set0) := @GreedyChordFrame.value R n S hS hne.

(** Source for [compact_greedy_chord_frame_specification]: proved
    abstract frame laws supporting 2.10.38, pp. 198–199.
    Sorted widths and exterior equalities are derived
    separately rather than included as assumptions. *)
Theorem compact_greedy_chord_frame_specification (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (hS : compact S) (hne : S !=set0) :
  is_greedy_chord_frame S (@compact_greedy_chord_frame R n S hS hne).
Proof. exact: GreedyChordFrame.laws. Qed.
