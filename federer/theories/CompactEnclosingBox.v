(** Federer (1969), 2.10.38, printed pp. 198–199: every nonempty compact
    Euclidean set is contained in a rectangular box with decreasing side
    lengths whose every initial product is attained by an exterior product
    of endpoint differences in the set. The printed statement needs
    nonemptiness in positive dimension; EmptyCompactBoxCounterexample.v
    proves this local correction, distinct from Federer's erratum, which has
    no entry for pp. 198–199. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  FinitePrefixes ExteriorDiameterUP EuclideanBoxUP GreedyChordFrameUP GreedyChordFrame
  GreedyChordFrameLaws GreedyChordExteriorProducts GreedyChordEnclosingBox.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_enclosing_rectangular_box]: direct
    theorem 2.10.38, pp. 198–199, with the
    necessary nonempty-source qualification. The conclusion
    includes every initial length, strengthened to include
    the empty product and ambient dimension zero.
    Convexity, positive widths and nonempty interior are
    not assumed. The box is specified by its laws. *)
Theorem compact_enclosing_rectangular_box (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact S -> S !=set0 -> exists (a b e : 'I_n -> R_n R n)
    (c : 'I_n -> R) origin Q,
    (forall i, S (a i) /\ S (b i)) /\
    is_euclidean_rectangular_box origin e c Q /\ S `<=` Q /\
    (forall i j : 'I_n, (i<=j)%N -> c j<=c i) /\
    forall k (hk : (k<=n)%N),
      exterior_difference_norm (family_prefix hk a) (family_prefix hk b)=
        \prod_(i<k) family_prefix hk c i.
Proof.
move=> hS hne.
pose D := @compact_greedy_chord_frame R n S hS hne.
have hD := @compact_greedy_chord_frame_specification R n S hS hne.
have [origin [Q [hQ hSQ]]] := greedy_chord_enclosing_box hD.
exists (greedy_chord_first D),(greedy_chord_second D),(greedy_chord_axis D),
  (greedy_chord_length D),origin,Q.
split; first exact: greedy_chord_endpoints_law hD.
split=> //; split=> //; split.
- exact: greedy_chord_lengths_ordered hD.
- exact: greedy_chord_prefix_norm hD.
Qed.

(** Source for [federer_2_10_38]: numbered public alias
    of 2.10.38, pp. 198–199. The source's
    nonemptiness qualification is made explicit and
    degree zero is included by the supporting theorem. *)
Definition federer_2_10_38 := @compact_enclosing_rectangular_box.
