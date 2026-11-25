(** Federer (1969), 2.10.38, printed pp. 198–199: supporting degenerate
    cases of the enclosing-box frame. A singleton has zero side lengths, and
    one zero side in an initial product makes its endpoint exterior norm
    zero. These consequences use the public laws alone. Source context and
    norm background: GreedyChordFrameUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerMetric InnerNorm GreedyChordFrameUP GreedyChordFrameLaws
  GreedyChordExteriorProducts FinitePrefixes ExteriorDiameterUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [greedy_chord_singleton_width]: supporting
    zero-diameter case in the proof of 2.10.38,
    p. 199. Every chosen width of a singleton
    is zero, without unfolding the chosen frame. *)
Lemma greedy_chord_singleton_width (R : realType) n
    (p : inner_metric_space (@euclidean_inner_productP R n))
    (D : greedy_chord_frame_data R n) :
  is_greedy_chord_frame [set p] D -> forall i, greedy_chord_length D i=0.
Proof.
move=> hD i.
have [ha hb] := greedy_chord_endpoints_law hD i.
have hh := greedy_chord_selected_norm hD i.
have ha' : greedy_chord_first D i=p := ha.
have hb' : greedy_chord_second D i=p := hb.
by rewrite ha' hb' subrr linear0 inner_norm0 in hh.
Qed.

(** Source for [greedy_chord_prefix_zero_width]: supporting
    degenerate initial-product case of 2.10.38,
    pp. 198–199. No nonzero-width cancellation is
    used in the stated exterior norm equality. *)
Lemma greedy_chord_prefix_zero_width (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (D : greedy_chord_frame_data R n) (hD : is_greedy_chord_frame S D)
    k (hk : (k<=n)%N) (i : 'I_k) :
  family_prefix hk (greedy_chord_length D) i=0 ->
  exterior_difference_norm (family_prefix hk (greedy_chord_first D))
    (family_prefix hk (greedy_chord_second D))=0.
Proof.
by move=> hi; rewrite (greedy_chord_prefix_norm hD hk) (bigD1 i) //= hi mul0r.
Qed.
