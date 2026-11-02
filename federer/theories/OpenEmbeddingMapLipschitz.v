(** Federer (1969), 2.2.9, p. 65: local Lipschitz regularity of g for the
    exact sequence metric. We select the first different coordinate instead
    of placing the input distance in a dyadic annulus; the same prefix and
    diameter bounds then give the same local constant one. Source context:
    OpenEmbeddingTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceSpaceUP ClosedCoverTreeUP
  SequenceTreePrefixes OpenEmbeddingTreeUP OpenEmbeddingMapUP SequenceFirstDifference
  ClosedCoverMapLipschitz LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_embedding_map_small_distance]: Federer 2.2.9, p. 65,
    supporting estimate for the construction: input distance less than one
    quarter bounds the output distance with constant one. Distinct sequences
    agree up to their first different coordinate; its half-weight bounds the
    input distance from below and the branch diameter above. *)
Lemma open_embedding_map_small_distance (R : realType) (T : metricType R)
    (E : seq nat -> set T) (hE : is_open_embedding_tree E)
    (g : positive_sequence_space R -> T) (hg : is_open_embedding_map E g) m n :
  mdist m n < @closed_cover_tree_scale R 0 -> mdist (g m) (g n) <= mdist m n.
Proof.
move=> hd; case: (eqVneq m n)=> [->|hmn]; first by rewrite !mdistxx.
have [k [hk hp]] := positive_sequence_first_difference hmn.
have hl := positive_sequence_different_coordinate_lower hk.
rewrite -closed_cover_scale_half_weight in hl.
case: k hk hp hl=> [|k] hk hp hl.
- by move: hd; rewrite ltNge hl.
- apply: le_trans _ hl.
  have he := sequence_tree_prefix_agreement hp.
  have hm := hg m k.+1; have hn := hg n k.+1; rewrite -he in hn.
  have hb := open_embedding_tree_diameter hE (s := sequence_tree_prefix m k.+1).
  rewrite sequence_tree_prefix_size in hb; apply: ltW; apply: hb=> //.
Qed.

(** Source for [open_embedding_map_locally_lipschitz]: supporting local
    Lipschitz consequence for g in Federer 2.2.9, p. 65. Balls of radius one
    eighth have diameter less than one quarter, so the preceding bound gives
    constant one on each such neighborhood. *)
Theorem open_embedding_map_locally_lipschitz (R : realType) (T : metricType R)
    (E : seq nat -> set T) (hE : is_open_embedding_tree E)
    (g : positive_sequence_space R -> T) (hg : is_open_embedding_map E g) :
  is_locally_metric_lipschitz setT g.
Proof.
move=> n _; pose r := @closed_cover_tree_scale R 0 / 2.
have hr : 0 < r by rewrite /r divr_gt0 ?closed_cover_tree_scale_positive ?ltr0n.
exists [set x | mdist n x < r]; split.
- have h := nbhsx_ballx n r hr; by rewrite ballEmdist in h.
- exists 1; split; first exact: ltr01.
  split; first exact: ler01.
  move=> x y [_ hx] [_ hy]; rewrite mul1r.
  apply: (@open_embedding_map_small_distance R T E hE g hg x y).
  apply: le_lt_trans (metric_triangle x n y) _; rewrite (metric_sym x n).
  have hh := ltrD hx hy; by rewrite /r -splitr in hh.
Qed.
