(** Federer (1969), 2.2.9, p. 65: continuity of the parametrisation follows
    from its local distance bound. This supporting consequence is used in
    2.2.10 to parametrise Suslin sets. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import SequenceSpace ClosedCoverTreeUP OpenEmbeddingTreeUP OpenEmbeddingMapUP
  OpenEmbeddingMapLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_embedding_map_continuous]: supporting
    consequence of Federer 2.2.9, p. 65: g is continuous.
    Use a ball radius below both the output tolerance and the
    one-quarter threshold for its local distance bound. *)
Lemma open_embedding_map_continuous (R : realType) (T : metricType R)
    (E : seq nat -> set T) (hE : is_open_embedding_tree E)
    (g : positive_sequence_space R -> T) (hg : is_open_embedding_map E g) :
  continuous g.
Proof.
move=> n U hU.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (g n) U) hU.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP n (g @^-1` U))).
exists (Order.min e (@closed_cover_tree_scale R 0)).
- by rewrite /= lt_min he closed_cover_tree_scale_positive.
- move=> m hm; apply: hball.
  have hde : mdist n m < e.
    apply: lt_le_trans hm _; by rewrite ge_min lexx.
  have hd : mdist n m < @closed_cover_tree_scale R 0.
    apply: lt_le_trans hm _; by rewrite ge_min lexx orbT.
  exact: le_lt_trans (@open_embedding_map_small_distance R T E hE g hg n m hd) hde.
Qed.
