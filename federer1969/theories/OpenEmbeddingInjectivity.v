(** Federer (1969), 2.2.9, p. 65: the branch map is one-to-one. We use the
    first different coordinate and the abstract disjoint-sibling-open-set
    law. Source context and encoding: OpenEmbeddingTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceTreePrefixes SequenceFirstDifference
  OpenEmbeddingTreeUP OpenEmbeddingMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [open_embedding_map_injective]: Federer 2.2.9, p. 65,
    injectivity of g: at the first different coordinate, the two branch
    points belong to disjoint sibling open sets. *)
Lemma open_embedding_map_injective (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U)
    (g : positive_sequence_space R -> T) (hg : is_open_embedding_map U g) :
  injective g.
Proof.
move=> m n he; case: (eqVneq m n)=> [//|hmn].
exfalso; have [k [hk hp]] := positive_sequence_first_difference hmn.
have hprefix := sequence_tree_prefix_agreement hp.
have hm := @open_embedding_map_in_open_branch R T U hU g hg m k.+1.
have hn := @open_embedding_map_in_open_branch R T U hU g hg n k.+1.
change (U (positive_sequence_coordinates m k :: sequence_tree_prefix m k) (g m)) in hm.
change (U (positive_sequence_coordinates n k :: sequence_tree_prefix n k) (g n)) in hn.
rewrite -hprefix -he in hn.
have hneq : positive_sequence_coordinates m k <> positive_sequence_coordinates n k.
  move=> h; by move: hk; rewrite h eqxx.
have hd := @open_embedding_tree_siblings R T U hU (sequence_tree_prefix m k)
  (positive_sequence_coordinates m k) (positive_sequence_coordinates n k) hneq.
have hh : (U (positive_sequence_coordinates m k :: sequence_tree_prefix m k) `&`
    U (positive_sequence_coordinates n k :: sequence_tree_prefix m k)) (g m) by split.
by rewrite hd in hh.
Qed.
