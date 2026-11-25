(** Federer (1969), 2.2.9, p. 65: the branch map is a homeomorphism onto
    Gamma. We use the equivalent finite-prefix neighborhood base: a union of
    corresponding open branch sets represents each image open set. Source
    editions and encoding: OpenEmbeddingTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceProductTopology SequenceTreePrefixes
  OpenEmbeddingTreeUP OpenEmbeddingMapUP OpenEmbeddingBorelImage OpenEmbeddingImageEquality
  OpenEmbeddingPrefixCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [open_embedding_map_open]: Federer 2.2.9, p. 65, supporting
    inverse continuity of the homeomorphism: the image of every open subset
    of the sequence space is open relative to Gamma. Disjoint level open
    sets recover the input prefix of every point in an image branch
    neighborhood. *)
Theorem open_embedding_map_open (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U)
    (g : positive_sequence_space R -> T) (hg : is_open_embedding_map U g)
    (O : set (positive_sequence_space R)) : open O -> exists V : set T,
  open V /\ g @` O = open_embedding_image U `&` V.
Proof.
move=> ho.
pose V := \bigcup_(n in O) \bigcup_(k in [set k | positive_sequence_prefix n k `<=` O])
  U (sequence_tree_prefix n k).
have hV : open V.
  apply: bigcup_open=> n _; apply: bigcup_open=> k _.
  exact: (@open_embedding_tree_open R T U hU (sequence_tree_prefix n k)).
have himg := @open_embedding_map_image R T U hU g hg.
exists V; split=> //; apply/seteqP; split.
- move=> x [n hn <-]; split.
  + rewrite -himg; by exists n.
  + have hnb : nbhs n O by rewrite openE in ho; exact: ho n hn.
    have [k hk] := proj1 (positive_sequence_product_neighborhoods n O) hnb.
    exists n=> //; exists k=> //.
    exact: (@open_embedding_map_in_open_branch R T U hU g hg n k).
- move=> x [hxGamma [n hn [k hk hxn]]].
  rewrite -himg in hxGamma; have [m _ hm] := hxGamma.
  have hxm : U (sequence_tree_prefix m k) x.
    rewrite -hm; exact: (@open_embedding_map_in_open_branch R T U hU g hg m k).
  have he : sequence_tree_prefix n k = sequence_tree_prefix m k.
    case: (eqVneq (sequence_tree_prefix n k) (sequence_tree_prefix m k))=> h; first exact h.
    exfalso; have hneq : sequence_tree_prefix n k <> sequence_tree_prefix m k.
      move=> heq; by move: h; rewrite heq eqxx.
    have hsize : size (sequence_tree_prefix n k) = size (sequence_tree_prefix m k).
      by rewrite !sequence_tree_prefix_size.
    have hd := @open_embedding_tree_level_disjoint R T U hU _ _ hsize hneq.
    have hh : (U (sequence_tree_prefix n k) `&`
        U (sequence_tree_prefix m k)) x by split.
    by rewrite hd in hh.
  exists m=> //; apply: hk.
  exact: sequence_tree_prefix_coordinates he.
Qed.
