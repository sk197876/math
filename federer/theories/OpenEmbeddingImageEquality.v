(** Federer (1969), 2.2.9, p. 65: the branch map's image is exactly the
    displayed Borel set Gamma. At each level a point of Gamma lies in a
    unique branch set; nesting and disjointness make those words consistent.
    Source context and encoding: OpenEmbeddingTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceTreePrefixes
  OpenEmbeddingTreeUP OpenEmbeddingBranches OpenEmbeddingMapUP OpenEmbeddingBorelImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [open_embedding_map_image_subset]: Federer 2.2.9, p. 65,
    inclusion img g in Gamma: the next child closure puts each branch point
    in the current open set. *)
Lemma open_embedding_map_image_subset (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U)
    (g : positive_sequence_space R -> T) (hg : is_open_embedding_map U g) :
  g @` setT `<=` open_embedding_image U.
Proof.
move=> x [n _ <-] k _; exists (sequence_tree_prefix n k.+1).
- exact: sequence_tree_prefix_size.
- exact: (@open_embedding_map_in_open_branch R T U hU g hg n k.+1).
Qed.

(** Source for [open_embedding_image_compatible_words]: supporting
    consistency argument in Federer 2.2.9, p. 65: a point of Gamma has a
    word at every level, and each next word extends the previous one. *)
Lemma open_embedding_image_compatible_words (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U) x :
  open_embedding_image U x -> exists w : nat -> seq nat,
    (forall k, size (w k) = k /\ U (w k) x) /\
    w 0 = [::] /\ forall k, w k.+1 = head 0%N (w k.+1) :: w k.
Proof.
move=> hx.
have hw k : exists s, size s = k /\ U s x.
  case: k=> [|k].
  - exists [::]; split=> //; by rewrite (open_embedding_tree_root hU).
  - have [s hs hxs] := hx k Logic.I; exists s; by split.
pose w k := projT1 (cid (hw k)).
have hwlaw k : size (w k) = k /\ U (w k) x := projT2 (cid (hw k)).
exists w; split=> //; split.
- apply/eqP; by rewrite -size_eq0 (hwlaw 0%N).1.
- move=> k; have [hsize hmem] := hwlaw k.+1.
  case he : (w k.+1)=> [|j s]; rewrite he /= in hsize hmem; first discriminate.
  have hs : size s = k by case: hsize.
  have hparent : U s x.
    apply: (@open_embedding_tree_child_inside R T U hU s j x).
    exact: subset_closure hmem.
  have hsw : s = w k.
    case: (eqVneq s (w k))=> h; first exact h.
    exfalso; have hneq : s <> w k by move=> hh; move: h; rewrite hh eqxx.
    have hd := @open_embedding_tree_level_disjoint R T U hU s (w k)
      (eq_trans hs (esym (hwlaw k).1)) hneq.
    have hh : (U s `&` U (w k)) x by split=> //; exact: (hwlaw k).2.
    by rewrite hd in hh.
  by rewrite /= hsw.
Qed.

(** Source for [open_embedding_map_image]: Federer 2.2.9, p. 65, equality of
    img g with Gamma. Realise the compatible coordinate words of a Gamma
    point and use uniqueness of its branch point. *)
Theorem open_embedding_map_image (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U)
    (g : positive_sequence_space R -> T) (hg : is_open_embedding_map U g) :
  g @` setT = open_embedding_image U.
Proof.
apply/seteqP; split; first exact: (@open_embedding_map_image_subset R T U hU g hg).
move=> x hx; have [w [hw [hw0 hstep]]] := open_embedding_image_compatible_words hU hx.
pose a k := head 0%N (w k.+1).
pose n := @positive_sequence_from_coordinates R a.
have hp k : sequence_tree_prefix n k = w k.
  elim: k=> [|k IH]; first by rewrite /= hw0.
  by rewrite /= /n positive_sequence_coordinatesK /a IH -hstep.
exists n; first exact Logic.I.
apply: (@open_embedding_branch_point_unique R T U hU n (g n) x).
- exact: hg.
- move=> k; rewrite hp; exact: subset_closure (hw k).2.
Qed.
