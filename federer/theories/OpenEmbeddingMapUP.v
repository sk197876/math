(** Federer (1969), 2.2.9, p. 65: g(n) is the unique point in the nested
    closures of U along n. We specify branch membership abstractly before
    selecting the map. Source context and word encoding:
    OpenEmbeddingTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceTreePrefixes OpenEmbeddingTreeUP
  OpenEmbeddingBranches.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_open_embedding_map]: Federer 2.2.9,
    p. 65, abstract branch-map definition: g(n) belongs to the
    closure of every U(n1,...,nk). *)
Definition is_open_embedding_map (R : realType) (T : metricType R)
    (U : seq nat -> set T) (g : positive_sequence_space R -> T) : Prop :=
  forall n k, closure (U (sequence_tree_prefix n k)) (g n).

(** Source for [open_embedding_map_unique]: supporting uniqueness
    of g for a fixed tree in Federer 2.2.9, p. 65, from
    uniqueness of every branch point. *)
Lemma open_embedding_map_unique (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U)
    (g h : positive_sequence_space R -> T) :
  is_open_embedding_map U g -> is_open_embedding_map U h -> g = h.
Proof.
move=> hg hh; apply: funext=> n.
exact: (@open_embedding_branch_point_unique R T U hU n (g n) (h n) (hg n) (hh n)).
Qed.

(** Source for [open_embedding_map_in_open_branch]: Federer 2.2.9, p. 65,
    the branch point lies in U at every level: the next child closure is
    contained in that open parent. *)
Lemma open_embedding_map_in_open_branch (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U)
    (g : positive_sequence_space R -> T) (hg : is_open_embedding_map U g) n k :
  U (sequence_tree_prefix n k) (g n).
Proof.
exact: (@open_embedding_tree_child_inside R T U hU (sequence_tree_prefix n k)
  (positive_sequence_coordinates n k) (g n) (hg n k.+1)).
Qed.
