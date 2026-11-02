(** Federer (1969), 2.2.9, p. 65: sealed existence of the open embedding
    tree. The recursive witness is hidden; only the laws in
    OpenEmbeddingTreeUP.v are exposed. Source context and reversed-word
    convention are recorded there. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import NoIsolatedPoints OpenEmbeddingTreeUP OpenEmbeddingTreeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type OpenEmbeddingTreeSignature.
(** Source for [value]: Federer 2.2.9, p. 65, an abstract
    open tree for a nonempty metric space with no isolated points. *)
Parameter value : forall (R : realType) (T : metricType R),
  has_no_isolated_points T -> (@setT T) !=set0 -> seq nat -> set T.
(** Source for [laws]: Federer 2.2.9, p. 65, the printed
    nesting, disjointness and small-diameter tree requirements. *)
Parameter laws : forall (R : realType) (T : metricType R)
  (hT : has_no_isolated_points T) (hn : (@setT T) !=set0),
  is_open_embedding_tree (@value R T hT hn).
End OpenEmbeddingTreeSignature.
Module OpenEmbeddingTree : OpenEmbeddingTreeSignature.
(** Source for [value]: supporting witness selection for
    Federer 2.2.9, p. 65, from the proved open-tree existence theorem. *)
Definition value (R : realType) (T : metricType R)
    (hT : has_no_isolated_points T) (hn : (@setT T) !=set0) :=
  projT1 (cid (open_embedding_tree_exists hT hn)).
(** Source for [laws]: Federer 2.2.9, p. 65, the selected
    witness satisfies the abstract open-tree specification. *)
Lemma laws (R : realType) (T : metricType R)
    (hT : has_no_isolated_points T) (hn : (@setT T) !=set0) :
  is_open_embedding_tree (@value R T hT hn).
Proof. exact: projT2 (cid (open_embedding_tree_exists hT hn)). Qed.
End OpenEmbeddingTree.
