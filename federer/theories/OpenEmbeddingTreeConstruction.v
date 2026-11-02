(** Federer (1969), 2.2.9, p. 65: recursive construction of the open
    embedding tree, using the proved and sealed countable refinements. The
    private recursive carrier packages open nonempty sets with their proofs.
    Source context and reversed word convention: OpenEmbeddingTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import NoIsolatedPoints OpenRefinementUP OpenRefinementSealed
  ClosedCoverTreeUP OpenEmbeddingTreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Construction.
Variable R : realType.
Variable T : metricType R.
Hypothesis hT : has_no_isolated_points T.
Hypothesis hn : (@setT T) !=set0.

(** Source for [open_nonempty_piece]: supporting witness type
    for Federer 2.2.9, p. 65: an open nonempty set with
    proved laws, used only in the private recursive construction. *)
Definition open_nonempty_piece := { A : set T | open A /\ A !=set0 }.

(** Source for [open_piece_children]: supporting child family
    for Federer 2.2.9, p. 65, obtained from the sealed
    refinement at the next printed diameter scale. *)
Definition open_piece_children (C : open_nonempty_piece) k : nat -> set T :=
  @OpenRefinement.value R T hT (proj1_sig C) (proj2_sig C).1 (proj2_sig C).2
    (@closed_cover_tree_scale R k.+1) (@closed_cover_tree_scale_positive R k.+1).

(** Source for [open_piece_children_laws]: supporting refinement
    laws for the recursive step in Federer 2.2.9, p. 65;
    this uses only the opaque refinement interface. *)
Lemma open_piece_children_laws (C : open_nonempty_piece) k :
  is_open_disjoint_refinement (proj1_sig C) (@closed_cover_tree_scale R k.+1)
    (open_piece_children C k).
Proof. exact: OpenRefinement.laws. Qed.

(** Source for [open_piece_child]: supporting recursive child
    object for Federer 2.2.9, p. 65, packaged with the
    already proved open and nonempty laws. *)
Definition open_piece_child (C : open_nonempty_piece) k j : open_nonempty_piece :=
  exist _ (open_piece_children C k j)
    (conj (@open_refinement_open R T _ _ _ (open_piece_children_laws C k) j)
      (@open_refinement_nonempty R T _ _ _ (open_piece_children_laws C k) j)).

(** Source for [open_piece_root]: supporting root for Federer
    2.2.9, p. 65: the whole nonempty space is open. *)
Definition open_piece_root : open_nonempty_piece := exist _ setT (conj (@openT T) hn).

(** Source for [open_embedding_piece_witness]: Federer 2.2.9,
    p. 65, recursive construction of U(s) with structural
    recursion on reversed finite coordinate words. *)
Fixpoint open_embedding_piece_witness (s : seq nat) : open_nonempty_piece :=
  if s is j::t then open_piece_child (open_embedding_piece_witness t) (size t) j
  else open_piece_root.

(** Source for [open_embedding_tree_exists]: Federer 2.2.9, p. 65, existence
    of the entire open tree with all printed closure, disjointness and
    strict diameter requirements. Completeness is needed only later for
    branch points, not for this tree construction. *)
Theorem open_embedding_tree_exists : exists U : seq nat -> set T, is_open_embedding_tree U.
Proof.
exists (fun s => proj1_sig (open_embedding_piece_witness s)); constructor.
- by [].
- move=> s; exact: (proj2_sig (open_embedding_piece_witness s)).1.
- move=> s; exact: (proj2_sig (open_embedding_piece_witness s)).2.
- move=> s j; exact: (@open_refinement_inside R T _ _ _
    (open_piece_children_laws (open_embedding_piece_witness s) (size s)) j).
- move=> s i j hij.
  have hd := @open_refinement_disjoint R T _ _ _
    (open_piece_children_laws (open_embedding_piece_witness s) (size s)) i j hij.
  apply/seteqP; split; last by move=> x [].
  move=> x [hxi hxj].
  have hi : closure (open_piece_children (open_embedding_piece_witness s) (size s) i) x.
    exact: subset_closure hxi.
  have hj : closure (open_piece_children (open_embedding_piece_witness s) (size s) j) x.
    exact: subset_closure hxj.
  have hh : (closure (open_piece_children (open_embedding_piece_witness s) (size s) i) `&`
      closure (open_piece_children (open_embedding_piece_witness s) (size s) j)) x by split.
  by rewrite hd in hh.
- move=> [|j s] // _ x y hx hy.
  exact: (@open_refinement_diameter R T _ _ _
    (open_piece_children_laws (open_embedding_piece_witness s) (size s)) j x y hx hy).
Qed.
End Construction.
