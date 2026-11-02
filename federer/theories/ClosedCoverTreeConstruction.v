(** Federer (1969), 2.2.8, p. 64: construction of the abstract closed-cover
    tree by successive countable refinements. Ordinary recursion on reversed
    finite words replaces the maximal-principle presentation in that
    footnote. The witness is private; downstream arguments use only the tree
    laws. Source context and encoding: ClosedCoverTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import ClosedCoverTreeUP SeparableClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Construction.
Variable R : realType.
Variable T : metricType R.
Variable D : set T.
Hypothesis hcnt : countable D.
Hypothesis hdense : dense D.
Hypothesis hnonempty : (@setT T) !=set0.

(** Source for [closed_nonempty_piece]: supporting witness type
    for Federer 2.2.8, p. 64: a closed nonempty subset together
    with its proved laws, used only in the recursive construction. *)
Definition closed_nonempty_piece := { C : set T | closed C /\ C !=set0 }.

(** Source for [closed_piece_refinement_exists]: Federer 2.2.8, p. 64,
    supporting recursive choice: a closed nonempty parent has a sequence of
    closed nonempty children at the next scale. *)
Lemma closed_piece_refinement_exists (C : closed_nonempty_piece) k :
  exists F : nat -> set T,
    (forall n, closed (F n) /\ F n !=set0 /\ F n `<=` proj1_sig C /\
      forall x y, F n x -> F n y -> mdist x y <= @closed_cover_tree_scale R k.+1) /\
    proj1_sig C = \bigcup_n F n.
Proof.
exact: separable_closed_small_cover hcnt hdense (proj1 (proj2_sig C))
  (proj2 (proj2_sig C)) (@closed_cover_tree_scale_positive R k.+1).
Qed.

(** Source for [closed_piece_children]: supporting private
    selection of a countable child family in Federer 2.2.8,
    p. 64, from the proved refinement theorem. *)
Definition closed_piece_children (C : closed_nonempty_piece) k :=
  projT1 (cid (closed_piece_refinement_exists C k)).

(** Source for [closed_piece_children_laws]: supporting proof
    that the selected family satisfies the refinement laws of
    Federer 2.2.8, p. 64; no unproved choice specification. *)
Lemma closed_piece_children_laws (C : closed_nonempty_piece) k :
    (forall n, closed (closed_piece_children C k n) /\
      closed_piece_children C k n !=set0 /\ closed_piece_children C k n `<=` proj1_sig C /\
      forall x y, closed_piece_children C k n x -> closed_piece_children C k n y ->
        mdist x y <= @closed_cover_tree_scale R k.+1) /\
    proj1_sig C = \bigcup_n closed_piece_children C k n.
Proof. exact: projT2 (cid (closed_piece_refinement_exists C k)). Qed.

(** Source for [closed_piece_child]: supporting recursive step
    for Federer 2.2.8, p. 64: package a selected child with
    its already proved closedness and nonemptiness. *)
Definition closed_piece_child (C : closed_nonempty_piece) k j : closed_nonempty_piece :=
  exist _ (closed_piece_children C k j)
    (conj ((closed_piece_children_laws C k).1 j).1
      ((closed_piece_children_laws C k).1 j).2.1).

(** Source for [closed_piece_root]: supporting root for
    Federer 2.2.8, p. 64: the whole nonempty space is closed. *)
Definition closed_piece_root : closed_nonempty_piece :=
  exist _ setT (conj (@closedT T) hnonempty).

(** Source for [closed_cover_piece_witness]: Federer 2.2.8,
    p. 64, recursive construction of all the closed sets E(s),
    using reversed word storage as documented in ClosedCoverTreeUP.v. *)
Fixpoint closed_cover_piece_witness (s : seq nat) : closed_nonempty_piece :=
  if s is j::t then closed_piece_child (closed_cover_piece_witness t) (size t) j
  else closed_piece_root.

(** Source for [closed_cover_tree_exists]: Federer 2.2.8, p. 64, existence
    of a family E satisfying all displayed covering and diameter
    requirements. *)
Theorem closed_cover_tree_exists : exists E : seq nat -> set T, is_closed_cover_tree E.
Proof.
exists (fun s => proj1_sig (closed_cover_piece_witness s)); constructor.
- by [].
- move=> s; exact: (proj2_sig (closed_cover_piece_witness s)).1.
- move=> s; exact: (proj2_sig (closed_cover_piece_witness s)).2.
- move=> s; exact: (closed_piece_children_laws (closed_cover_piece_witness s) (size s)).2.
- move=> [|j s] // _ x y hx hy.
  exact: ((closed_piece_children_laws (closed_cover_piece_witness s) (size s)).1 j).2.2.2 x y hx hy.
Qed.
End Construction.
