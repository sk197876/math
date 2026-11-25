(** Federer (1969), 2.2.8, p. 64: sealed existence of the closed-cover tree.
    The recursive witness is hidden; only the laws in ClosedCoverTreeUP.v
    are exposed. Source context and reversed-word convention are recorded
    there. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import ClosedCoverTreeUP ClosedCoverTreeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type ClosedCoverTreeSignature.
(** Source for [value]: Federer 2.2.8, p. 64, an abstract
    tree of closed sets for a supplied countable dense subset. *)
Parameter value : forall (R : realType) (T : metricType R) (D : set T),
  countable D -> dense D -> (@setT T) !=set0 -> seq nat -> set T.
(** Source for [laws]: Federer 2.2.8, p. 64, all the printed
    closedness, nonemptiness, covering and diameter requirements. *)
Parameter laws : forall (R : realType) (T : metricType R) (D : set T)
  (hc : countable D) (hd : dense D) (hn : (@setT T) !=set0),
  is_closed_cover_tree (@value R T D hc hd hn).
End ClosedCoverTreeSignature.
Module ClosedCoverTree : ClosedCoverTreeSignature.
(** Source for [value]: supporting private witness selection
    for Federer 2.2.8, p. 64, from the proved tree existence theorem. *)
Definition value (R : realType) (T : metricType R) (D : set T)
    (hc : countable D) (hd : dense D) (hn : (@setT T) !=set0) :=
  projT1 (cid (closed_cover_tree_exists hc hd hn)).
(** Source for [laws]: Federer 2.2.8, p. 64, the selected
    witness discharges all abstract tree laws. *)
Lemma laws (R : realType) (T : metricType R) (D : set T)
    (hc : countable D) (hd : dense D) (hn : (@setT T) !=set0) :
  is_closed_cover_tree (@value R T D hc hd hn).
Proof. exact: projT2 (cid (closed_cover_tree_exists hc hd hn)). Qed.
End ClosedCoverTree.
