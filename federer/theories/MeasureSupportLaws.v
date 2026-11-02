(** Federer (1969), 2.2.1, p. 60: consequences of the abstract support
    specification. No nullity of the entire complement is asserted; Federer
    explicitly warns that this need not hold. Source context:
    MeasureSupportUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureSupportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_support_specification_formula]: Federer
    2.2.1, p. 60, the printed defining formula: the support
    is the complement of the union of open sets of measure zero.
    Here it is derived from the abstract neighborhood law. *)
Lemma measure_support_specification_formula (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (S : set T) : is_measure_support mu S ->
  S = ~` (\bigcup_(U in [set U | open U /\ mu U = 0]) U).
Proof.
move=> hS; apply/seteqP; split.
- move=> x hx [U [ho hz] hu]; exact: (proj1 (measure_support_neighborhood_law hS x) hx U ho hu hz).
- move=> x hn; apply: (proj2 (measure_support_neighborhood_law hS x))=> U ho hu hz.
  apply: hn; exists U=> //; by split.
Qed.

(** Source for [measure_support_positive_neighborhood]: Federer
    2.2.1, p. 60, supporting equivalent characterisation: every
    open neighborhood of a support point has positive measure,
    since measure values are nonnegative. *)
Lemma measure_support_positive_neighborhood (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (S : set T)
    (hS : is_measure_support mu S) x :
  S x <-> forall U, open U -> U x -> 0 < mu U.
Proof.
rewrite (measure_support_neighborhood_law hS x); split.
- move=> hn U ho hu; rewrite lt_def (measure_nonnegative hm) andbT.
  apply/eqP; exact: hn U ho hu.
- move=> hp U ho hu he; have h := hp U ho hu; by rewrite he ltxx in h.
Qed.

(** Source for [measure_support_open_null_disjoint]: Federer
    2.2.1, p. 60: every open null set is disjoint from the
    support, directly from the defining union formula. *)
Lemma measure_support_open_null_disjoint (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (S U : set T) (hS : is_measure_support mu S) :
  open U -> mu U = 0 -> U `&` S = set0.
Proof.
move=> ho hz; apply/seteqP; split=> [x [hu hs]|x []].
exact: (proj1 (measure_support_neighborhood_law hS x) hs U ho hu hz).
Qed.
