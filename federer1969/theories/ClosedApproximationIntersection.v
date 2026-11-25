(** Federer (1969), 2.2.2, p. 61: closure of the inner approximation class
    under countable intersections. The intersection error lies in the union
    of the individual errors. No measurability of the original sets and no
    finite-total-measure hypothesis is needed for this direction. Source
    editions: ClosedApproximationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP ClosedApproximationUP GeometricErrorBudget MeasureGeometricCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [closed_approximable_sequence_intersection]: Federer
    2.2.2, p. 61, first displayed geometric-error estimate.
    Choose closed inner approximants with summable errors and take
    their closed intersection; every point in the excess belongs
    to one of the individual error sets. *)
Lemma closed_approximable_sequence_intersection (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (A : nat -> set T) :
  (forall n, is_closed_approximable mu (A n)) ->
  is_closed_approximable mu (\bigcap_n A n).
Proof.
move=> hA epsilon he.
pose C n := projT1 (cid (hA n _ (geometric_error_budget_positive n he))).
have hC n : closed (C n) /\ C n `<=` A n /\
    mu (A n `\` C n) < (geometric_error_budget epsilon n)%:E.
  exact: projT2 (cid (hA n _ (geometric_error_budget_positive n he))).
exists (\bigcap_n C n); split.
- apply: closed_bigI=> n _; exact: (hC n).1.
- split.
  + move=> x hx n _; exact: (hC n).2.1 x (hx n Logic.I).
  + apply: (proj2 (@measure_geometric_cover_bound R _ mu hm _
      (fun n => A n `\` C n) epsilon he _ (fun n => (hC n).2.2))).
    move=> x [ha hn]; apply: contrapT=> hnone; apply: hn=> n _.
    apply: contrapT=> hnc; apply: hnone; exists n; first exact Logic.I.
    by split; first exact: ha n Logic.I.
Qed.
