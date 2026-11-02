(** Federer (1969), 2.2.2(2), p. 61, construction of an open approximation
    from closed approximations to V_i minus B. This supporting form isolates
    exactly the hypotheses used by the construction, allowing its reuse for
    measurable B in 2.2.3, pp. 61-62. Source context:
    ClosedApproximationUP.v. *)
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

(** Source for [open_cover_from_closed_complements]: Federer
    2.2.2(2), p. 61, supporting form of the final construction:
    closed inner approximants C_i to V_i minus B yield the open
    superset union(V_i minus C_i), with total geometric error below
    epsilon. No additional measurability premise on B is used here. *)
Lemma open_cover_from_closed_complements (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (B : set T)
    (V : nat -> set T) (epsilon : R) :
  (forall n, open (V n)) -> B `<=` \bigcup_n V n ->
  (forall n, is_closed_approximable mu (V n `\` B)) -> (0 < epsilon)%R ->
  exists W, open W /\ B `<=` W /\ mu (W `\` B) < epsilon%:E.
Proof.
move=> hV hcover hD he.
pose C n := projT1 (cid (hD n _ (geometric_error_budget_positive n he))).
have hC n : closed (C n) /\ C n `<=` V n `\` B /\
    mu ((V n `\` B) `\` C n) < (geometric_error_budget epsilon n)%:E.
  exact: projT2 (cid (hD n _ (geometric_error_budget_positive n he))).
pose W := \bigcup_n (V n `\` C n).
exists W; split.
- apply: bigcup_open=> n _; rewrite setDE.
  exact: openI (hV n) (closed_openC (hC n).1).
- split.
  + move=> x hx; have [n _ hv] := hcover x hx; exists n; first exact Logic.I.
    split=> //; move=> hc; exact: ((hC n).2.1 x hc).2 hx.
  + apply: (proj2 (@measure_geometric_cover_bound R _ mu hm (W `\` B)
      (fun n => (V n `\` B) `\` C n) epsilon he _ (fun n => (hC n).2.2))).
    move=> x [[n _ [hv hn]] hb]; exists n; first exact Logic.I.
    split=> //; by split.
Qed.
