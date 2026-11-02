(** Federer (1969), 2.2.2, p. 61: countable-union closure of the inner
    closed-approximation class for a finite measure. All closed sets are
    assumed measurable, but the original sets need not be measurable. Source
    editions and error convention: ClosedApproximationUP.v and
    GeometricErrorBudget.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderLimit MeasureUP ClosedApproximationUP
  GeometricErrorBudget MeasureGeometricCover MeasurePrefixComplementLimit
  SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [closed_approximable_sequence_union]: Federer
    2.2.2, p. 61, second displayed estimate and the finite
    closed-union conclusion. Geometric errors bound the residual
    after all approximants; decreasing continuity after restriction
    then gives a finite closed union with error below epsilon. *)
Lemma closed_approximable_sequence_union (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (A : nat -> set T) :
  mu setT < +oo -> (forall K, closed K -> measure_measurable mu K) ->
  (forall n, is_closed_approximable mu (A n)) ->
  is_closed_approximable mu (\bigcup_n A n).
Proof.
move=> hf hclosed hA epsilon he.
pose C n := projT1 (cid (hA n _ (geometric_error_budget_positive n he))).
have hC n : closed (C n) /\ C n `<=` A n /\
    mu (A n `\` C n) < (geometric_error_budget epsilon n)%:E.
  exact: projT2 (cid (hA n _ (geometric_error_budget_positive n he))).
pose U := \bigcup_n A n.
have herror : mu (U `\` \bigcup_n C n) < epsilon%:E.
  apply: (proj2 (@measure_geometric_cover_bound R _ mu hm _
    (fun n => A n `\` C n) epsilon he _ (fun n => (hC n).2.2))).
  move=> x [[n _ ha] hn]; exists n; first exact Logic.I.
  split=> //; move=> hc; apply: hn; by exists n.
have hmC n : measure_measurable mu (C n) := hclosed _ (hC n).1.
have hlim := @measure_prefix_complement_limit R _ mu hm U C hf hmC.
have [N hN] := hlim.2.2 epsilon%:E herror.
exists (set_sequence_prefix C N); split.
- clear hN; elim: N=> [|N IH]; first by rewrite set_sequence_prefix_zero; exact: closed0.
  rewrite set_sequence_prefix_succ; exact: closedU IH (hC N).1.
- split.
  + move=> x [n _ hx]; exists n; first exact Logic.I.
    exact: (hC n).2.1 x hx.
  + exact: hN N (leqnn N).
Qed.
