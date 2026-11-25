(** Federer (1969), 2.10.26, p. 190: reduction to compact A by 2.2.3, pp.
    61–62. Expand finite measurable inner approximation into an increasing
    sequence of compact subsets with null remainder in a boundedly compact
    metric source. A supplied centre is used only for the compact
    closed-ball exhaustion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealReciprocalBounds MetricClosedBalls LipschitzFunctionCompact
  NullFibresProperSource BorelRegularMeasureUP BorelRegularApproximation MeasureUP MeasureBasic
  MeasureAlmostBasic CountableFamilySequence SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [proper_metric_finite_compact_approximation]:
    supporting compact reduction in 2.10.26, p. 190,
    from 2.2.3, pp. 61–62. Every finite
    measurable A is an increasing compact union
    up to a null remainder. The chosen centre
    is bookkeeping, and need not belong to A. *)
Theorem proper_metric_finite_compact_approximation (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_borel_regular_measure mu)
    (A : set X) (a : X) :
  metric_boundedly_compact X -> measure_measurable mu A -> mu A< +oo ->
  exists K : nat -> set X, (forall n, compact (K n)) /\
    (forall n, K n `<=` A) /\ (forall n m, (n<=m)%N -> K n `<=` K m) /\
    mu (A `\` (\bigcup_n K n))=0.
Proof.
move=> hX hA hfin.
have hex n : exists C, closed C /\ C `<=` A /\ mu (A `\` C)<((n.+1%:R : R)^-1)%R%:E.
  apply: (@borel_regular_closed_approximation R X mu hm hr A hA hfin).
  by rewrite invr_gt0 ltr0n.
pose C n := projT1 (cid (hex n)); have hC n := projT2 (cid (hex n)).
have hnull : mu (A `\` (\bigcup_n C n))=0.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  apply: (@extended_real_reciprocal_upper_bound R _ 0%R)=> n; rewrite add0r.
  apply: le_trans _ (ltW (hC n).2.2).
  apply: (@measure_mono R X mu hm)=> x [hx hn]; split=> // hc; apply: hn; by exists n.
pose D (p : nat*nat) := C p.1 `&` metric_closed_ball a (p.2%:R : R).
have hDc p : compact (D p).
  rewrite /D setIC; exact: compact_closedI (hX a _ (@ler0n R p.2)) (hC p.1).1.
have hDA p : D p `<=` A by move=> x [hx _]; exact: (hC p.1).2.1 x hx.
have hDU : (\bigcup_p D p)=\bigcup_n C n.
  apply/seteqP; split.
  - move=> x [p _ [hx _]]; by exists p.1.
  - move=> x [n _ hx]; have [j _ hj] := @metric_natural_closed_balls_cover R X a x Logic.I.
    exists (n,j)=> //; by split.
have [E [hE hEU]] := @countable_family_as_sequence X [the choiceType of ((nat*nat)%type : Type)]
  setT D (countableP _).
have hEc n : compact (E n).
  case: (hE n)=> [->|[p [_ ->]]]; [exact: compact0|exact: hDc].
have hEA n : E n `<=` A.
  case: (hE n)=> [->|[p [_ ->]]]; [by move=> x []|exact: hDA].
pose K n := set_sequence_prefix E n.
have hKc n : compact (K n).
  elim: n=> [|n ih]; first by rewrite /K set_sequence_prefix_zero; exact: compact0.
  rewrite /K set_sequence_prefix_succ; exact: compactU ih (hEc n).
have hKA n : K n `<=` A by move=> x [i hi hx]; exact: hEA i x hx.
have hKi n m (hnm : (n<=m)%N) : K n `<=` K m.
  move=> x [i hi hx]; exists i=> //; exact: leq_trans hi hnm.
have hKU : (\bigcup_n K n)=\bigcup_n E n.
  apply/seteqP; split=> [x [n _ [i hi hx]]|x [i _ hx]].
  - by exists i.
  - exists i.+1=> //; exists i=> //; exact: ltnSn.
exists K; split=> //; split=> //; split=> //.
by rewrite hKU hEU hDU.
Qed.
