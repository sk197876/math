(** Supporting the section-volume argument of Federer (1969), 2.10.46, p.
    204: for a finite measure, values on all subsets are finite real
    numbers. Translate the splitting and increasing-continuity laws of
    2.1.2–2.1.3, pp. 54–55, to those real values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MeasureUP MeasureBasic MeasureSplit MeasureFiniteAdditivity MeasureContinuityBelow
  FiniteMeasureSetDifference RealErrorOrderLimit ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_total_measure_value]: supporting
    finite real value from monotonicity in 2.1.2, p. 54,
    used in the section-volume argument of 2.10.46, p. 204. *)
Lemma finite_total_measure_value (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  mu setT< +oo -> forall A, mu A=(fine (mu A))%:E.
Proof.
move=> ht A; symmetry; apply: fineK.
rewrite (ge0_fin_numE (measure_nonnegative hm A)).
exact: le_lt_trans (measure_mono hm (subsetT A)) ht.
Qed.

(** Source for [finite_total_measure_difference_fine]:
    real-valued form of the measurable splitting law in
    2.1.2, p. 54, for the section argument of
    2.10.46, p. 204. *)
Lemma finite_total_measure_difference_fine (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A B : set X) :
  mu setT< +oo -> measure_measurable mu A -> A `<=` B ->
  fine (mu (B `\` A))=(fine (mu B)-fine (mu A))%R.
Proof.
move=> ht hA hAB.
have he := @finite_measure_nested_difference R X mu hm A B (fine (mu A)) (fine (mu B))
  hA hAB (finite_total_measure_value hm ht A) (finite_total_measure_value hm ht B).
by rewrite he.
Qed.

(** Source for [finite_total_measure_disjoint_union_fine]:
    finite real form of 2.1.3(3), pp. 54–55,
    supporting the section-volume argument of 2.10.46, p. 204. *)
Lemma finite_total_measure_disjoint_union_fine (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A B : set X) :
  mu setT< +oo -> measure_measurable mu A ->
  (forall x, A x -> B x -> False) -> fine (mu (A `|` B))=(fine (mu A)+fine (mu B))%R.
Proof.
move=> ht hA hd; rewrite (measure_disjoint_union hA hd)
  (finite_total_measure_value hm ht A) (finite_total_measure_value hm ht B).
by [].
Qed.

(** Source for [finite_total_measure_increasing_real_limit]:
    real-topology version of increasing continuity 2.1.3(4),
    p. 55, used for Borel section volumes in 2.10.46,
    p. 204. Measurability of the increasing sets is retained. *)
Lemma finite_total_measure_increasing_real_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : nat -> set X) :
  mu setT< +oo -> (forall n, measure_measurable mu (A n)) ->
  (forall n m, (n<=m)%N -> A n `<=` A m) ->
  (fun n=> (fine (mu (A n)) : real_line_metric R)) @ \oo --> (fine (mu (\bigcup_n A n)) : real_line_metric R).
Proof.
move=> ht hA hinc.
have hl := (@measure_continuity_below R X mu hm A hA hinc).2.
have hr : extended_order_limit (fun n=>(fine (mu (A n)))%:E) (fine (mu (\bigcup_n A n)))%:E.
  have he : (fun n=>(fine (mu (A n)))%:E)=(fun n=>mu (A n)).
    apply: funext=> n; exact: esym (finite_total_measure_value hm ht (A n)).
  by rewrite he -(finite_total_measure_value hm ht (\bigcup_n A n)).
move=> V hV.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP
  (fine (mu (\bigcup_n A n)) : real_line_metric R) V) hV.
have [N hN] := extended_finite_order_limit_error hr he.
exists N; first exact Logic.I.
move=> n hn; apply: hb.
change (mdist (fine (mu (\bigcup_n A n)) : real_line_metric R) (fine (mu (A n)))<e)%R.
rewrite real_line_metric_distanceE distrC.
exact: hN n hn.
Qed.
