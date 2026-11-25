(** General metric measurability background supporting Federer (1969),
    2.9.22, p. 167: in a separable metric target, measurable inverse images
    of all closed balls imply measurability. This expands the countability
    step in the book's dual-evaluation observation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureAlmostBasic MeasureCountableClosure MeasurableFunctionUP
  MetricClosedBalls SeparableClosedCover SequencePowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_total_closed_balls_criterion]: supporting
    separable metric step in Federer 2.9.22, p. 167.
    Every open set is a countable union of closed balls
    contained in it, with centers in a countable dense set
    and radii 2^(-n). No compactness of the balls is used. *)
Theorem measurable_total_closed_balls_criterion (R : realType) (X : choiceType)
    (Y : metricType R) (C : set Y) (mu : set X -> \bar R)
    (hm : is_measure mu) (u : X -> Y) :
  countable C -> dense C ->
  (forall y r, measure_measurable mu (u @^-1` metric_closed_ball y r)) ->
  is_measure_measurable_function mu (partial_function_total u).
Proof.
move=> hCc hCd hb; constructor.
  rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
move=> U ho; rewrite partial_function_total_preimage.
pose B (p : Y * nat) := metric_closed_ball p.1 ((2^-1 : R)^+p.2).
pose J : set (Y * nat) := [set p | C p.1 /\ B p `<=` U].
have hJc : countable J.
  apply: sub_countable _ (countableX hCc (countableP (@setT nat))).
  apply: subset_card_le=> p [hc _]; by split.
have he : u @^-1` U = \bigcup_(p in J) (u @^-1` B p).
  apply/seteqP; split=> x hx.
  - have hn : nbhs (u x) U by rewrite openE in ho; exact: ho (u x) hx.
    have [e he hball] := (metricType_numDomainType.nbhs_mdistP _ _).1 hn.
    have he3 : 0<e/3 by rewrite divr_gt0 // ltr0n.
    have [n hn'] := sequence_inverse_power_small he3.
    pose r := (2^-1 : R)^+n.
    have hr : 0<r by rewrite /r exprn_gt0 // invr_gt0 ltr0n.
    have [c [hc hcx]] := metric_dense_point_near hCd (u x) hr.
    exists (c,n); last first.
      change (mdist c (u x)<=r); rewrite metric_sym; exact: ltW hcx.
    split=> // y hy.
    apply: hball; have ht := metric_triangle (u x) c y.
    change (is_true (mdist c y<=r)) in hy.
    have hsmall : r<e/3 := hn'.
    change (mdist (u x) y<e).
    lra.
  - have [p [_ hp] hpx] := hx; exact: hp (u x) hpx.
rewrite he; apply: (measure_measurable_countable_union hm hJc)=> p _.
exact: hb.
Qed.
