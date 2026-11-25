(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground RealOpenIntervals MetricClosedBalls MeasureUP
  MeasureDerivationContext BallMeasureComparisonCorollaries.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_centered_ball_ratio_locus]: supporting
    uniform mass bound in the closed set C_n of Federer
    2.9.17, p. 162. Coefficient c and positive-radius
    cutoff d are explicit; quotient division is avoided in
    this topological comparison set. *)
Definition bounded_centered_ball_ratio_locus (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (c d : R) : set X :=
  [set x | forall r : R, (0<r)%R -> (r<d)%R ->
    psi (metric_closed_ball x r)<=c%:E*phi (metric_closed_ball x r)].

(** Source for [bounded_centered_ball_ratio_locus_closed]: direct
    closedness step for C_n in Federer 2.9.17, p. 162,
    applying the first corollary of 2.9.14. Only phi is
    required to belong to M; the numerator has only measure
    laws, exactly as in the target theorem. *)
Lemma bounded_centered_ball_ratio_locus_closed (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (c d : R) :
  is_derivation_measure phi -> is_measure psi -> (0<c)%R ->
  closed (bounded_centered_ball_ratio_locus psi phi c d).
Proof.
move=> hphi hpsi hc.
pose U : set X := [set x | exists r : R,
  real_open_interval 0%R d r /\ c%:E*phi (metric_closed_ball x r)<psi (metric_closed_ball x r)].
have ho : open U.
  exact (@ball_measure_upper_comparison_open R X phi psi (real_open_interval 0%R d) c
    hphi hpsi hc (@real_open_interval_open R 0%R d) (fun r hr => hr.1)).
have he : bounded_centered_ball_ratio_locus psi phi c d=~` U.
  apply/seteqP; split=> x.
  - move=> hx [r [[hr hrd] hlt]].
    by have := lt_le_trans hlt (hx r hr hrd); rewrite ltxx.
  - move=> hx r hr hrd; rewrite leNgt; apply/negP=> hlt.
    apply: hx; exists r; split=> //; by split.
rewrite he; exact: open_closedC ho.
Qed.

(** Source for [closed_target_ball_ratio_locus]: direct closed
    set C_n step in Federer 2.9.17, p. 162,
    retaining an arbitrary closed target T and explicit positive
    coefficient and radius cutoff. *)
Lemma closed_target_ball_ratio_locus (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (T : set X) (c d : R) :
  is_derivation_measure phi -> is_measure psi -> closed T -> (0<c)%R ->
  closed (T `&` bounded_centered_ball_ratio_locus psi phi c d).
Proof.
move=> hphi hpsi hT hc; apply: closedI hT _.
exact (@bounded_centered_ball_ratio_locus_closed R X psi phi c d hphi hpsi hc).
Qed.
