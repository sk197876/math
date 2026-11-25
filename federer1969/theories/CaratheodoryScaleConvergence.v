(** Federer (1969), 2.10.1, p. 170, first display: the supremum of the
    approximations is their limit as the positive cutoff decreases to zero.
    This file derives the full positive-cutoff order limit from the abstract
    infimum and supremum laws, including an infinite final value. No
    relevant erratum correction affects this display. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricScaleEnvelopeUP MetricScaleEnvelopeLaws MetricScaleEnvelope
  CaratheodoryLimitUP CaratheodoryBorelRegular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_cutoff_order_limit]: direct order-topology
    interpretation of the limit as delta decreases to zero in
    Federer 2.10.1, p. 170. Every strict bound on either
    side of the candidate limit holds at every sufficiently
    small positive cutoff. Infinite limit values are included. *)
Definition positive_cutoff_order_limit (R : realType)
    (u : \bar R -> \bar R) (l : \bar R) :=
  (forall a, a<l -> exists d : R, (0<d)%R /\
    forall delta, 0<delta -> delta<d%:E -> a<u delta) /\
  (forall b, l<b -> exists d : R, (0<d)%R /\
    forall delta, 0<delta -> delta<d%:E -> u delta<b).

(** Source for [caratheodory_limit_positive_cutoff_convergence]: direct
    limit assertion in Federer 2.10.1, p. 170 It follows from the
    monotonicity and supremum specifications alone, without assuming
    finiteness or restricting the assertion to a sequence of cutoffs. *)
Theorem caratheodory_limit_positive_cutoff_convergence (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) :
  is_caratheodory_limit S cost mu ->
  positive_cutoff_order_limit (fun delta => metric_scale_envelope S cost delta A) (mu A).
Proof.
move=> hmu; split.
- move=> a ha.
  have [eta [nu [he [hn hab]]]] : exists eta nu, 0<eta /\
      is_metric_scale_envelope S cost eta nu /\ a<nu A.
    apply: contrapT=> hnone.
    have hle : mu A<=a.
      apply: (caratheodory_limit_least hmu)=> eta nu he hn.
      rewrite leNgt; apply/negP=> hlt; apply: hnone; by exists eta,nu.
    by have := lt_le_trans ha hle; rewrite ltxx.
  have [n hnsmall] := reciprocal_metric_cutoffs_cofinal he.
  pose d : R := ((n.+1%:R)^-1)%R.
  have hd : (0<d)%R by rewrite /d invr_gt0 ltr0n.
  exists d; split=> // delta hdelta hdd.
  have hde : delta<=eta := le_trans (ltW hdd) hnsmall.
  apply: lt_le_trans hab _.
  exact (@metric_scale_envelope_antitone_cutoff R X J S cost delta eta
    (metric_scale_envelope S cost delta) nu
    (metric_scale_envelope_specification S cost delta) hn hde A).
- move=> b hb; exists 1%R; split; first exact: ltr01.
  move=> delta hd _; apply: le_lt_trans _ hb.
  exact (@caratheodory_limit_upper R X J S cost mu hmu A delta
    (metric_scale_envelope S cost delta) hd (metric_scale_envelope_specification S cost delta)).
Qed.
