(** Federer (1969), 2.10.24, p. 187: consequences and actual positive-cutoff
    convergence from the weighted limit's supremum laws. Source context:
    WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP WeightedMetricEnvelopeLaws WeightedMetricEnvelope
  WeightedMetricLimitUP CaratheodoryScaleConvergence CaratheodoryBorelRegular MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_metric_limit_unique]: supporting
    uniqueness of the supremum specifying the limit
    in 2.10.24, p. 187. *)
Lemma weighted_metric_limit_unique (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (L M : (X -> \bar R) -> \bar R) :
  is_weighted_metric_limit S c psi L -> is_weighted_metric_limit S c psi M -> L=M.
Proof.
move=> hL hM; apply: funext=> f; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (weighted_metric_limit_least hL)=> delta lambda hd hl.
  exact: (@weighted_metric_limit_upper R X J S c psi M hM f delta lambda hd hl).
- apply: (weighted_metric_limit_least hM)=> delta lambda hd hl.
  exact: (@weighted_metric_limit_upper R X J S c psi L hL f delta lambda hd hl).
Qed.

(** Source for [weighted_metric_limit_nonnegative]: supporting
    nonnegativity of the weighted limit in
    2.10.24, p. 187, from the cost-infimum laws. *)
Lemma weighted_metric_limit_nonnegative (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (L : (X -> \bar R) -> \bar R) : is_weighted_metric_limit S c psi L -> forall f, 0<=L f.
Proof.
move=> hL f.
have hl := @weighted_metric_envelope_specification R X J S c psi 1.
have hpos : (0<1 :> \bar R) by [].
have hh := @weighted_metric_limit_upper R X J S c psi L hL f 1 _ hpos hl.
exact: le_trans (weighted_metric_envelope_nonnegative hl f) hh.
Qed.

(** Source for [weighted_metric_limit_strict_lower_bound]: supporting
    choice of a finite positive cutoff in the
    arguments for 2.10.24, pp. 187–188.
    The first selected cutoff may be infinite;
    reciprocal cofinality supplies a finite one later. *)
Lemma weighted_metric_limit_strict_lower_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (L : (X -> \bar R) -> \bar R) (f : X -> \bar R) (b : \bar R) :
  is_weighted_metric_limit S c psi L -> b<L f -> exists delta lambda,
    0<delta /\ is_weighted_metric_envelope S c psi delta lambda /\ b<lambda f.
Proof.
move=> hL hb; apply: contrapT=> hnone.
have hle : L f<=b.
  apply: (weighted_metric_limit_least hL)=> delta lambda hd hl.
  rewrite leNgt; apply/negP=> hlt; apply: hnone; exists delta,lambda; by split=> //; split.
by have hh := lt_le_trans hb hle; rewrite ltxx in hh.
Qed.

(** Source for [weighted_metric_limit_positive_cutoff_convergence]: direct
    meaning of the limit as delta decreases to
    zero in 2.10.24, p. 187. Both
    eventual order inequalities hold for every sufficiently
    small positive cutoff, including infinite limiting values. *)
Theorem weighted_metric_limit_positive_cutoff_convergence (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (L : (X -> \bar R) -> \bar R) (f : X -> \bar R) :
  is_weighted_metric_limit S c psi L ->
  positive_cutoff_order_limit (fun delta=>weighted_metric_envelope S c psi delta f) (L f).
Proof.
move=> hL; split.
- move=> b hb.
  have [eta [lambda [heta [hl hlower]]]] := @weighted_metric_limit_strict_lower_bound R X J S c psi L f b hL hb.
  have [n hn] := reciprocal_metric_cutoffs_cofinal heta.
  pose d := ((n.+1%:R : R)^-1)%R.
  have hd : (0<d)%R by rewrite /d invr_gt0 ltr0n.
  exists d; split=> // delta hdelta hdd.
  have hde : delta<=eta := le_trans (ltW hdd) hn.
  have hh := @weighted_metric_envelope_antitone_cutoff R X J S c psi delta eta
    (weighted_metric_envelope S c psi delta) lambda (weighted_metric_envelope_specification _ _ _ _) hl hde f.
  exact: lt_le_trans hlower hh.
- move=> b hb; exists 1%R; split; first exact: ltr01.
  move=> delta hdelta hdd; apply: le_lt_trans _ hb.
  exact: (@weighted_metric_limit_upper R X J S c psi L hL f delta _ hdelta (weighted_metric_envelope_specification _ _ _ _)).
Qed.

(** Source for [weighted_metric_limit_zero]: supporting
    zero-function boundary of the cutoff limit in
    2.10.24, p. 187. *)
Lemma weighted_metric_limit_zero (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (L : (X -> \bar R) -> \bar R) :
  is_measure psi -> is_weighted_metric_limit S c psi L -> L (fun _=>0)=0.
Proof.
move=> hm hL; apply/eqP; rewrite eq_le (weighted_metric_limit_nonnegative hL) andbT.
apply: (weighted_metric_limit_least hL)=> delta lambda hd hl.
by rewrite (weighted_metric_envelope_zero hm hl).
Qed.
