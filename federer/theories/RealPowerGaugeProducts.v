(** Federer 2.10.25, p. 189: the real-degree gauge product in the
    first line of the proof. Extend the existing positive-base exponent
    addition only to zero and infinite nonnegative diameters. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealPower RealPowerSuccessor ExtendedPositivePower
  MetricRealPowerCost MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_metric_real_power_add_nonnegative]: supporting
    exact gauge identity for Federer 2.10.25, p. 189. Nonnegative
    exponents add at every nonnegative extended diameter, including
    zero and infinity, with the original zeroth-power conventions. *)
Lemma extended_metric_real_power_add_nonnegative (R : realType)
    (d : \bar R) (p q : R) :
    0<=d -> (0<=p)%R -> (0<=q)%R ->
    extended_metric_real_power d (p+q)%R=
      extended_metric_real_power d p*extended_metric_real_power d q.
Proof.
move=> hd hp hq.
case: (eqVneq p 0%R) => [->|hp0].
  by rewrite add0r /extended_metric_real_power eqxx mul1e.
case: (eqVneq q 0%R) => [->|hq0].
  by rewrite addr0 /extended_metric_real_power eqxx mule1.
have hpp : (0<p)%R by rewrite lt_def hp0 hp.
have hqp : (0<q)%R by rewrite lt_def hq0 hq.
have hpq : (0<p+q)%R := addr_gt0 hpp hqp.
rewrite /extended_metric_real_power (negPf hp0) (negPf hq0) (gt_eqF hpq).
case: d hd => [d hd|_|hd]; last by [].
- rewrite /extended_positive_power /= -EFinM; congr (_%:E).
  have hdR : (0<=d)%R by move: hd; rewrite lee_fin.
  case: (eqVneq d 0%R) => [->|hd0].
  + by rewrite !real_power_zero_base ?gt_eqF // mulr0.
  + apply: real_power_add_exponents_positive.
    by rewrite lt_def hd0 hdR.
- by rewrite /extended_positive_power /= mulyy.
Qed.
