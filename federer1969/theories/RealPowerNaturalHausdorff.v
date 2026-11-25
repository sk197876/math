(** Federer (1969), 2.10.2(1), p. 171: for natural degree the real-power
    gauge agrees with the printed alpha(m) 2^(-m) diameter power. This
    adapter applies the real-power proof of 2.10.47, pp. 204–205, to the
    existing Hausdorff interface without altering its normalisation or
    zero-degree conventions. The separate real-degree Euler-Gamma extension
    is not assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealPower RealPowerSuccessor ExtendedPositivePower
  MetricDiameterUP MetricDiameter MetricRealPowerCost MetricRealPowerMeasureUP
  HausdorffDiameterCost HausdorffMeasureUP HausdorffLengthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_natural_exponent]: supporting
    agreement of real and natural powers for the gauge
    in 2.10.2(1), p. 171, including 0^0=1. *)
Lemma real_power_natural_exponent (R : realType) (x : R) m :
  (0<=x)%R -> real_power x m%:R=(x^+m)%R.
Proof.
move=> hx; case: (eqVneq x 0%R)=> [->|hxne].
- case: m=> [|m]; first by rewrite real_power_zero_exponent expr0.
  by rewrite real_power_zero_base ?pnatr_eq0 // expr0n.
- have hxpos : (0<x)%R by rewrite lt_neqAle eq_sym hxne hx.
  elim: m=> [|m IH]; first by rewrite real_power_zero_exponent expr0.
  by rewrite -[m.+1]addn1 natrD real_power_add_exponents_positive // IH real_power_one_exponent // exprD expr1.
Qed.

(** Source for [extended_metric_real_power_natural]: supporting
    natural-degree compatibility of the extended diameter
    powers in 2.10.2(1), p. 171. Positive infinity
    to exponent zero remains one. *)
Lemma extended_metric_real_power_natural (R : realType) (d : \bar R) m :
  0<=d -> extended_metric_real_power d m%:R=d^+m.
Proof.
case: d=> [d| |] hd.
- rewrite extended_metric_real_power_finite -EFin_expe; congr (_%:E).
  apply: real_power_natural_exponent; by move: hd; rewrite lee_fin.
- case: m=> [|m]; first by rewrite /extended_metric_real_power eqxx expe0.
  have hne : ((m.+1)%:R : R)!=0%R by rewrite pnatr_eq0.
  rewrite /extended_metric_real_power (negPf hne) /extended_positive_power.
  clear hne; symmetry; elim: m=> [|m IH]; first by rewrite expeS expe0 mule1.
  by rewrite expeS IH mulyy.
- by move: hd; rewrite leeNy_eq.
Qed.

(** Source for [real_power_natural_hausdorff_cost]: exact
    equality with the normalised cost of 2.10.2(1),
    p. 171, used for the theorem 2.10.47. *)
Lemma real_power_natural_hausdorff_cost (R : realType) (X : metricType R) m (A : set X) :
  metric_real_diameter_cost (hausdorff_normalisation R m) m%:R A=hausdorff_diameter_cost m A.
Proof.
rewrite /metric_real_diameter_cost /metric_real_power_cost /hausdorff_diameter_cost /hausdorff_power_cost.
by rewrite extended_metric_real_power_natural //; exact: metric_diameter_nonnegative (extended_metric_diameter_specification A).
Qed.

(** Source for [hausdorff_natural_real_power_laws]: every
    Hausdorff measure satisfying the printed natural-degree
    specification of 2.10.2(1), p. 171, satisfies
    the matching real-power laws. This is a proved adapter,
    not an additional assumption for 2.10.47. *)
Lemma hausdorff_natural_real_power_laws (R : realType) (X : metricType R) m (mu : set X -> \bar R) :
  is_hausdorff_measure m mu -> is_metric_real_power_measure (hausdorff_normalisation R m) m%:R mu.
Proof.
move=> hmu.
have he : (fun S : @nonempty_metric_sets R X=>metric_real_diameter_cost (hausdorff_normalisation R m) m%:R (val S))=
    (fun S : @nonempty_metric_sets R X=>hausdorff_diameter_cost m (val S)).
  apply: funext=> S; exact: real_power_natural_hausdorff_cost.
by rewrite /is_metric_real_power_measure he.
Qed.
