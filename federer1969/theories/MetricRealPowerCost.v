(** Federer (1969), 2.10.2(1), p. 171, bracketed real-degree extension, used
    in 2.10.29, pp. 193–195. Specify the real power diameter gauge with its
    positive coefficient left explicit. The book chooses alpha(p)*2^-p; this
    file does not define Euler's Gamma function or assume agreement with an
    integer ball-volume normalisation. Include the printed 0^0=infinity^0=1
    conventions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealPower ExtendedPositivePower MetricDiameter MetricDiameterClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_metric_real_power]: supporting
    extended nonnegative real power for the
    real-degree gauge in 2.10.2(1), p. 171.
    At exponent zero both zero and infinity
    have power one; other exponents use the
    existing project power on the nonnegative axis. *)
Definition extended_metric_real_power (R : realType) (x : \bar R) (p : R) :=
  if p==0%R then 1 else extended_positive_power x p.

(** Source for [extended_metric_real_power_nonnegative]: supporting
    nonnegative diameter costs in 2.10.2(1),
    p. 171. Only nonnegative diameter inputs
    enter the later measure specification. *)
Lemma extended_metric_real_power_nonnegative (R : realType) (x : \bar R) (p : R) :
  0<=extended_metric_real_power x p.
Proof. rewrite /extended_metric_real_power; case: ifP=> _; first exact: ler01. exact: extended_positive_power_nonnegative. Qed.

(** Source for [extended_metric_real_power_finite]: supporting
    agreement with real powers on finite
    nonnegative lengths in 2.10.2(1), p. 171,
    including degree zero. *)
Lemma extended_metric_real_power_finite (R : realType) (x p : R) :
  extended_metric_real_power x%:E p=(real_power x p)%:E.
Proof.
rewrite /extended_metric_real_power; case: ifP=> [/eqP ->|hp]; last by [].
by rewrite real_power_zero_exponent.
Qed.

(** Source for [metric_real_power_cost]: supporting
    coefficient c times the real power of a
    nonnegative diameter in 2.10.2(1), p. 171.
    Keeping c explicit separates the covering
    arguments from Euler-Gamma normalisation. *)
Definition metric_real_power_cost (R : realType) (c p : R) (d : \bar R) :=
  c%:E*extended_metric_real_power d p.

(** Source for [metric_real_diameter_cost]: direct
    diameter-gauge form in 2.10.2(1), p. 171,
    with the normalising coefficient explicit.
    The actual covering family excludes empty sets. *)
Definition metric_real_diameter_cost (R : realType) (X : metricType R) (c p : R) (A : set X) :=
  metric_real_power_cost c p (extended_metric_diameter A).

(** Source for [metric_real_power_cost_nonnegative]: supporting
    nonnegative cost hypothesis of Caratheodory's
    construction for 2.10.2(1), p. 171. *)
Lemma metric_real_power_cost_nonnegative (R : realType) (c p : R) (d : \bar R) :
  (0<=c)%R -> 0<=metric_real_power_cost c p d.
Proof.
move=> hc; rewrite /metric_real_power_cost; apply: mule_ge0; first by rewrite lee_fin.
exact: extended_metric_real_power_nonnegative.
Qed.

(** Source for [metric_real_power_cost_finite]: supporting
    finite-length evaluation c*d^p in
    2.10.2(1), p. 171, for the real
    interval and Cartesian cover calculations. *)
Lemma metric_real_power_cost_finite (R : realType) (c p d : R) :
  metric_real_power_cost c p d%:E=(c*real_power d p)%R%:E.
Proof. by rewrite /metric_real_power_cost extended_metric_real_power_finite -EFinM. Qed.

(** Source for [metric_real_power_cost_degree_zero]: direct
    constant degree-zero cost c on nonempty
    generators, including zero and infinite
    diameters, in 2.10.2(1), p. 171.
    Federer's normalisation has c=1 at zero. *)
Lemma metric_real_power_cost_degree_zero (R : realType) (c : R) (d : \bar R) :
  metric_real_power_cost c 0%R d=c%:E.
Proof. by rewrite /metric_real_power_cost /extended_metric_real_power eqxx mule1. Qed.

(** Source for [metric_real_power_cost_monotone]: supporting
    diameter monotonicity for the real-degree
    gauge in 2.10.2(1), p. 171, used
    in the product-cover estimates of 2.10.29. *)
Lemma metric_real_power_cost_monotone (R : realType) (c p : R) (d e : \bar R) :
  (0<=c)%R -> (0<=p)%R -> 0<=d -> d<=e ->
  metric_real_power_cost c p d<=metric_real_power_cost c p e.
Proof.
move=> hc hp hd hde; rewrite /metric_real_power_cost /extended_metric_real_power.
case: ifP=> [/eqP hp0|hp0]; first exact: lexx.
have hpp : (0<p)%R by rewrite lt_neqAle eq_sym hp0 hp.
apply: lee_wpmul2l; first by rewrite lee_fin.
exact: extended_positive_power_monotone hd hde hpp.
Qed.

(** Source for [metric_real_diameter_cost_closure]: direct unchanged
    diameter cost under closure in 2.10.2(1), p. 171 No continuity
    assumption on the diameter gauge is needed for this exact equality. *)
Lemma metric_real_diameter_cost_closure (R : realType) (X : metricType R) (c p : R) (A : set X) :
  metric_real_diameter_cost c p (closure A)=metric_real_diameter_cost c p A.
Proof. by rewrite /metric_real_diameter_cost extended_metric_diameter_closure. Qed.
