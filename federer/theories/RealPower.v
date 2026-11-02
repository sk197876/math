(** Elementary powers supporting Federer (1969), 2.4.12, pp. 86–87, and
    2.4.13, p. 88. Only nonnegative bases are used in the integration
    theory. The zero-exponent convention is 0^0 = 1; positive exponents give
    0^p = 0. These are scalar support lemmas, not separately numbered
    statements of the book. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealExponentialUP RealExponentialSealed RealExponentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power]: real powers used in Federer
    2.4.12, p. 86, expressed through abstract exp and log
    as used in 2.4.13, p. 88. Values on negative bases
    are outside the specification and never used. *)
Definition real_power (R : realType) (x p : R) :=
  if x == 0 then (p == 0)%:R else
  RealExponential.exponential (p * RealExponential.logarithm x).

Section Power.
Variable R : realType.
Local Notation h := (@RealExponential.laws R).

(** Source for [real_power_positive_base]: exponential expression
    for positive bases, supporting Federer 2.4.13, p. 88. *)
Lemma real_power_positive_base (x p : R) : 0 < x ->
  real_power x p = RealExponential.exponential (p * RealExponential.logarithm x).
Proof. by move=> hx; rewrite /real_power (gt_eqF hx). Qed.

(** Source for [real_power_zero_base]: zero-base convention for
    positive powers in Federer 2.4.12, p. 86. *)
Lemma real_power_zero_base (p : R) : p != 0 -> real_power 0 p = 0.
Proof. by move=> hp; rewrite /real_power eqxx (negPf hp). Qed.

(** Source for [real_power_zero_exponent]: supporting scalar
    convention for powers in Federer 2.4.12–13, pp. 86–88. *)
Lemma real_power_zero_exponent (x : R) : real_power x 0 = 1.
Proof. by rewrite /real_power eqxx mul0r (real_exponential_zero h); case: ifP. Qed.

(** Source for [real_power_one_base]: supporting scalar
    normalisation for Federer 2.4.12–13, pp. 86–88. *)
Lemma real_power_one_base (p : R) : real_power 1 p = 1.
Proof. by rewrite /real_power oner_eq0 real_logarithm_one mulr0 (real_exponential_zero h). Qed.

(** Source for [real_power_one_exponent]: recovery of the
    p = 1 integrand in Federer 2.4.12, p. 86. *)
Lemma real_power_one_exponent (x : R) : 0 <= x -> real_power x 1 = x.
Proof.
move=> hx; have [->|hx0] := eqVneq x 0; first by rewrite /real_power eqxx oner_eq0.
rewrite /real_power (negPf hx0) mul1r (real_exponential_logarithm h) //.
by rewrite lt_neqAle eq_sym hx0 hx.
Qed.

(** Source for [real_power_nonnegative]: nonnegative scalar
    powers used in Federer 2.4.12, p. 86. *)
Lemma real_power_nonnegative (x p : R) : 0 <= real_power x p.
Proof.
rewrite /real_power; case: ifP=> _; first exact: ler0n.
exact: ltW (real_exponential_positive h _).
Qed.

(** Source for [real_power_strictly_positive]: positivity for
    positive bases, supporting Federer 2.4.13, p. 88. *)
Lemma real_power_strictly_positive (x p : R) : 0 < x -> 0 < real_power x p.
Proof. move=> hx; rewrite /real_power (gt_eqF hx).
exact (real_exponential_positive h (p * RealExponential.logarithm x)). Qed.

(** Source for [real_power_product]: multiplicativity on
    nonnegative bases, supporting the Lp computations in
    Federer 2.4.12–15, pp. 86–89. *)
Lemma real_power_product (x y p : R) :
  0 <= x -> 0 <= y -> real_power (x*y) p = real_power x p * real_power y p.
Proof.
move=> hx hy; have [->|hp] := eqVneq p 0.
  by rewrite !real_power_zero_exponent mul1r.
have [->|hx0] := eqVneq x 0.
  by rewrite mul0r !real_power_zero_base // mul0r.
have [->|hy0] := eqVneq y 0.
  by rewrite mulr0 !real_power_zero_base // mulr0.
have hxpos : 0 < x by rewrite lt_neqAle eq_sym hx0 hx.
have hypos : 0 < y by rewrite lt_neqAle eq_sym hy0 hy.
rewrite !real_power_positive_base ?mulr_gt0 // real_logarithm_product // mulrDr.
exact (real_exponential_add h (p * RealExponential.logarithm x) (p * RealExponential.logarithm y)).
Qed.

(** Source for [real_power_positive_iterate]: iterating positive
    real powers multiplies exponents, supporting the root in
    Federer 2.4.12, p. 86, and 2.4.15, p. 89. *)
Lemma real_power_positive_iterate (x p q : R) :
  0 <= x -> 0 < p -> 0 < q ->
  real_power (real_power x p) q = real_power x (p*q).
Proof.
move=> hx hp hq; have [->|hx0] := eqVneq x 0.
  by rewrite !real_power_zero_base ?gt_eqF ?mulr_gt0.
have hxpos : 0 < x by rewrite lt_neqAle eq_sym hx0 hx.
by rewrite /real_power (negPf hx0)
  (gt_eqF (real_exponential_positive h (p * RealExponential.logarithm x)))
  (real_logarithm_exponential h) mulrA [q * p]mulrC.
Qed.

(** Source for [real_power_monotone]: positive-exponent order
    preservation supporting the power comparisons in Federer
    2.4.12–15, pp. 86–89. *)
Lemma real_power_monotone (x y p : R) :
  0 <= x -> x <= y -> 0 < p -> real_power x p <= real_power y p.
Proof.
move=> hx hxy hp; have [->|hx0] := eqVneq x 0.
  rewrite real_power_zero_base ?gt_eqF //; exact: real_power_nonnegative.
have hxpos : 0 < x by rewrite lt_neqAle eq_sym hx0 hx.
have hypos := lt_le_trans hxpos hxy.
rewrite !real_power_positive_base // real_exponential_order ler_pM2l //.
by rewrite real_logarithm_order.
Qed.

(** Source for [real_power_root_cancel]: cancellation of a
    positive power and its reciprocal, supporting the Lp
    definition in Federer 2.4.12, p. 86. *)
Lemma real_power_root_cancel (x p : R) :
  0 <= x -> 0 < p -> real_power (real_power x p) p^-1 = x.
Proof.
move=> hx hp; rewrite real_power_positive_iterate ?invr_gt0 //
  mulfV ?gt_eqF // real_power_one_exponent //.
Qed.
End Power.

(** Source for [real_power_strict_monotone]: strict scalar order
    preservation for positive powers, supporting the Lp root and
    level-set comparisons in Federer 2.4.12, pp. 86–87. *)
Lemma real_power_strict_monotone (R : realType) (x y p : R) :
  0 <= x -> x < y -> 0 < p -> real_power x p < real_power y p.
Proof.
move=> hx hxy hp; have hypos := le_lt_trans hx hxy.
have [->|hx0] := eqVneq x 0.
  rewrite real_power_zero_base ?gt_eqF //; exact: real_power_strictly_positive hypos.
have hxpos : 0 < x by rewrite lt_neqAle eq_sym hx0 hx.
by rewrite !real_power_positive_base // (real_exponential_strict_order (@RealExponential.laws R))
  ltr_pM2l // ltNge real_logarithm_order // -ltNge.
Qed.

(** Source for [real_power_order_embedding]: order reflection
    on nonnegative bases, supporting the power/root comparisons
    in Federer 2.4.12, pp. 86–87. *)
Lemma real_power_order_embedding (R : realType) (x y p : R) :
  0 <= x -> 0 <= y -> 0 < p ->
  (real_power x p <= real_power y p) = (x <= y).
Proof.
move=> hx hy hp; apply/idP/idP; last by move=> hxy; exact: real_power_monotone hx hxy hp.
move=> h; rewrite leNgt; apply/negP=> hyx.
have hstrict := real_power_strict_monotone hy hyx hp.
by move: hstrict; rewrite ltNge h.
Qed.

(** Source for [real_power_le_root]: supporting inversion of
    positive-power sublevels in Federer 2.4.12, pp. 86–87.
    The threshold and base are both nonnegative. *)
Lemma real_power_le_root (R : realType) (x r p : R) :
  0 <= x -> 0 <= r -> 0 < p ->
  (real_power x p <= r) = (x <= real_power r p^-1).
Proof.
move=> hx hr hp.
have hi : 0 < p^-1 by rewrite invr_gt0.
have he := real_power_order_embedding (real_power_nonnegative x p) hr hi.
by rewrite real_power_root_cancel // in he.
Qed.
