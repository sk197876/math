(** Federer (1969), 2.4.17, p. 90: pointwise passage to the limit in |f|^p
    when the exponent varies. The supporting scalar fact includes zero bases
    but requires positive exponents, as in the book's Lebesgue-norm domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit RealScalarOrderLimits RealExponentialOrderLimit
  RealExponentialSealed RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_exponent_order_limit]: Supporting Federer 2.4.17,
    p. 90. *)
Lemma real_power_exponent_order_limit (R : realType) (p : nat -> R) (q x : R) :
  (0 <= x)%R -> (0 < q)%R -> (forall n, (0 < p n)%R) ->
  extended_order_limit (fun n => (p n)%:E) q%:E ->
  extended_order_limit (fun n => (real_power x (p n))%:E) (real_power x q)%:E.
Proof.
move=> hx hq hp hl; have [hx0|hx0] := eqVneq x 0%R.
- rewrite hx0 real_power_zero_base ?gt_eqF //.
  have he : (fun n => (real_power 0 (p n))%:E) = (fun _ : nat => (0 : \bar R)).
    apply/funext=> n; by rewrite real_power_zero_base ?gt_eqF.
  rewrite he; exact: real_constant_order_limit.
have hxp : (0 < x)%R by rewrite lt_neqAle eq_sym hx0 hx.
rewrite real_power_positive_base //.
have he : (fun n => (real_power x (p n))%:E) =
    (fun n => (RealExponential.exponential (RealExponential.logarithm x * p n)%R)%:E).
  apply/funext=> n; by rewrite real_power_positive_base // mulrC.
rewrite he [(q * _)%R]mulrC; apply: real_exponential_order_limit.
exact: real_scalar_order_limit.
Qed.

(** Source for [real_power_positive_base_exponent_limit]: Supporting Federer
    2.4.17, p. 90.Positive bases allow arbitrary real exponents, including
    limiting exponent zero. *)
Lemma real_power_positive_base_exponent_limit (R : realType) (p : nat -> R) (q x : R) :
  (0 < x)%R -> extended_order_limit (fun n => (p n)%:E) q%:E ->
  extended_order_limit (fun n => (real_power x (p n))%:E) (real_power x q)%:E.
Proof.
move=> hx hl; rewrite real_power_positive_base //.
have he : (fun n => (real_power x (p n))%:E) =
    (fun n => (RealExponential.exponential (RealExponential.logarithm x * p n)%R)%:E).
  apply/funext=> n; by rewrite real_power_positive_base // mulrC.
rewrite he [(q * _)%R]mulrC; apply: real_exponential_order_limit.
exact: real_scalar_order_limit.
Qed.
