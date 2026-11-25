(** Federer (1969), 2.4.17, p. 90: upper continuity at the infinity
    exponent. This supporting limit is the explicit chord bound, using the
    sealed exponential and logarithm laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal.
From Federer Require Import RealPower RealExponentialUP RealExponentialSealed
  RealScalarOrderLimits RealExponentialOrderLimit ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_interpolation_endpoint_limit]: the explicit limit
    of the multiplicative convexity bound at a reciprocal endpoint,
    supporting Federer 2.4.17, p. 90 Both endpoint values are positive; zero
    norms are handled by almost equality. *)
Lemma real_power_interpolation_endpoint_limit (R : realType) (t : nat -> R) (a b : R) :
  (0 < a)%R -> (0 < b)%R -> extended_order_limit (fun n => (t n)%:E) 0 ->
  extended_order_limit (fun n => (real_power a (1-t n)%R * real_power b (t n))%:E) a%:E.
Proof.
move=> ha hb hl.
pose A := RealExponential.logarithm a; pose B := RealExponential.logarithm b.
have hal := @real_affine_order_limit R t 0%R (B-A)%R A hl.
rewrite mulr0 addr0 in hal.
have hexp := @real_exponential_order_limit R (fun n => (A+(B-A) * t n)%R) A hal.
rewrite /A (real_exponential_logarithm (RealExponential.laws R) ha) in hexp.
have he : (fun n => (real_power a (1-t n)%R * real_power b (t n))%:E)=
    (fun n => (RealExponential.exponential (A+(B-A) * t n)%R)%:E).
  apply/funext=> n; rewrite !real_power_positive_base // -(real_exponential_add (RealExponential.laws R)).
  congr ((_ )%:E); congr (RealExponential.exponential _).
  by rewrite /A /B mulrBl mul1r mulrBl [(RealExponential.logarithm b * t n)%R]mulrC [(RealExponential.logarithm a * t n)%R]mulrC addrA addrAC.
by rewrite he.
Qed.
