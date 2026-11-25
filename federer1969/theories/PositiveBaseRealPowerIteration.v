(** Federer (1969), 3.3.21, p. 309: exact positive-base exponent cancellation for the original density quotient. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import ring.
From Federer Require Import RealPower RealExponentialUP RealExponentialSealed RealExponentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_base_real_power_iteration]: for a positive
    actual base, iterated real powers multiply arbitrary real
    exponents. This supports the inverse-root width cancellation in
    3.3.21, p. 309; no negative base or zero-base convention is
    involved. The existing sealed logarithm and exponential laws suffice. *)
Lemma positive_base_real_power_iteration (R:realType) (x p q:R):
  0<x ->real_power (real_power x p) q=real_power x (p * q).
Proof.
move=>hx.
have hInner:0<real_power x p:=real_power_strictly_positive p hx.
rewrite (@real_power_positive_base R (real_power x p) q hInner)
  (@real_power_positive_base R x p hx)
  (@real_power_positive_base R x (p * q) hx)
  (real_logarithm_exponential (@RealExponential.laws R)).
congr (RealExponential.exponential _);ring.
Qed.
