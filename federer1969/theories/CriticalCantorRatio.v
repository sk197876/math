(** Federer (1969), 3.3.20, pp. 306 and 308:
    the critical binary side ratio is exactly one quarter. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import RealPower RealPowerContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_cantor_binary_ratio]: substituting
    m=1/2 in the actual printed 2^(-1/m)
    side ratio of 3.3.20 gives 1/4. This
    uses the actual real-power laws; no alternative
    critical Cantor construction is introduced. *)
Lemma critical_cantor_binary_ratio (R:realType):
  real_power (2:R) (-((1:R)/2)^-1)=(4:R)^-1.
Proof.
have hHalf:((1:R)/2)^-1= 2 by field.
have hTwo:(0<2:>R) by rewrite ltr0n.
have hFour:(2:R)^+2= 4 by ring.
by rewrite hHalf (@real_power_negative_exponent R 2 2 hTwo)
  (@real_power_two R 2 (ltW hTwo)) hFour.
Qed.
