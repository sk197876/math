(** Federer (1969), 2.4.17, p. 90: supporting check for the
    exponent-continuity argument. Splitting by f<=1 instead of |f|<=1 fails
    at f=-2 when the exponent decreases from two to one. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower RealPowerSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [signed_exponent_split_counterexample]: Supporting check for
    the continuity claim in Federer 2.4.17, p. 90: the split must use
    absolute values. At f=-2, decreasing the exponent from two to one
    decreases the absolute power, despite f<=1. *)
Lemma signed_exponent_split_counterexample (R : realType) :
  (-2 : R) <= 1 /\ ~ (real_power `|(-2 : R)| 2 <= real_power `|(-2 : R)| 1).
Proof.
split.
- have hn : (-2 : R) <= 0 by rewrite oppr_le0 ler0n.
  exact: le_trans hn ler01.
rewrite normrN ger0_norm ?ler0n //.
have h2 : (0 <= (2 : R)) by rewrite ler0n.
have he : real_power (2 : R) 2=4.
  change (real_power (2 : R) (1+1)=4).
  by rewrite real_power_positive_successor // ?ltr01 real_power_one_exponent // -natrM.
rewrite he real_power_one_exponent // ler_nat; by [].
Qed.
