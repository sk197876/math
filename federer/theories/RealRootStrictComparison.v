(** Federer (1969), 3.2.41, printed p. 278, compact
    inner approximation: a strict root threshold corresponds
    to a strict powered mass threshold. The scalar power laws
    are those already proved for 2.4.12, pp. 86--87. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower RealPowerContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_root_strict_power_comparison]: supporting
    strict compact mass thresholds in Federer 3.2.41, p. 278.
    Every nonnegative a,q and positive real p are allowed,
    including the zero-base boundary of the original power laws. *)
Lemma real_root_strict_power_comparison (R:realType) (a p q:R):
  0<=a ->0<p ->0<=q ->
  (q<real_power a p^-1 <->real_power q p<a).
Proof.
move=> ha hp hq.
have hi:0<p^-1 by rewrite invr_gt0.
split.
- move=> hRoot.
  have h:=@real_power_strict_monotone R q (real_power a p^-1) p hq hRoot hp.
  by rewrite (real_power_inverse_power ha hp) in h.
- move=> hPower.
  have h:=@real_power_strict_monotone R (real_power q p) a p^-1
    (real_power_nonnegative q p) hPower hi.
  by rewrite (real_power_root_cancel hq hp) in h.
Qed.
