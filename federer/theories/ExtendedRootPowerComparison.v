(** Federer (1969), 3.2.41, printed pp. 277--278:
    raise a finite nonnegative root bound to its positive
    power, then undo that power after passing to the compact
    tube-volume limit. Infinite target volumes are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import RealPower ExtendedPositivePower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [extended_root_power_lower_comparison]: supporting
    equivalent powered form of the Brunn--Minkowski bound in
    Federer 3.2.41, pp. 277--278. Positive real p generalizes
    the printed positive integer n, and the outer target x may
    be infinite. Zero q is included with its actual power zero. *)
Lemma extended_root_power_lower_comparison (R:realType) (x : \bar R) (p q:R):
  (0<=x)%E ->0<p ->0<=q ->
  ((q%:E<=extended_positive_power x p^-1)%E <->
    ((real_power q p)%:E<=x)%E).
Proof.
move=> hx hp hq.
have hpi:0<p^-1 by rewrite invr_gt0.
have hqE:(0<=q%:E)%E by rewrite lee_fin.
split.
- move=> hRoot.
  have hRaised:=@extended_positive_power_monotone R q%:E (extended_positive_power x p^-1) p
    hqE hRoot hp.
  have hCancel:extended_positive_power (extended_positive_power x p^-1) p=x.
    have h:=@extended_positive_power_root_cancel R x p^-1 hx hpi.
    by rewrite invrK in h.
  by rewrite hCancel /extended_positive_power in hRaised.
- move=> hPower.
  have hPower0:(0<=(real_power q p)%:E)%E by rewrite lee_fin real_power_nonnegative.
  have hRaised:=@extended_positive_power_monotone R (real_power q p)%:E x p^-1
    hPower0 hPower hpi.
  change (is_true ((real_power (real_power q p) p^-1)%:E<=extended_positive_power x p^-1)%E) in hRaised.
  by rewrite (real_power_root_cancel hq hp) in hRaised.
Qed.
