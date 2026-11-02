(** Federer (1969), 2.4.17, p. 90: continuity of the integral root while its
    exponent varies. This supporting joint continuity is derived from order
    density and the abstract power laws. Zero and infinite base limits are
    included; limiting exponents are positive finite. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit ExtendedPositivePower
  ExtendedPositivePowerOrder RealPowerExponentLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_varying_power_order_limit]: supporting joint
    continuity for the varying positive root in Federer 2.4.17, p. 90 The
    proof traps the base between fixed finite thresholds and uses continuity
    in the exponent at those thresholds. *)
Lemma extended_varying_power_order_limit (R : realType)
    (u : nat -> \bar R) (p : nat -> R) (l : \bar R) (q : R) :
  (forall n, 0 <= u n) -> 0 <= l -> (forall n, (0 < p n)%R) -> (0 < q)%R ->
  extended_order_limit u l -> extended_order_limit (fun n => (p n)%:E) q%:E ->
  extended_order_limit (fun n => extended_positive_power (u n) (p n))
    (extended_positive_power l q).
Proof.
move=> hu hl hp hq [hul huh] hpl.
have hqi : (0 < q^-1)%R by rewrite invr_gt0.
split.
- move=> a ha; have [ha0|ha0] := leP 0 a.
  + have hroot : extended_positive_power a q^-1 < l.
      have he := @extended_positive_power_strict_order R a (extended_positive_power l q) q^-1
        ha0 (extended_positive_power_nonnegative l q) hqi.
      rewrite extended_positive_power_root_cancel // in he; by rewrite he.
    have [r [hrr hrl]] := @extended_rationals_order_dense R (extended_positive_power a q^-1) l hroot.
    have hr0e : 0 < (ratr r : R)%:E := le_lt_trans (extended_positive_power_nonnegative a q^-1) hrr.
    have hr0 : (0 < ratr r :> R)%R := hr0e.
    have har : a < (RealPower.real_power (ratr r : R) q)%:E.
      have he := @extended_positive_power_strict_order R (extended_positive_power a q^-1) (ratr r : R)%:E q
        (extended_positive_power_nonnegative a q^-1) (ltW hr0e) hq.
      rewrite extended_positive_power_inverse_cancel // in he; by rewrite -he in hrr.
    have hrp := @real_power_exponent_order_limit R p q (ratr r : R) (ltW hr0) hq hp hpl.
    have [k hk] := hrp.1 a har; have [j hj] := hul _ hrl.
    exists (maxn k j)=> n hn.
    apply: lt_le_trans (hk n (leq_trans (leq_maxl k j) hn)) _.
    exact: (@extended_positive_power_monotone R (ratr r : R)%:E (u n) (p n) (ltW hr0e)
      (ltW (hj n (leq_trans (leq_maxr k j) hn))) (hp n)).
  + exists 0%N=> n hn; exact: lt_le_trans ha0 (extended_positive_power_nonnegative (u n) (p n)).
- move=> b hb.
  have hb0 : 0 <= b := le_trans (extended_positive_power_nonnegative l q) (ltW hb).
  have hroot : l < extended_positive_power b q^-1.
    have he := @extended_positive_power_strict_order R (extended_positive_power l q) b q^-1
      (extended_positive_power_nonnegative l q) hb0 hqi.
    rewrite extended_positive_power_root_cancel // in he; by rewrite he.
  have [r [hlr hrr]] := @extended_rationals_order_dense R l (extended_positive_power b q^-1) hroot.
  have hr0e : 0 < (ratr r : R)%:E := le_lt_trans hl hlr.
  have hr0 : (0 < ratr r :> R)%R := hr0e.
  have hrb : (RealPower.real_power (ratr r : R) q)%:E < b.
    have he := @extended_positive_power_strict_order R (ratr r : R)%:E (extended_positive_power b q^-1) q
      (ltW hr0e) (extended_positive_power_nonnegative b q^-1) hq.
    rewrite extended_positive_power_inverse_cancel // in he; by rewrite -he in hrr.
  have hrp := @real_power_exponent_order_limit R p q (ratr r : R) (ltW hr0) hq hp hpl.
  have [k hk] := hrp.2 b hrb; have [j hj] := huh _ hlr.
  exists (maxn k j)=> n hn.
  apply: le_lt_trans _ (hk n (leq_trans (leq_maxl k j) hn)).
  exact: (@extended_positive_power_monotone R (u n) (ratr r : R)%:E (p n) (hu n)
    (ltW (hj n (leq_trans (leq_maxr k j) hn))) (hp n)).
Qed.
