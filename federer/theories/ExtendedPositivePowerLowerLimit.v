(** Federer (1969), 2.4.12, p. 87: positive roots commute with the scalar
    lower limit in the Lp lower-semicontinuity argument. This supporting
    scalar fact follows from the supremum of eventual lower bounds and
    inverse-power order laws; infinite values are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP ExtendedLowerLimitUP
  ExtendedPositivePower ExtendedPositivePowerOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_positive_power_lower_limit]: supporting
    interchange of positive powers and lower limits in Federer
    2.4.12, p. 87. The assumption of nonnegative
    terms matches the integral values in that argument. *)
Lemma extended_positive_power_lower_limit (R : realType) (u : nat -> \bar R)
    (l : \bar R) (p : R) :
  (forall n, 0 <= u n) -> (0 < p)%R -> is_extended_lower_limit u l ->
  is_extended_lower_limit (fun n => extended_positive_power (u n) p)
    (extended_positive_power l p).
Proof.
move=> hu hp hl.
have hl0 : 0 <= l.
  apply: (extended_lower_limit_eventual_bound hl); exists 0%N=> n _; exact: hu.
have hi : (0 < p^-1)%R by rewrite invr_gt0.
constructor.
- move=> b [k hk]; have [hb|hb] := leP b 0.
  + exact: le_trans hb (extended_positive_power_nonnegative l p).
  + have hb0 := ltW hb.
    have hroot : extended_positive_power b p^-1 <= l.
      apply: (extended_lower_limit_eventual_bound hl); exists k=> n hn.
      have h := @extended_positive_power_monotone R b (extended_positive_power (u n) p)
        p^-1 hb0 (hk n hn) hi.
      by rewrite extended_positive_power_root_cancel // in h.
    have h := @extended_positive_power_monotone R (extended_positive_power b p^-1) l p
      (extended_positive_power_nonnegative b p^-1) hroot hp.
    by rewrite extended_positive_power_inverse_cancel // in h.
- move=> c hc.
  have hc0 : 0 <= c.
    apply: hc; exists 0%N=> n _; exact: extended_positive_power_nonnegative.
  have hroot : l <= extended_positive_power c p^-1.
    apply: (extended_real_supremum_least hl)=> b [k hk].
    have [hb|hb] := leP b 0.
    + exact: le_trans hb (extended_positive_power_nonnegative c p^-1).
    + have hb0 := ltW hb.
      have hbc : extended_positive_power b p <= c.
        apply: hc; exists k=> n hn.
        exact (@extended_positive_power_monotone R b (u n) p hb0 (hk n hn) hp).
      have h := @extended_positive_power_monotone R (extended_positive_power b p) c
        p^-1 (extended_positive_power_nonnegative b p) hbc hi.
      by rewrite extended_positive_power_root_cancel // in h.
  have h := @extended_positive_power_monotone R l (extended_positive_power c p^-1) p hl0 hroot hp.
  by rewrite extended_positive_power_inverse_cancel // in h.
Qed.
