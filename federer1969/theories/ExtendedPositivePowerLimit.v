(** Federer (1969), 2.4.12, p. 87: passage to positive powers in the
    lower-semicontinuity argument. Supporting scalar continuity is proved
    from the inverse-power order laws, including infinite limits, rather
    than imported as an external integration or Lp theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit ExtendedPositivePower ExtendedPositivePowerOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_positive_power_order_limit]: scalar
    continuity supporting Federer 2.4.12, p. 87, where
    Fatou's lemma is applied to norms raised to a positive
    power. The sequence and limit are nonnegative; positive
    infinity is allowed. *)
Lemma extended_positive_power_order_limit (R : realType) (u : nat -> \bar R)
    (l : \bar R) (p : R) :
  (forall n, 0 <= u n) -> 0 <= l -> (0 < p)%R ->
  extended_order_limit u l ->
  extended_order_limit (fun n => extended_positive_power (u n) p)
    (extended_positive_power l p).
Proof.
move=> hu hl hp [hlow hupp].
have hi : (0 < p^-1)%R by rewrite invr_gt0.
split.
- move=> a ha; have [ha0|ha0] := leP 0 a.
  + have he := @extended_positive_power_strict_order R a (extended_positive_power l p)
      p^-1 ha0 (extended_positive_power_nonnegative l p) hi.
    rewrite extended_positive_power_root_cancel // in he.
    have ha' : extended_positive_power a p^-1 < l by rewrite he.
    have [k hk] := hlow _ ha'; exists k=> n hn.
    have he' := @extended_positive_power_strict_order R
      (extended_positive_power a p^-1) (u n) p
      (extended_positive_power_nonnegative a p^-1) (hu n) hp.
    rewrite extended_positive_power_inverse_cancel // in he'.
    by rewrite he'; exact: hk n hn.
  + exists 0%N=> n _.
    exact: lt_le_trans ha0 (extended_positive_power_nonnegative (u n) p).
- move=> b hb.
  have hb0 : 0 <= b := le_trans (extended_positive_power_nonnegative l p) (ltW hb).
  have he := @extended_positive_power_strict_order R (extended_positive_power l p) b
    p^-1 (extended_positive_power_nonnegative l p) hb0 hi.
  rewrite extended_positive_power_root_cancel // in he.
  have hb' : l < extended_positive_power b p^-1 by rewrite he.
  have [k hk] := hupp _ hb'; exists k=> n hn.
  have he' := @extended_positive_power_strict_order R (u n)
    (extended_positive_power b p^-1) p (hu n)
    (extended_positive_power_nonnegative b p^-1) hp.
  rewrite extended_positive_power_inverse_cancel // in he'.
  by rewrite he'; exact: hk n hn.
Qed.
