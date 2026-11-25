(** Federer (1969), 2.10.29, p. 194, displayed recursions
    s_j=s_(j-1)*n_j^(-1/m) and its second-factor analogue: derive the
    explicit child-length formula from the equal-cost laws of 2.10.28(4), p.
    192. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealPower RealPowerDivision RealPowerContinuity CantorSplitRadiusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [power_cantor_inverse_root_cost]: supporting
    (n^(-1/m))^m=1/n in the scalar
    recurrence of 2.10.29, p. 194.
    The base is positive, so reciprocal
    and root cancellations are legitimate. *)
Lemma power_cantor_inverse_root_cost (R : realType) (N m : R) :
  0<N -> 0<m -> real_power (real_power N (-m^-1)) m=N^-1.
Proof.
move=> hN hm.
have hrootpos := @real_power_strictly_positive R N m^-1 hN.
rewrite real_power_negative_exponent // real_power_inverse_base //.
by rewrite real_power_inverse_power // ltW.
Qed.

(** Source for [power_cantor_split_length]: direct
    explicit child length d*n^(-1/m) used in
    2.10.29, p. 194. It is derived from
    a specified equal-cost radius, rather than
    introduced as an extra recurrence assumption.
    The positive coefficient c cancels and
    the lemma needs only m>0; the Cantor
    application further requires m<1. *)
Theorem power_cantor_split_length (R : realType) (c m d s : R) n :
  0<c -> 0<m -> 0<d -> (2<=n)%N ->
  is_cantor_split_radius (fun t=>c*real_power t m) d n s ->
  s=d*real_power n%:R (-m^-1).
Proof.
move=> hc hm hd hn hs.
have hN : (0<n%:R :> R) by rewrite ltr0n; exact: leq_trans (leqnSn 1%N) hn.
have hfactor := @real_power_nonnegative R n%:R (-m^-1).
have hc0 : c!=0 by rewrite gt_eqF.
have hcost := cantor_split_radius_cost hs.
have hexplicit : c*real_power (d*real_power n%:R (-m^-1)) m=c*real_power d m/n%:R.
  by rewrite (@real_power_product R d _ m (ltW hd) hfactor)
    (@power_cantor_inverse_root_cost R n%:R m hN hm) mulrA.
have hpow : real_power s m=real_power (d*real_power n%:R (-m^-1)) m.
  apply: (mulfI hc0); by rewrite hcost hexplicit.
exact (@real_power_injective R s (d*real_power n%:R (-m^-1)) m
  (ltW (cantor_split_radius_bounds hs).1) (mulr_ge0 (ltW hd) hfactor) hm hpow).
Qed.
