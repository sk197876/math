(** Federer 2.10.27, p. 191: the endpoint limit for the actual
    real-power radial integral, using the already proved continuity
    and reciprocal mesh bounds. No limiting integral is postulated. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import RealPower RealPowerContinuity RealErrorOrderLimit
  ExtendedRealOrderLimit StieltjesIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_real_power_reciprocal_limit]: supporting
    endpoint passage in the radial evaluation of Federer 2.10.27,
    p. 191. For every positive real p, (1/(n+1))^p tends to zero.
    This is the existing real-power continuity applied to the mesh. *)
Lemma positive_real_power_reciprocal_limit (R : realType) (p : R) :
  0 < p -> extended_order_limit
    (fun n : nat => (real_power (n.+1%:R)^-1 p)%:E) 0%E.
Proof.
move=> hp; apply: real_error_extended_order_limit => e he.
have hpne : p != 0 by rewrite gt_eqF.
have [d hd hBound] := @real_power_local_bound R 0 p e (lexx 0) hp he.
have [N hN] := @uniform_mesh_small R 0 1 d ler01 hd.
exists N => n hn.
have ha : (0 <= (n.+1%:R : R)^-1) by rewrite invr_ge0 ler0n.
have hsmall : `|0-(n.+1%:R : R)^-1| < d.
  rewrite sub0r normrN ger0_norm //.
  have h := hN n hn; by rewrite subr0 mul1r in h.
have h := hBound _ ha hsmall.
rewrite (@real_power_zero_base R p hpne) sub0r normrN in h.
by rewrite subr0.
Qed.
