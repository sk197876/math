(** Federer (1969), 3.2.40, p. 276: supporting scalar
    separation estimates for 0<m<=1/2, derived from the
    original equal-cost split laws of 2.10.28, pp. 192--193. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealPower RealPowerContinuity RealPowerExponentOrder
  PowerCantorSplit CantorSplitRadiusUP CantorSplitRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [subcritical_power_cantor_child_square_bound]: supporting
    geometric gap estimate for the actual Cantor square in
    Federer 3.2.40, p. 276. At m<=1/2 the true child width
    is at most the parent width divided by n squared.
    The bound is proved from the original cost recurrence,
    rather than added to the Cantor-pair definition. *)
Lemma subcritical_power_cantor_child_square_bound (R:realType)
    (c m d s:R) (n:nat):
  0<c ->0<m ->m<=1/2 ->0<d ->(2<=n)%N ->
  is_cantor_split_radius (fun t=>c*real_power t m) d n s ->
  s<=d/(n%:R)^+2.
Proof.
move=>hc hm hmHalf hd hn hSplit.
have hn0:(0<n)%N:=leq_trans (leqnSn 1) hn.
have hN:(0<(n%:R:R)) by rewrite ltr0n.
have hN1:(1<=(n%:R:R)) by rewrite ler1n.
have hInv:(2:R)<=m^-1.
  rewrite -(ler_pM2l hm) mulfV ?gt_eqF //.
  lra.
have hExponent:(-m^-1:R)<= -2 by rewrite lerN2.
have hPower:=@real_power_exponent_order_above_one R n%:R (-m^-1) (-2) hN1 hExponent.
rewrite (@real_power_negative_exponent R n%:R 2 hN)
  (@real_power_two R n%:R (ltW hN)) in hPower.
rewrite (@power_cantor_split_length R c m d s n hc hm hd hn hSplit).
exact:(ler_wpM2l (ltW hd) hPower).
Qed.
