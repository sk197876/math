(** Federer (1969), 3.3.21, p. 309: positive original gap independent of the subdivision count. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealPower RealPowerContinuity RealPowerSuccessor RealPowerExponentOrder
  RealExponentialUP RealExponentialSealed RealExponentialLaws CantorSplitRadiusUP CantorSplitRadius
  PowerCantorSplit BinaryCantorRatioBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power_negative_base_order]: positive-base
    real powers of a nonpositive exponent reverse base order,
    supporting the actual subdivision gap in 3.3.21, p. 309.
    The existing sealed logarithm and exponential laws prove it. *)
Lemma real_power_negative_base_order (R:realType) (x y p:R):
  0<x ->x<=y ->p<= 0 ->real_power y p<=real_power x p.
Proof.
move=>hx hxy hp.
have hy:0<y:=lt_le_trans hx hxy.
have hLog:RealExponential.logarithm x<=RealExponential.logarithm y
  by rewrite real_logarithm_order.
rewrite (@real_power_positive_base R y p hy) (@real_power_positive_base R x p hx) real_exponential_order.
nra.
Qed.

(** Source for [power_cantor_uniform_gap_positive]: the actual
    fixed scalar kappa= 1-2*2^(-1/m) lies strictly between zero
    and one for every original 0<m<1, supporting 3.3.21, p. 309. *)
Lemma power_cantor_uniform_gap_positive (R:realType) (m:R):
  0<m ->m<1 ->0<1-2 * real_power 2 (-m^-1)<1.
Proof.
move=>hm hm1;have /andP[h0 h1]:=(binary_cantor_original_ratio_bounds hm hm1).1.
apply/andP;split;lra.
Qed.

(** Source for [power_cantor_subdivision_retained_fraction]: all
    original children together occupy at most the same strict fraction
    2*2^(-1/m) of their parent side, supporting the uniform actual
    separation in 3.3.21, p. 309. No large-n hypothesis is imposed. *)
Lemma power_cantor_subdivision_retained_fraction (R:realType) (m:R) n:
  0<m ->m<1 ->(2<=n)%N ->
  n%:R * real_power n%:R (-m^-1)<= 2 * real_power 2 (-m^-1).
Proof.
move=>hm hm1 hn.
have hN:0<(n%:R:R) by rewrite ltr0n;exact:leq_trans (leqnSn 1) hn.
have hN2:(2:R)<=n%:R by rewrite ler_nat.
have hTwo:0<(2:R) by rewrite ltr0n.
have hInverse:1<m^-1 by rewrite invf_gt1 //.
have hExponent:1-m^-1<= 0 by lra.
have hPower x:0<x ->x * real_power x (-m^-1)=real_power x (1-m^-1).
  move=>hx;by rewrite real_power_add_exponents_positive // real_power_one_exponent ?ltW.
rewrite !hPower //.
exact:real_power_negative_base_order hTwo hN2 hExponent.
Qed.

(** Source for [power_cantor_original_child_gap_bounds]: the actual
    original spacing-minus-child-width is at least kappa*d/n and
    at least kappa*s, uniformly at every original positive parent,
    supporting 3.3.21, p. 309. Exact Phi spacing and the proved
    retained-fraction bound discharge every uniform-gap premise. *)
Theorem power_cantor_original_child_gap_bounds (R:realType) (c m d s:R) n:
  0<c ->0<m ->m<1 ->0<d ->(2<=n)%N ->
  is_cantor_split_radius (fun t=>c * real_power t m) d n s ->
  let k:= 1-2 * real_power 2 (-m^-1) in
  k * d/n%:R<=cantor_split_spacing d n s-s /\
  k * s<=cantor_split_spacing d n s-s.
Proof.
move=>hc hm hm1 hd hn hSplit k.
have hS:0<s:=(cantor_split_radius_bounds hSplit).1.
have hN1:1<(n%:R:R) by rewrite ltr1n.
have hN:0<(n%:R:R) by lra.
have hDen:0<(n%:R:R)-1 by lra.
have /andP[hk hk1]:=power_cantor_uniform_gap_positive hm hm1.
change (is_true (0<k)) in hk.
have hRetain:=power_cantor_subdivision_retained_fraction hm hm1 hn.
have hExact:=@power_cantor_split_length R c m d s n hc hm hd hn hSplit.
have hOccupied:(n%:R:R) * s<=d * (1-k).
  rewrite hExact /k;have hScaled:=ler_wpM2l (ltW hd) hRetain;nra.
have hGap:cantor_split_spacing d n s-s=(d-n%:R * s)/(n%:R-1).
  rewrite /cantor_split_spacing;field;by rewrite ?gt_eqF //.
rewrite hGap.
have hNumerator:k * d<=d-n%:R * s by nra.
have hFirst:k * d/n%:R<=(d-n%:R * s)/(n%:R-1).
  have hInverse:(n%:R:R)^-1<=(n%:R-1)^-1.
    by rewrite lef_pV2 ?posrE //;lra.
  have hLower:k * d/n%:R<=k * d/(n%:R-1).
    apply:ler_wpM2l;[exact:mulr_ge0 (ltW hk) (ltW hd)|exact:hInverse].
  apply:le_trans hLower _.
  by rewrite ler_pM2r ?invr_gt0.
split;first exact:hFirst.
have hsBound:s<=d/n%:R:=ltW (cantor_split_radius_bounds hSplit).2.
apply:le_trans _ hFirst.
by rewrite -mulrA (ler_pM2l hk).
Qed.
