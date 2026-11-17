(** Federer (1969), 3.4.8(11), pp. 334–335:
    small lower coefficients force every root of
    the original monic Weierstrass polynomial into
    the prescribed small interval. This scalar
    estimate supplies the nested neighbourhood argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import MonicRealPolynomialRootBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [monic_small_real_roots]:
    the bound on the original W_j roots
    used in 3.4.8(11), pp. 334–335.
    Every positive degree and every radius
    strictly between zero and one remains. *)
Theorem monic_small_real_roots (R:realType) k (b:'I_k->R) t r:
  (0<k)%N ->0<r ->r<1 ->
  (\sum_(i<k) `|b i|)<r^+k ->
  t^+k+\sum_(i<k) b i*t^+(i:nat) = 0 ->`|t|<r.
Proof.
move=>hK hR hR1 hSmall hEquation.
pose M:=\sum_(i<k) `|b i|.
have hM1:M<1:=lt_le_trans hSmall (exprn_ile1 k (ltW hR) (ltW hR1)).
have hUnit:`|t|<=1.
  have hBound:=@monic_real_polynomial_root_bound R k b t hK hEquation.
  by rewrite (max_l (ltW hM1)) in hBound.
have hEquality:t^+k = -\sum_(i<k) b i*t^+(i:nat).
  have h:=congr1 (fun x:R=>x-\sum_(i<k) b i*t^+(i:nat)) hEquation.
  by rewrite addrK sub0r in h.
have hNorm:`|t|^+k = `|\sum_(i<k) b i*t^+(i:nat)|.
  by rewrite -normrX hEquality normrN.
have hBound:`|t|^+k<=M.
  rewrite hNorm;apply:(le_trans (ler_norm_sum _ _ _)).
  apply:ler_sum=>i _;rewrite normrM normrX.
  have hPower:`|t|^+(i:nat)<=1:=exprn_ile1 i (normr_ge0 t) hUnit.
  have h:=ler_wpM2l (normr_ge0 (b i)) hPower.
  by rewrite mulr1 in h.
case:(ltP `|t| r)=>// hReverse.
have hPowerReverse:=lerXn2r k (ltW hR) (normr_ge0 t) hReverse.
have hImpossible:=le_lt_trans (le_trans hPowerReverse hBound) hSmall.
by move:hImpossible;rewrite ltxx.
Qed.
