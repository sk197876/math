(** Federer (1969), 3.4.8(10), p. 332:
    the original monic equation bounds its
    real roots by the sum of the
    absolute lower coefficients, or by one.
    Apply norm and ordered-power laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [monic_real_polynomial_root_bound]:
    the first-coordinate bound used for compact
    fibres in 3.4.8(10), p. 332.
    Every positive original degree is retained;
    no root-separation or coefficient-regularity premise
    is needed for this scalar inequality. *)
Theorem monic_real_polynomial_root_bound (R:realType) k (b:'I_k->R) (t:R):
  (0<k)%N ->t^+k+\sum_(i<k) b i*t^+(i:nat) = 0 ->
  `|t|<=Num.max 1 (\sum_(i<k) `|b i|).
Proof.
move=>hK hEquation.
pose M:=\sum_(i<k) `|b i|.
case:(leP `|t| 1)=>hSmall.
- apply:(le_trans hSmall);by rewrite le_max lexx.
have hNormPositive:0<`|t| :=lt_trans ltr01 hSmall.
have hAtLeastOne:1<=`|t| :=ltW hSmall.
have hEquality:t^+k = -\sum_(i<k) b i*t^+(i:nat).
  have h:=congr1 (fun x:R=>x-\sum_(i<k) b i*t^+(i:nat)) hEquation.
  by rewrite addrK sub0r in h.
have hNorm:`|t|^+k = `|\sum_(i<k) b i*t^+(i:nat)|.
  by rewrite -normrX hEquality normrN.
have hSum:`|\sum_(i<k) b i*t^+(i:nat)|<=M*`|t|^+k.-1.
  apply:(le_trans (ler_norm_sum _ _ _)).
  rewrite /M mulr_suml;apply:ler_sum=>i _.
  rewrite normrM normrX.
  apply:ler_wpM2l;first exact:normr_ge0.
  apply:(ler_weXn2l hAtLeastOne).
  have hBoundNat:forall j:nat,(j<k)%N ->(j<=k.-1)%N.
    move=>j;by rewrite -(prednK hK) ltnS.
  exact:hBoundNat (i:nat) (ltn_ord i).
have hPowerPositive:0<`|t|^+k.-1:=exprn_gt0 _ hNormPositive.
have hCancel:`|t|<=M.
  rewrite -(ler_pM2r hPowerPositive) -exprS (prednK hK) hNorm.
  exact:hSum.
apply:(le_trans hCancel);by rewrite le_max lexx orbT.
Qed.
