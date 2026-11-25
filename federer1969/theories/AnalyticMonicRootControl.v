(** Federer (1969), 3.4.8(11), pp. 334–335:
    choose the preceding prefix radius so that
    every original monic root has last-coordinate
    norm less than half the next radius.
    The actual analytic coefficients vanish at zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormAnalyticUP AnalyticZeroCoefficientSmallBall MonicSmallRealRoots.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_monic_root_radius_control]:
    the actual smaller-radius selection for each
    original Weierstrass polynomial in 3.4.8(11),
    pp. 334–335. The positive next radius
    is arbitrary; an internal subunit cutoff
    permits direct reuse of the small-root estimate. *)
Theorem analytic_monic_root_radius_control (R:realType) (X Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) k (U:set Y) (f:'I_k->Y->R^o)
    (P:Hom X Y) (xi:X->R) (D:set X):
  (0<k)%N ->U 0 ->
  (forall i,@norm_analytic R Y R^o NY (fun z:R^o=>`|z|) hNY
    (@scalar_absolute_value_norm R) U (f i)) ->
  (forall i,f i 0 = 0) ->
  (forall x,D x ->(xi x)^+k+\sum_(i<k) f i (P x)*(xi x)^+(i:nat) = 0) ->
  forall r:R,0<r ->exists s:R,0<s /\ s<r/2 /\
    forall x,D x ->NY (P x)<=s ->`|xi x|<r/2.
Proof.
move=>hK hU0 hAnalytic hZero hEquation r hr.
pose t:R:=Num.min (r/2) (1/2).
have hHalf:0<(1/2:R) by rewrite divr_gt0 // ltr0n.
have hT:0<t by rewrite /t lt_min divr_gt0 // ltr0n andbT.
have hTOne:t<1.
  have hBound:t<=1/2 by rewrite /t ge_min lexx orbT.
  lra.
have hPower:0<t^+k:=exprn_gt0 k hT.
have [d [hd hSmall]]:=@analytic_zero_coefficient_small_ball R Y NY hNY k U f (t^+k)
  hK hU0 hPower hAnalytic hZero.
pose s:R:=Num.min d (r/4).
have hS:0<s by rewrite /s lt_min hd divr_gt0 // ltr0n.
exists s;split;first exact:hS.
split.
- have hBound:s<=r/4 by rewrite /s ge_min lexx orbT.
  lra.
- move=>x hDx hPx.
  have hSD:s<=d by rewrite /s ge_min lexx.
  have [_ hSum]:=hSmall (P x) (le_trans hPx hSD).
  have hRoot:=@monic_small_real_roots R k (fun i=>f i (P x)) (xi x) t
    hK hT hTOne hSum (hEquation x hDx).
  apply:(lt_le_trans hRoot);by rewrite /t ge_min lexx.
Qed.
