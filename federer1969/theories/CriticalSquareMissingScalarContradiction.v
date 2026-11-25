(** Federer (1969), 3.3.20, pp. 308–309:
    the four successive missing-count squeezes. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import FourAdicPositiveBracket.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_square_missing_scalar_contradiction]:
    the exact final scalar contradiction on pp. 308–309.
    The input inequalities are the printed Omega consequences
    for actual missing counts, proved geometrically downstream.
    The successive thresholds 8,20,14,10 and coefficients
    5,14,19/2,8 remain exactly those in the book.
    This helper does not assume any density or measure bound. *)
Theorem critical_square_missing_scalar_contradiction (R:realType) (sigma:R)
    (r:nat->nat):
  0<sigma ->sigma<= 1/2 ->
  (forall j,(1<=j)%N ->(r j)%:R<(4:R)^+j*sigma) ->
  (forall j,(2<=j)%N ->(r j<8)%N ->sigma<= 5/(4:R)^+j) ->
  (forall j,(3<=j)%N ->(r j<20)%N ->sigma<= 14/(4:R)^+j) ->
  (forall j,(3<=j)%N ->(r j<14)%N ->sigma<=(19/2)/(4:R)^+j) ->
  (forall j,(3<=j)%N ->(r j<10)%N ->sigma<= 8/(4:R)^+j) ->False.
Proof.
move=>hSigma hHalf hMissing hEight hTwenty hFourteen hTen.
have [k [hk [hLower hUpper]]]:=@four_adic_positive_bracket R sigma hSigma hHalf.
pose p:=(4:R)^+k.
have hp:0<p by rewrite /p exprn_gt0 // ltr0n.
have hp4:0<4* p by nra.
have hp16:0<16* p by nra.
have hPower1:(4:R)^+k.+1= 4* p by rewrite exprS.
have hPower2:(4:R)^+k.+2= 16* p by rewrite exprS hPower1;ring.
rewrite hPower1 in hLower.
change (is_true (sigma<= 2/p)) in hUpper.
have hLowerProduct:2<sigma*(4* p) by move:hLower;rewrite ltr_pdivrMr.
have hUpperProduct:sigma* p<= 2 by move:hUpper;rewrite ler_pdivlMr.
have hk1:(1<=k.+1)%N by [].
have hk2:(2<=k.+1)%N by rewrite ltnS.
have hk3:(3<=k.+2)%N by rewrite !ltnS.
have hMiss1:=hMissing k.+1 hk1;rewrite hPower1 in hMiss1.
have hR8:(r k.+1<8)%N.
  have h:(r k.+1)%:R<(8:R) by nra.
  by move:h;rewrite ltr_nat.
have hFive:=hEight k.+1 hk2 hR8.
rewrite hPower1 ler_pdivlMr // in hFive.
have hMiss2:=hMissing k.+2 (leq_trans (erefl true:(1<= 3)%N) hk3).
rewrite hPower2 in hMiss2.
have hR20:(r k.+2<20)%N.
  have h:(r k.+2)%:R<(20:R) by nra.
  by move:h;rewrite ltr_nat.
have hBound14:=hTwenty k.+2 hk3 hR20.
rewrite hPower2 ler_pdivlMr // in hBound14.
have hR14:(r k.+2<14)%N.
  have h:(r k.+2)%:R<(14:R) by nra.
  by move:h;rewrite ltr_nat.
have hBoundHalf:=hFourteen k.+2 hk3 hR14.
rewrite hPower2 ler_pdivlMr // in hBoundHalf.
have hR10:(r k.+2<10)%N.
  have h:(r k.+2)%:R<(10:R) by nra.
  by move:h;rewrite ltr_nat.
have hFinal:=hTen k.+2 hk3 hR10.
rewrite hPower2 ler_pdivlMr // in hFinal.
nra.
Qed.
