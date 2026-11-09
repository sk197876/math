(** Federer (1969), 3.4.5, p. 321: bounded
    multiples of the actual flat coefficient are negligible
    relative to every positive-side power. The estimates use
    the proved flat exponential of 3.1.11, p. 223. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import FlatExponentialUP FlatExponentialSealed FlatExponentialPowerBound
  ScalarRightLittleOPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [bounded_flat_exponential_right_decay]: the
    actual power decay in the flat-coefficient argument
    supporting the example cited at 3.4.5, p. 321.
    The finite multiplier is arbitrary and is not a
    hidden vanishing or analyticity hypothesis. *)
Theorem bounded_flat_exponential_right_decay (R:realType) (f:R->R) (C r:R):
  0<=C ->0<r ->
  (forall t:R,0<t<r ->`|f t|<=C*FlatExponential.value t) ->
  forall m,scalar_right_little_o_power f m.
Proof.
move=>hC hr hBound m epsilon hEpsilon.
pose n:=m.+1.
pose K:R:=C*n%:R^+n.
have hK:0<=K:=mulr_ge0 hC (exprn_ge0 n (ler0n R n)).
have hDen:0<K+1 by rewrite addrC ltr_pwDl.
pose delta:R:=Num.min r (Num.min 1 (epsilon/(K+1))).
have hDelta:0<delta by rewrite /delta !lt_min hr ltr01 divr_gt0.
exists delta;split;first exact:hDelta.
move=>t /andP [ht htDelta].
have hDeltaR:delta<=r by rewrite /delta ge_min lexx.
have htr:t<r:=lt_le_trans htDelta hDeltaR.
have hDeltaOther:delta<=Num.min 1 (epsilon/(K+1)) by rewrite /delta ge_min lexx orbT.
have htOther:t<Num.min 1 (epsilon/(K+1)):=lt_le_trans htDelta hDeltaOther.
have [htOne htRatio]:t<1 /\t<epsilon/(K+1).
  by move:htOther;rewrite lt_min=>/andP[].
have hE:=@flat_exponential_power_bound R n t (leq0n m) ht.
rewrite -(flat_exponential_positive_value (@FlatExponential.laws R) ht) in hE.
apply:le_trans (hBound t (introT andP (conj ht htr))) _.
apply:le_trans (ler_wpM2l hC hE) _.
have hDegree:(2 * n=m+(m.+2))%N by rewrite /n mul2n -addnn !addnS !addSn.
rewrite hDegree exprD.
have hTail:t^+m.+2<=t.
  rewrite exprS;have hPower:t^+m.+1<=1:=exprn_ile1 m.+1 (ltW ht) (ltW htOne).
  have hh:=ler_wpM2l (ltW ht) hPower;by rewrite mulr1 in hh.
have hKT:K*t<=epsilon.
  have hProduct:t*(K+1)<epsilon by move:htRatio;rewrite ltr_pdivlMr // mulrC.
  nra.
have hTailBound:=ler_wpM2l hK hTail.
have hCoefficient:K*t^+m.+2<=epsilon:=le_trans hTailBound hKT.
have hResult:=ler_wpM2r (exprn_ge0 m (ltW ht)) hCoefficient.
have hIdentity:C*(n%:R^+n*(t^+m*t^+m.+2))=(K*t^+m.+2)*t^+m by rewrite /K;ring.
by rewrite hIdentity.
Qed.
