(** Federer (1969), 3.4.4, pp. 317–318: choose
    the two Cantor degrees for any requested smaller image degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_sharpness_parameters]: the choices
    0<beta<1/k and beta<alpha/k with alpha<1,
    and the final approach to nu+(m-nu)/k in
    3.4.4, pp. 317–318. For any positive smaller
    gamma, choose beta so that nu+(m-nu)beta>gamma,
    then choose alpha between k beta and one. *)
Lemma critical_sharpness_parameters (R:realType) m nu k (gamma:R):
  (nu<m)%N ->(1<=k)%N ->0<gamma ->gamma<nu%:R+(m-nu)%:R/k%:R ->
  exists beta alpha:R,
    0<beta /\beta<1 /\beta<1/k%:R /\
    0<alpha /\alpha<1 /\beta<alpha/k%:R /\
    gamma<nu%:R+(m-nu)%:R*beta.
Proof.
move=>hNu hk hGamma hUpper.
pose delta:=(m-nu)%:R:R.
pose q:=(k%:R:R)^-1.
have hDelta:0<delta by rewrite /delta ltr0n subn_gt0.
have hK:0<(k%:R:R) by rewrite ltr0n.
have hKOne:(1:R)<=k%:R.
  change (is_true (((1%N)%:R:R)<=k%:R));by rewrite ler_nat.
have hQ:0<q by rewrite /q invr_gt0.
have hKQ:(k%:R:R)*q= 1 by rewrite /q mulfV // gt_eqF.
pose t:=(gamma-nu%:R)/delta.
have hT:t<q.
  rewrite /t ltr_pdivrMr //.
  change (is_true (gamma<nu%:R+delta*q)) in hUpper;nra.
pose b:=Num.max (0:R) t.
have hB0:0<=b by rewrite /b le_max lexx.
have hTB:t<=b by rewrite /b le_max lexx orbT.
have hBQ:b<q by rewrite /b gt_max hQ hT.
pose beta:=(b+q)/2.
pose alpha:=((k%:R:R)*beta+1)/2.
have hBetaPositive:0<beta by rewrite /beta; lra.
have hBetaBound:beta<q by rewrite /beta; lra.
have hTBeta:t<beta by rewrite /beta; lra.
have hKBeta:(k%:R:R)*beta<1 by nra.
have hKBetaPositive:0<(k%:R:R)*beta:=mulr_gt0 hK hBetaPositive.
have hQBound:q<=1 by nra.
have hAlphaPositive:0<alpha by rewrite /alpha; lra.
have hAlphaBound:alpha<1 by rewrite /alpha; lra.
have hAlphaLarge:(k%:R:R)*beta<alpha by rewrite /alpha; lra.
have hTValue:delta*t=gamma-nu%:R by rewrite /t mulrC divfK // gt_eqF.
exists beta,alpha;split;first exact:hBetaPositive.
split;first exact:lt_le_trans hBetaBound hQBound.
split;first by rewrite div1r.
split;first exact:hAlphaPositive.
split;first exact:hAlphaBound.
split.
- rewrite ltr_pdivlMr //;by rewrite mulrC.
- change (is_true (gamma<nu%:R+delta*beta));nra.
Qed.
