(** Federer (1969), 3.1.24, p. 240: the positive
    square root in the explicit quadratic inverse majorant.
    Its differential is proved here from its algebraic laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormHigherCurveDerivativeUP NormedPrimitiveCell.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_square_root_remainder]: supporting the
    square root in Federer 3.1.24, p. 240. Rationalizing
    the two differences gives an exact quadratic remainder;
    both arguments are positive, so the denominators are nonzero. *)
Lemma scalar_square_root_remainder (R:realType) (a h:R) :
  0<a -> 0<a+h ->
  Num.sqrt (a+h)-Num.sqrt a-h/(2*Num.sqrt a)=
    -(h^+2)/(2*Num.sqrt a*(Num.sqrt (a+h)+Num.sqrt a)^+2).
Proof.
move=>ha hah.
pose s:=Num.sqrt a; pose t:=Num.sqrt (a+h).
have hs:0<s by rewrite /s sqrtr_gt0.
have ht:0<t by rewrite /t sqrtr_gt0.
have hs2:s^+2=a:=sqr_sqrtr (ltW ha).
have ht2:t^+2=a+h:=sqr_sqrtr (ltW hah).
have h0:s!=0 by rewrite gt_eqF.
have h1:t+s!=0 by rewrite gt_eqF //; exact: addr_gt0.
have h2:(2:R)!=0 by rewrite pnatr_eq0.
change (t-s-h/(2*s)= -(h^+2)/(2*s*(t+s)^+2)).
have he:h= t^+2-s^+2 by rewrite ht2 hs2; ring.
rewrite he; by field; rewrite h0 h1.
Qed.

(** Source for [scalar_square_root_differential]: the positive
    square root is differentiable with derivative 1/(2 sqrt a),
    supporting the analytic quadratic inverse in Federer 3.1.24,
    p. 240. This proves the epsilon remainder directly;
    no external calculus theorem is imported. *)
Theorem scalar_square_root_differential (R:realType) (a:R) :
  0<a -> has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    (fun t=>0<t) Num.sqrt a
    (@scalar_coefficient_linear_map R R^o ((2*Num.sqrt a)^-1)).
Proof.
move=>ha.
pose s:=Num.sqrt a.
have hs:0<s by rewrite /s sqrtr_gt0.
have hsn:0<=s:=ltW hs.
have hs3:0<s^+3:=exprn_gt0 _ hs.
constructor.
- exists a; split; first exact ha.
  move=>h hh; have hl:=ler_norm (-h); rewrite normrN in hl; lra.
- exact: scalar_coefficient_linear_bound (@scalar_absolute_value_norm R) _.
- move=>e he; exists (e*s^+3); split; first exact: mulr_gt0.
  move=>h hah hh.
  pose t:=Num.sqrt (a+h).
  have htn:0<=t:=sqrtr_ge0 _.
  have hsum:0<t+s by lra.
  have hden:0<2*s*(t+s)^+2 by rewrite !mulr_gt0 ?ltr0n ?exprn_gt0.
  have hlow:s^+3<=2*s*(t+s)^+2.
    have hl:=ler_wpM2l hsn (ler_wpM2r hsn htn).
    rewrite !exprS expr0; nra.
  change (`|Num.sqrt (a+h)-Num.sqrt a-h*(2*s)^-1|<=e*`|h|).
  rewrite (scalar_square_root_remainder ha hah) normf_div normrN normrX (ger0_norm (ltW hden)).
  rewrite ler_pdivrMr //.
  have hcoef:`|h|<=e*(2*s*(t+s)^+2).
    exact (le_trans (ltW hh) (ler_wpM2l (ltW he) hlow)).
  have hp:=ler_wpM2r (normr_ge0 h) hcoef.
  change (`|h|^+2<=e*`|h|*(2*s*(t+s)^+2)).
  rewrite expr2; nra.
Qed.
