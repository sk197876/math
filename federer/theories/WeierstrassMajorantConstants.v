(** Federer (1969), 3.4.6, p. 324: the positive
    constants used to bound the quotient coefficient recursion.
    Their existence is proved from b,c>0; the smallness
    condition is not added as a theorem hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Constants.
Variable R:realType.

(** Source for [weierstrass_quarter_majorant]: a finite
    positive padding makes each original nonnegative coefficient
    ratio less than one quarter, supporting the choice
    of constants in 3.4.6, p. 324. *)
Lemma weierstrass_quarter_majorant (x:R):
  0<=x ->x/(4*x+1)<1/4.
Proof.
move=>hx.
have hDen:0<4*x+1 by nra.
rewrite ltr_pdivrMr //.
nra.
Qed.

(** Source for [weierstrass_majorant_constants_exist]: the
    original constants alpha>bc^k, beta>c, gamma>c can be
    chosen so that the printed sum delta is below one,
    3.4.6, p. 324. All inequalities are proved
    for explicit finite positive choices. *)
Theorem weierstrass_majorant_constants_exist (b c:R) k:
  0<b ->0<c ->exists alpha beta gamma:R,
    0<alpha /\0<beta /\0<gamma /\
    b*c^+k<alpha /\c<beta /\c<gamma /\
    b*c^+k/alpha+b*c^+k.+1/(beta-c)+
      b*c*beta^+k.+1/((beta-c)*(gamma-c))<1.
Proof.
move=>hb hc.
pose A:=b*c^+k.
pose B:=b*c^+k.+1.
have hA:0<A by rewrite /A mulr_gt0 // exprn_gt0.
have hB:0<B by rewrite /B mulr_gt0 // exprn_gt0.
pose alpha:=4*A+1.
pose beta:=c+4*B+1.
pose T:=b*c*beta^+k.+1/(beta-c).
have hBeta:0<beta by rewrite /beta;nra.
have hGap:0<beta-c by rewrite /beta;nra.
have hT:0<T by rewrite /T divr_gt0 // !mulr_gt0 // exprn_gt0.
pose gamma:=c+4*T+1.
have hGamma:0<gamma by rewrite /gamma;nra.
have hAlpha:0<alpha by rewrite /alpha;nra.
have hFirst:A/alpha<1/4:=weierstrass_quarter_majorant (ltW hA).
have hSecond:B/(beta-c)<1/4.
  have hDen:beta-c=4*B+1 by rewrite /beta;ring.
  rewrite hDen;exact:weierstrass_quarter_majorant (ltW hB).
have hThird:b*c*beta^+k.+1/((beta-c)*(gamma-c))<1/4.
  have hDen:gamma-c=4*T+1 by rewrite /gamma;ring.
  rewrite invfM mulrA -/T hDen.
  exact:weierstrass_quarter_majorant (ltW hT).
exists alpha,beta,gamma;split;first exact:hAlpha.
split;first exact:hBeta.
split;first exact:hGamma.
split;first by rewrite -/A /alpha;nra.
split;first by rewrite /beta;nra.
split;first by rewrite /gamma;nra.
change (A/alpha+B/(beta-c)+b*c*beta^+k.+1/((beta-c)*(gamma-c))<1).
nra.
Qed.
End Constants.
