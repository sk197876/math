(** Federer (1969), 3.4.6, p. 324: the three original
    quotient-recursion terms have total less than the
    proposed coefficient majorant. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import WeierstrassConvolutionMajorants.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bound.
Variable R:realType.

(** Source for [weierstrass_numerical_majorant]: the final
    strict estimate in the displayed coefficient induction,
    3.4.6, p. 324. Both finite sums have exactly
    the printed index bounds. These numerical hypotheses
    will be discharged by the proved choice of constants. *)
Theorem weierstrass_numerical_majorant (b c alpha beta gamma:R) k i j:
  0<b ->0<c ->0<alpha ->c<beta ->c<gamma ->
  b*c^+k/alpha+b*c^+k.+1/(beta-c)+
    b*c*beta^+k.+1/((beta-c)*(gamma-c))<1 ->
  b*c^+(i+j+k)+
    (\sum_(mu<i) alpha*beta^+mu*gamma^+j*b*c^+(i+k-mu))+
    (\sum_(mu<(i+k).+1) \sum_(nu<j)
      alpha*beta^+mu*gamma^+nu*b*c^+(i+k-mu+j-nu))<
    alpha*beta^+i*gamma^+j.
Proof.
move=>hb hc hAlpha hBeta hGamma hDelta.
have hB:0<beta:=lt_trans hc hBeta.
have hG:0<gamma:=lt_trans hc hGamma.
have hAlphaNZ:alpha!=0:=lt0r_neq0 hAlpha.
pose T:=alpha*beta^+i*gamma^+j.
have hT:0<T by rewrite /T !mulr_gt0 // exprn_gt0.
have hBase:b*c^+(i+j+k)<=T*(b*c^+k/alpha).
  have hI:=lerXn2r i (ltW hc) (ltW hB) (ltW hBeta).
  have hJ:=lerXn2r j (ltW hc) (ltW hG) (ltW hGamma).
  have hProd:=le_trans (ler_wpM2r (exprn_ge0 j (ltW hc)) hI)
    (ler_wpM2l (exprn_ge0 i (ltW hB)) hJ).
  have hBound:=ler_wpM2l (mulr_ge0 (ltW hb) (exprn_ge0 k (ltW hc))) hProd.
  have hLeft:b*c^+k*(c^+i*c^+j)=b*c^+(i+j+k).
    by rewrite !exprD;ring.
  have hRight:b*c^+k*(beta^+i*gamma^+j)=T*(b*c^+k/alpha).
    rewrite /T;field;exact:hAlphaNZ.
  by rewrite hLeft hRight in hBound.
have hPrefix:(\sum_(mu<i) alpha*beta^+mu*gamma^+j*b*c^+(i+k-mu))<=
    T*(b*c^+k.+1/(beta-c)).
  have hSum:(\sum_(mu<i) alpha*beta^+mu*gamma^+j*b*c^+(i+k-mu))=
      (alpha*gamma^+j*b)*(\sum_(mu<i) beta^+mu*c^+(i+k-mu)).
    rewrite mulr_sumr;apply:eq_bigr=>mu _;ring.
  have hFactor:0<=alpha*gamma^+j*b.
    exact:mulr_ge0 (mulr_ge0 (ltW hAlpha) (exprn_ge0 j (ltW hG))) (ltW hb).
  have hBound:=ler_wpM2l hFactor
    (@weierstrass_shifted_geometric_bound R c beta i k hc hBeta).
  have hRight:alpha*gamma^+j*b*(c^+k.+1*beta^+i/(beta-c))=
      T*(b*c^+k.+1/(beta-c)) by rewrite /T;ring.
  rewrite hSum;by rewrite hRight in hBound.
have hCross:(\sum_(mu<(i+k).+1) \sum_(nu<j)
      alpha*beta^+mu*gamma^+nu*b*c^+(i+k-mu+j-nu))<=
    T*(b*c*beta^+k.+1/((beta-c)*(gamma-c))).
  have hSum:(\sum_(mu<(i+k).+1) \sum_(nu<j)
      alpha*beta^+mu*gamma^+nu*b*c^+(i+k-mu+j-nu))=
      (alpha*b)*(\sum_(mu<(i+k).+1) \sum_(nu<j)
        beta^+mu*gamma^+nu*c^+(i+k-mu+j-nu)).
    rewrite mulr_sumr;apply:eq_bigr=>mu _.
    rewrite mulr_sumr;apply:eq_bigr=>nu _;ring.
  have hBound:=ler_wpM2l (mulr_ge0 (ltW hAlpha) (ltW hb))
    (@weierstrass_double_geometric_bound R c beta gamma i j k hc hBeta hGamma).
  have hRight:alpha*b*(beta^+(i+k).+1*c*gamma^+j/((beta-c)*(gamma-c)))=
      T*(b*c*beta^+k.+1/((beta-c)*(gamma-c))).
    rewrite /T !exprS exprD;ring.
  rewrite hSum;by rewrite hRight in hBound.
have hBound:=lerD (lerD hBase hPrefix) hCross.
apply:le_lt_trans hBound _.
rewrite -!mulrDr -[X in _<X]mulr1 (ltr_pM2l hT).
exact:hDelta.
Qed.
End Bound.
