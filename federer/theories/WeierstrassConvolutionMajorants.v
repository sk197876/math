(** Federer (1969), 3.4.6, p. 324: the original three
    numerical majorants for the quotient coefficient recursion. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import WeierstrassFiniteGeometricBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bounds.
Variable R:realType.

(** Source for [weierstrass_shifted_geometric_bound]: the
    same-transverse-degree sum is bounded by
    c^(k+1) beta^i/(beta-c), supporting the displayed
    induction in 3.4.6, p. 324. *)
Lemma weierstrass_shifted_geometric_bound (c beta:R) i k:
  0<c ->c<beta ->
  (\sum_(mu<i) beta^+mu*c^+(i+k-mu))<=c^+k.+1*beta^+i/(beta-c).
Proof.
move=>hc hBeta.
have hSum:(\sum_(mu<i) beta^+mu*c^+(i+k-mu))=
    c^+k*(\sum_(mu<i) beta^+mu*c^+(i-mu)).
  rewrite mulr_sumr;apply:eq_bigr=>mu _.
  have hMu:(mu<=i)%N:=ltnW (ltn_ord mu).
  rewrite addnC -addnBA // exprD;ring.
have hh:=ler_wpM2l (exprn_ge0 k (ltW hc))
  (@weierstrass_finite_geometric_bound R c beta i hc hBeta).
rewrite hSum.
have hRight:c^+k*(c*beta^+i/(beta-c))=c^+k.+1*beta^+i/(beta-c).
  rewrite exprS;ring.
by rewrite hRight in hh.
Qed.

(** Source for [weierstrass_double_geometric_bound]: the
    cross-degree sum is bounded by the product of two
    original geometric majorants in 3.4.6, p. 324. *)
Lemma weierstrass_double_geometric_bound (c beta gamma:R) i j k:
  0<c ->c<beta ->c<gamma ->
  (\sum_(mu<(i+k).+1) \sum_(nu<j)
    beta^+mu*gamma^+nu*c^+(i+k-mu+j-nu))<=
    beta^+(i+k).+1*c*gamma^+j/((beta-c)*(gamma-c)).
Proof.
move=>hc hBeta hGamma.
have hSum:(\sum_(mu<(i+k).+1) \sum_(nu<j)
    beta^+mu*gamma^+nu*c^+(i+k-mu+j-nu))=
    (\sum_(mu<(i+k).+1) beta^+mu*c^+(i+k-mu))*
    (\sum_(nu<j) gamma^+nu*c^+(j-nu)).
  rewrite mulr_suml;apply:eq_bigr=>mu _.
  rewrite mulr_sumr;apply:eq_bigr=>nu _.
  have hNu:(nu<=j)%N:=ltnW (ltn_ord nu).
  rewrite -addnBA // exprD;ring.
have hFirst:=@weierstrass_closed_geometric_bound R c beta (i+k)%N hc hBeta.
have hSecond:=@weierstrass_finite_geometric_bound R c gamma j hc hGamma.
have hNonnegative:0<=\sum_(mu<(i+k).+1) beta^+mu*c^+(i+k-mu).
  apply:sumr_ge0=>mu _.
  exact:mulr_ge0 (exprn_ge0 _ (ltW (lt_trans hc hBeta))) (exprn_ge0 _ (ltW hc)).
have hSecondNonnegative:0<=c*gamma^+j/(gamma-c).
  apply:divr_ge0;first exact:mulr_ge0 (ltW hc) (exprn_ge0 j (ltW (lt_trans hc hGamma))).
  by rewrite subr_ge0;exact:ltW hGamma.
have hBound:=le_trans (ler_wpM2l hNonnegative hSecond)
  (ler_wpM2r hSecondNonnegative hFirst).
rewrite hSum.
have hRight:beta^+(i+k).+1/(beta-c)*(c*gamma^+j/(gamma-c))=
    beta^+(i+k).+1*c*gamma^+j/((beta-c)*(gamma-c)).
  rewrite invfM;ring.
by rewrite hRight in hBound.
Qed.
End Bounds.
