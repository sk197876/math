(** Federer (1969), 3.4.6, p. 324: the finite geometric
    estimates used in the original quotient coefficient induction. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bounds.
Variable R:realType.

(** Source for [weierstrass_finite_geometric_bound]: bound
    the original finite convolution by the full geometric
    majorant, supporting the displayed induction in 3.4.6,
    p. 324. The estimate holds also for an empty sum. *)
Lemma weierstrass_finite_geometric_bound (c beta:R) n:
  0<c ->c<beta ->
  (\sum_(mu<n) beta^+mu*c^+(n-mu))<=c*beta^+n/(beta-c).
Proof.
move=>hc hBeta.
have hb:0<beta:=lt_trans hc hBeta.
have hGap:0<beta-c by rewrite subr_gt0.
elim:n=>[|n ih].
  rewrite big_ord0 expr0 mulr1;exact:ltW (divr_gt0 hc hGap).
have hSum:(\sum_(mu<n.+1) beta^+mu*c^+(n.+1-mu))=
    c*(\sum_(mu<n) beta^+mu*c^+(n-mu))+c*beta^+n.
  rewrite big_ord_recr /= subSn // subnn expr1 [beta^+n*c]mulrC.
  congr (_+_).
  rewrite mulr_sumr;apply:eq_bigr=>mu _.
  have hMu:(mu<=n)%N:=ltnW (ltn_ord mu).
  rewrite subSn // exprS;ring.
have hBound:=ler_wpM2l (ltW hc) ih.
rewrite hSum.
apply:le_trans (lerD hBound (lexx (c*beta^+n))) _.
have hIdentity:c*(c*beta^+n/(beta-c))+c*beta^+n=
    c*beta^+n.+1/(beta-c).
  rewrite exprS;field;exact:lt0r_neq0 hGap.
by rewrite hIdentity.
Qed.

(** Source for [weierstrass_closed_geometric_bound]: the
    finite sum with both endpoints retained has the upper
    bound beta^(n+1)/(beta-c), used for the first factor
    of the double sum in 3.4.6, p. 324. *)
Lemma weierstrass_closed_geometric_bound (c beta:R) n:
  0<c ->c<beta ->
  (\sum_(mu<n.+1) beta^+mu*c^+(n-mu))<=beta^+n.+1/(beta-c).
Proof.
move=>hc hBeta.
have hh:=@weierstrass_finite_geometric_bound c beta n.+1 hc hBeta.
have hSum:(\sum_(mu<n.+1) beta^+mu*c^+(n.+1-mu))=
    c*(\sum_(mu<n.+1) beta^+mu*c^+(n-mu)).
  rewrite mulr_sumr;apply:eq_bigr=>mu _.
  have hMu:(mu<=n)%N by have:=ltn_ord mu;rewrite ltnS.
  rewrite subSn // exprS;ring.
rewrite hSum in hh.
have hRight:c*beta^+n.+1/(beta-c)=c*(beta^+n.+1/(beta-c)) by ring.
rewrite hRight (ler_pM2l hc) in hh;exact:hh.
Qed.
End Bounds.
