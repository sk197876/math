(** Federer (1969), 3.4.6, p. 323: finite
    geometric prefix and tail bounds for the original
    absolutely convergent shifted double series. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_geometric_prefix]: every
    original finite geometric prefix is bounded by
    (1-u) inverse, supporting 3.4.6, p. 323.
    Empty prefixes and u=0 are retained. *)
Lemma weierstrass_geometric_prefix (R:realType) (u:R) n:
  0<=u ->u<1 ->(\sum_(i<n) u^+i)<=1/(1-u).
Proof.
move=>hu hSmall.
have hGap:0<1-u by rewrite subr_gt0.
have hIdentity m:(1-u)*(\sum_(i<m) u^+i)= 1-u^+m.
  elim:m=>[|m ih];first by rewrite big_ord0 mulr0 expr0 subrr.
  by rewrite big_ord_recr /= mulrDr ih exprS;ring.
rewrite ler_pdivlMr // mulrC hIdentity.
have hPower:0<=u^+n:=exprn_ge0 n hu.
by lra.
Qed.

(** Source for [weierstrass_geometric_tail]: the original
    positive geometric tail has its quantitative bound
    u^n/(1-u), supporting all shifted series in
    3.4.6, p. 323. Both finite endpoints
    are retained without an infinite-sum assumption. *)
Lemma weierstrass_geometric_tail (R:realType) (u:R) n m:
  0<=u ->u<1 ->(\sum_(i<m) u^+(n+i))<=u^+n/(1-u).
Proof.
move=>hu hSmall.
have hIdentity:(\sum_(i<m) u^+(n+i))=u^+n*\sum_(i<m) u^+i.
  rewrite mulr_sumr;apply:eq_bigr=>i _;by rewrite exprD.
rewrite hIdentity.
have hBound:=ler_wpM2l (exprn_ge0 n hu) (@weierstrass_geometric_prefix R u m hu hSmall).
have hRight:u^+n*(1/(1-u))=u^+n/(1-u) by ring.
by rewrite hRight in hBound.
Qed.
