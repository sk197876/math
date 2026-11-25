(** Federer (1969), 3.4.6, p. 323: the
    original absolute shifted double series has its printed
    quantitative bound, with finite tails retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import WeierstrassShiftedTermBound WeierstrassRectangularBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_shifted_absolute_rectangle]:
    every original shifted absolute rectangle, including
    either tail, is bounded by alpha*(2 beta)^s times
    the two geometric powers and inverse gaps,
    3.4.6, p. 323. The original n=p=0
    case is the displayed infinite-series majorant;
    finite tail bounds justify its limiting use. *)
Theorem weierstrass_shifted_absolute_rectangle (R:realType) (alpha beta gamma rho t:R)
    (q:nat->nat->R):
  0<alpha ->0<beta ->0<gamma ->0<=rho ->2*beta*`|t|<1 ->gamma*rho<1 ->
  (forall i j,`|q i j|<=alpha*beta^+i*gamma^+j*rho^+j) ->
  forall s n p I J,
    (\sum_(i<I) \sum_(j<J) `|('C(s+(n+i),s))%:R*t^+(n+i)*q (s+(n+i))%N (p+j)%N|)<=
      alpha*(2*beta)^+s*(2*beta*`|t|)^+n*(gamma*rho)^+p/
        (1-2*beta*`|t|)/(1-gamma*rho).
Proof.
move=>hAlpha hBeta hGamma hRho hT hR hQ s n p I J.
pose u:=2*beta*`|t|.
pose w:=gamma*rho.
pose D:=alpha*(2*beta)^+s*u^+n*w^+p.
have hu:0<=u:=mulr_ge0 (mulr_ge0 (ler0n R 2) (ltW hBeta)) (normr_ge0 t).
have hw:0<=w:=mulr_ge0 (ltW hGamma) hRho.
have hD:0<=D:=mulr_ge0 (mulr_ge0 (mulr_ge0 (ltW hAlpha)
  (exprn_ge0 s (mulr_ge0 (ler0n R 2) (ltW hBeta)))) (exprn_ge0 n hu)) (exprn_ge0 p hw).
have hMajorant:(\sum_(i<I) \sum_(j<J) `|('C(s+(n+i),s))%:R*t^+(n+i)*q (s+(n+i))%N (p+j)%N|)<=
    \sum_(i<I) \sum_(j<J) D*u^+i*w^+j.
  apply:ler_sum=>i _;apply:ler_sum=>j _.
  have hTerm:=@weierstrass_shifted_term_bound R alpha beta gamma rho t q
    hAlpha hBeta hGamma hRho hQ s (n+i)%N (p+j)%N.
  have hIdentity:alpha*(2*beta)^+s*(2*beta*`|t|)^+(n+i)*(gamma*rho)^+(p+j)=D*u^+i*w^+j.
    by rewrite /D /u /w !exprD;ring.
  by rewrite hIdentity in hTerm.
apply:le_trans hMajorant _.
exact:(@weierstrass_rectangular_geometric_bound R D u w I J hD hu hT hw hR).
Qed.
