(** Federer (1969), 3.4.6, p. 323: the original
    double-coefficient bounds give a geometric bound on the
    finite grouping by total degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP HomogeneousPolynomialFunctions PolynomialNorm
  PolynomialFiniteNormBound AnalyticSuccessorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_grouped_geometric_bound]: a
    finite total-degree grouping has a common geometric
    bound on the original closed unit ball, supporting the
    analyticity assertion in 3.4.6, p. 323.
    The original bounded functional and projection supply
    all map constants; no series convergence is assumed. *)
Theorem weierstrass_grouped_geometric_bound (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (xi:Hom X R^o) (projection:Hom X K) (q:nat->nat->K->R) (alpha beta gamma:R):
  0<alpha ->0<beta ->0<gamma ->
  norm_bounded_linear NX (fun r:R^o=>`|r|) xi ->norm_bounded_linear NX NK projection ->
  (forall i j,@is_homogeneous_polynomial R K R^o j (q i j)) ->
  (forall i j z,NK z<=1 ->`|q i j z|<=alpha*beta^+i*gamma^+j) ->
  exists c:R,0<c /\forall m x,NX x<=1 ->
    `|\sum_(i<m.+1) (xi x)^+i*q i (m-i)%N (projection x)|<=alpha*c^+m.
Proof.
move=>hAlpha hBeta hGamma [M [hM hXi]] [N [hN hProjection]] hQ hBound.
pose D:=1+beta*M+gamma*N.
have hBM:0<=beta*M:=mulr_ge0 (ltW hBeta) hM.
have hGN:0<=gamma*N:=mulr_ge0 (ltW hGamma) hN.
have hDOne:1<=D.
  have hh:=lerD (lerD (lexx (1:R)) hBM) hGN.
  by rewrite !addr0 in hh.
have hD:0<D:=lt_le_trans ltr01 hDOne.
have hDB:beta*M<=D.
  have hh:=lerD (lerD (@ler01 R) (lexx (beta*M))) hGN.
  by rewrite add0r addr0 in hh.
have hDG:gamma*N<=D.
  have hh:=lerD (addr_ge0 ler01 hBM) (lexx (gamma*N)).
  by rewrite add0r in hh.
have hValue i j z:`|q i j z|<=NK z^+j*(alpha*beta^+i*gamma^+j).
  have hNorm:(polynomial_norm hNK.1 (fun r:R^o=>(`|r|)%R) (q i j)<=
      (alpha*beta^+i*gamma^+j)%:E)%E.
    apply:(polynomial_norm_bound hNK.1 (fun r:R^o=>`|r|) (q i j) _).2.
    exact:hBound i j.
  exact:(@homogeneous_polynomial_finite_norm_bound R K R^o NK (fun r=>`|r|)
    hNK (@scalar_absolute_value_norm R).1 j (q i j) (hQ i j) _ hNorm z).
exists (2*D);split;first by rewrite mulr_gt0 // ltr0n.
move=>m x hx.
have hXiBound:`|xi x|<=M.
  have hh:=le_trans (hXi x) (ler_wpM2l hM hx);by rewrite mulr1 in hh.
have hProjectionBound:NK (projection x)<=N.
  have hh:=le_trans (hProjection x) (ler_wpM2l hN hx);by rewrite mulr1 in hh.
have hBX:beta*`|xi x|<=D:=le_trans (ler_wpM2l (ltW hBeta) hXiBound) hDB.
have hGP:gamma*NK (projection x)<=D:=
  le_trans (ler_wpM2l (ltW hGamma) hProjectionBound) hDG.
have hBX0:0<=beta*`|xi x| :=mulr_ge0 (ltW hBeta) (normr_ge0 _).
have hGP0:0<=gamma*NK (projection x):=
  mulr_ge0 (ltW hGamma) (real_seminorm_nonnegative hNK.1 _).
have hTerm (i:'I_m.+1):`|(xi x)^+i*q i (m-i)%N (projection x)|<=alpha*D^+m.
  have hi:(i<=m)%N by have:=ltn_ord i;rewrite ltnS.
  rewrite normrM normrX.
  have hCoefficient:=ler_wpM2l (exprn_ge0 i (normr_ge0 (xi x))) (hValue i (m-i)%N (projection x)).
  apply:le_trans hCoefficient _.
  have hI:=lerXn2r i hBX0 (ltW hD) hBX.
  have hJ:=lerXn2r (m-i)%N hGP0 (ltW hD) hGP.
  have hProduct:=le_trans (ler_wpM2r (exprn_ge0 (m-i)%N hGP0) hI)
    (ler_wpM2l (exprn_ge0 i (ltW hD)) hJ).
  have hScaled:=ler_wpM2l (ltW hAlpha) hProduct.
  have hLeft:alpha*((beta*`|xi x|)^+i*(gamma*NK (projection x))^+(m-i))=
      `|xi x|^+i*(NK (projection x)^+(m-i)*(alpha*beta^+i*gamma^+(m-i))).
    by rewrite !exprMn;ring.
  rewrite hLeft -exprD (subnKC hi) in hScaled.
  exact:hScaled.
apply:le_trans (ler_norm_sum _ _ _) _.
have hSum:(\sum_(i<m.+1) `|(xi x)^+i*q i (m-i)%N (projection x)|)<=
    \sum_(i<m.+1) alpha*D^+m.
  apply:ler_sum=>i _;exact:hTerm.
apply:le_trans hSum _.
rewrite sumr_const card_ord.
have hCount:(m.+1%:R:R)<=(2:R)^+m.
  rewrite -natrX ler_nat;exact:natural_successor_power_two_bound.
have hScaled:=ler_wpM2r (mulr_ge0 (ltW hAlpha) (exprn_ge0 m (ltW hD))) hCount.
have hRight:(2:R)^+m*(alpha*D^+m)=alpha*(2*D)^+m by rewrite exprMn;ring.
rewrite hRight [(m.+1%:R:R)*(alpha*D^+m)]mulrC in hScaled.
have hNatural:(alpha*D^+m) *+ m.+1 = alpha*D^+m * m.+1%:R :=esym (mulr_natr _ _).
rewrite hNatural;exact:hScaled.
Qed.
