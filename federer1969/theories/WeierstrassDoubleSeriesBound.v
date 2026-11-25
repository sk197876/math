(** Federer (1969), 3.4.6, p. 323: the
    original polynomial coefficient norm hypothesis gives
    the printed absolute shifted double-series bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP HomogeneousPolynomialFunctions WeierstrassHomogeneousFullBound
  WeierstrassShiftedAbsoluteBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_double_series_bound]: the
    displayed geometric majorant in 3.4.6, p. 323,
    for every original transverse point, every shift,
    every finite rectangle and both coordinate tails.
    The pointwise bound is proved from actual homogeneous
    polynomial unit-ball bounds, rather than assumed. *)
Theorem weierstrass_double_series_bound (R:realType) (K:lmodType R)
    (NK:K->R) (hNK:is_real_norm NK) (q:nat->nat->K->R) (alpha beta gamma:R):
  0<alpha ->0<beta ->0<gamma ->
  (forall i j,@is_homogeneous_polynomial R K R^o j (q i j)) ->
  (forall i j z,NK z<=1 ->`|q i j z|<=alpha*beta^+i*gamma^+j) ->
  forall (t:R) z,2*beta*`|t|<1 ->gamma*NK z<1 ->forall s n p I J,
    (\sum_(i<I) \sum_(j<J) `|('C(s+(n+i),s))%:R*t^+(n+i)*q (s+(n+i))%N (p+j)%N z|)<=
      alpha*(2*beta)^+s*(2*beta*`|t|)^+n*(gamma*NK z)^+p/
        (1-2*beta*`|t|)/(1-gamma*NK z).
Proof.
move=>hAlpha hBeta hGamma hQ hBound t z hT hZ s n p I J.
apply:(@weierstrass_shifted_absolute_rectangle R alpha beta gamma (NK z) t (fun i j=>q i j z)
  hAlpha hBeta hGamma (real_seminorm_nonnegative hNK.1 z) hT hZ)=>i j.
have hFull:=@weierstrass_homogeneous_full_bound R K NK hNK j (q i j)
  (alpha*beta^+i*gamma^+j) (hQ i j) (hBound i j) z.
by rewrite [NK z^+j*(alpha*beta^+i*gamma^+j)]mulrC in hFull.
Qed.
