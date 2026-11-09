(** Federer (1969), 3.4.6, p. 323: geometrically
    bounded double homogeneous coefficients produce an actual
    analytic germ with exactly the original grouped coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP HomogeneousPolynomialFunctions AnalyticGermUP
  WeierstrassGroupedUP WeierstrassGroupedHomogeneous WeierstrassGroupedBounds WeierstrassHomogeneousRealisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [weierstrass_grouped_germ_exists]: the
    analyticity assertion for the original double series in
    3.4.6, p. 323. Actual polynomial grouping,
    finite norm bounds and the proved analytic-series
    realisation establish existence from the coefficient bounds. *)
Theorem weierstrass_grouped_germ_exists (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (xi:Hom X R^o) (projection:Hom X K) (q:nat->nat->K->R) (A B C:R):
  0<A ->0<B ->0<C ->
  norm_bounded_linear NX (fun r:R^o=>`|r|) xi ->norm_bounded_linear NX NK projection ->
  (forall i j,@is_homogeneous_polynomial R K R^o j (q i j)) ->
  (forall i j z,NK z<=1 ->`|q i j z|<=A*B^+i*C^+j) ->
  exists alpha:analytic_germ_space hNX (0:X),is_weierstrass_grouped_germ xi projection q alpha.
Proof.
move=>hA hB hC hXi hProjection hQ hBound.
have [c [hc hGrouped]]:=@weierstrass_grouped_geometric_bound R X K NX NK hNX hNK
  xi projection q A B C hA hB hC hXi hProjection hQ hBound.
exact:(@weierstrass_homogeneous_germ_exists R X NX hNX
  (fun m x=>\sum_(i<m.+1) (xi x)^+i*q i (m-i)%N (projection x)) A c hA hc
  (fun m=>@weierstrass_grouped_homogeneous R X K xi projection q m hQ) hGrouped).
Qed.
