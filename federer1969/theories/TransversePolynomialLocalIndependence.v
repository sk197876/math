(** Federer (1969), 3.4.7, p. 325: xi is
    transcendental over the actual transverse coefficient ring.
    This local finite-polynomial argument expands the coefficient
    uniqueness proof of 3.4.6(2), p. 322, without
    a monicity or coefficient-vanishing restriction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormOpenDomainLaws NormLinearDomainLaws NormBoundedLinearTopology NormTaylorLineValues
  WeierstrassTransverseUP WeierstrassTransverseLaws WeierstrassFiniteLocalCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [transverse_polynomial_local_independence]: local
    vanishing of an actual finite transverse polynomial
    forces every original coefficient to vanish near the
    transverse origin, supporting the transcendence assertion
    in 3.4.7, p. 325. No analyticity or
    independence conclusion is supplied as a premise. *)
Theorem transverse_polynomial_local_independence (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection)
    k (f:nat->K->R) (U:set X):
  @open (real_norm_metric_space hNX) U ->U 0 ->
  (forall x,U x ->\sum_(i<k) (xi x)^+i*f i (projection x) = 0) ->
  exists B:set K,@open (real_norm_metric_space hNK) B /\B 0 /\
    forall z,B z ->forall i,(i<k)%N ->f i z = 0.
Proof.
move=>hU hOrigin hZero.
have hInterior x (hx:U x):norm_domain_interior NX U x.
  have hNeighbourhood:=hU;rewrite openE in hNeighbourhood.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).2 (hNeighbourhood x hx).
have [rho [hRho hBall]]:=hInterior 0 hOrigin.
pose B:set K:=fun z=>NK z<rho.
have hBOrigin:B 0 by rewrite /B (real_seminorm_zero hNK.1).
have hBOpen:@open (real_norm_metric_space hNK) B.
  rewrite openE=>z hz;apply:(@norm_domain_interior_neighbourhood R K NK hNK B z).1.
  have hBallOpen:=@norm_open_ball_domain_interior R K NK hNK 0 rho z.
  rewrite subr0 in hBallOpen.
  have hDomain:(fun x:K=>is_true (NK (x-0)<rho)) = B by apply:funext=>x;rewrite subr0.
  rewrite hDomain in hBallOpen;exact:hBallOpen hz.
exists B;split;first exact:hBOpen.
split;first exact:hBOrigin.
move=>z hz i hi.
have hIncluded:U (inclusion z).
  have hSmall:NX (inclusion z)<rho by rewrite (weierstrass_transverse_inclusion_norm hSplit).
  have h:=hBall (inclusion z) hSmall;by rewrite add0r in h.
have [radius [hRadius hLineBall]]:=hInterior (inclusion z) hIncluded.
have [delta [hDelta hSmall]]:=@norm_scalar_line_small_increments R X NX hNX v radius hRadius.
have hPolynomial:exists r:R,0<r /\forall t,`|t|<r ->
    (\sum_(j<k) t^+j*f j z) = \sum_(j<k) t^+j*(0:R).
  exists delta;split;first exact:hDelta.
  move=>t ht.
  have hPoint:U (inclusion z+t*:v):=hLineBall _ (hSmall t ht).
  have hEquation:=hZero (inclusion z+t*:v) hPoint.
  rewrite [inclusion z+t*:v]addrC
    (weierstrass_line_functional_coordinate hSplit)
    (weierstrass_line_transverse_coordinate hSplit) in hEquation.
  rewrite hEquation;apply:esym;apply:big1=>j _;exact:mulr0.
exact:(@weierstrass_finite_local_coefficients R k (fun j=>f j z) (fun _=>0) hPolynomial i hi).
Qed.
