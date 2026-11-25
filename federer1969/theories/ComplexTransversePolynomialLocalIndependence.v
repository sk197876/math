(** Federer (1969), 3.4.12, p. 339, extending 3.4.7,
    p. 325: the actual distinguished coordinate is transcendental
    over transverse holomorphic germs. Short real parameter lines
    and the proved normed-target finite coefficient theorem suffice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus
  ComplexScalarNorm NormMetric NormDifferentialUP NormRegularity NormOpenDomainLaws NormLinearDomainLaws
  NormBoundedLinearTopology NormTaylorLineValues ComplexWeierstrassTransverseUP ComplexWeierstrassTransverseLaws
  NormWeierstrassFiniteLocalCoefficients ComplexRealPowerSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Independence.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_complex_norm NX) (hNK:is_complex_norm NK).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation KR:=(restricted_space (ComplexScalars.embed R) K).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation hNKR:=(complex_norm_real hNK).

(** Source for [complex_transverse_polynomial_local_independence]: local
    zero of an actual finite polynomial forces every original
    coefficient to vanish near the transverse origin, extending
    3.4.7, p. 325. No analyticity or independence
    conclusion is supplied as a premise. *)
Theorem complex_transverse_polynomial_local_independence (v:X) (xi:Hom X (ComplexScalars.C R)^o)
    (inclusion:Hom K X) (projection:Hom X K)
    (hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection)
    k (f:nat->K->ComplexScalars.C R) (U:set X):
  @open (real_norm_metric_space hNXR) U ->U 0 ->
  (forall x,U x ->\sum_(i<k) (xi x)^+i*f i (projection x)=0) ->
  exists B:set K,@open (real_norm_metric_space hNKR) B /\B 0 /\
    forall z,B z ->forall i,(i<k)%N ->f i z=0.
Proof.
move=>hU hOrigin hZero.
have hInterior x (hx:U x):@norm_domain_interior R XR NX U x.
  have hNeighbourhood:=hU;rewrite openE in hNeighbourhood.
  exact:(@norm_domain_interior_neighbourhood R XR NX hNXR U x).2 (hNeighbourhood x hx).
have [rho [hRho hBall]]:=hInterior 0 hOrigin.
pose B:set K:=fun z=>NK z<rho.
have hBOrigin:B 0 by rewrite /B (real_seminorm_zero hNKR.1).
have hBOpen:@open (real_norm_metric_space hNKR) B.
  rewrite openE=>z hz;apply:(@norm_domain_interior_neighbourhood R KR NK hNKR B z).1.
  have hBallOpen:=@norm_open_ball_domain_interior R KR NK hNKR 0 rho z.
  rewrite subr0 in hBallOpen.
  have hDomain:(fun x:K=>is_true (NK (x-0)<rho))=B by apply:funext=>x;rewrite subr0.
  rewrite hDomain in hBallOpen;exact:hBallOpen hz.
exists B;split;first exact:hBOpen.
split;first exact:hBOrigin.
move=>z hz i hi.
have hIncluded:U (inclusion z).
  have hSmall:NX (inclusion z)<rho by rewrite (complex_weierstrass_transverse_inclusion_norm hSplit).
  have h:=hBall (inclusion z) hSmall;by rewrite add0r in h.
have [radius [hRadius hLineBall]]:=hInterior (inclusion z) hIncluded.
have [delta [hDelta hSmall]]:=@norm_scalar_line_small_increments R XR NX hNXR v radius hRadius.
have hPolynomial:exists r:R,0<r /\forall t:R,`|t|<r ->
    (\sum_(j<k) t^+j*:(f j z:CR))=\sum_(j<k) t^+j*:(0:CR).
  exists delta;split;first exact:hDelta.
  move=>t ht.
  have hPoint:U ((inclusion z:XR)+t*:(v:XR)):=hLineBall _ (hSmall t ht).
  have hEquation:=hZero _ hPoint.
  have hExpression:((inclusion z:XR)+t*:(v:XR):XR)=ComplexScalars.embed R t*:v+inclusion z:=addrC _ _.
  rewrite hExpression (complex_weierstrass_line_functional_coordinate hSplit)
    (complex_weierstrass_line_transverse_coordinate hSplit) in hEquation.
  have hBridge:(\sum_(j<k) (ComplexScalars.embed R t)^+j*f j z)=
      \sum_(j<k) t^+j*:(f j z:CR).
    apply:eq_bigr=>j _.
    change ((ComplexScalars.embed R t)^+j*f j z=ComplexScalars.embed R (t^+j)*f j z).
    by rewrite rmorphXn.
  rewrite hBridge in hEquation.
  rewrite hEquation;apply:esym;apply:big1=>j _;exact:scaler0.
exact:(@norm_weierstrass_finite_local_coefficients R CR (@complex_modulus R) (@complex_modulus_real_norm R)
  k (fun j=>f j z) (fun _=>0) hPolynomial i hi).
Qed.
End Independence.
