(** Federer (1969), 3.4.12, p. 339: every original
    nonzero complex direction admits a bounded complex functional
    taking value one on it. Reuse the project's proved real
    Hahn–Banach norming corollary and complexify that actual functional. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexScalarLaws
  ComplexModulus ComplexScalarNorm ComplexModulusFiniteSum NormDifferentialUP HolomorphicLinear
  SeminormNormingFunctional ComplexifyRealFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Functionals.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation e:=(ComplexScalars.embed R).
Local Notation ii:=(ComplexScalars.ii R).
Local Notation N:=(@complex_modulus R).

(** Source for [complex_weierstrass_direction_functional_exists]: the
    original complex functional for the transverse splitting, extending
    3.4.6, p. 322, under 3.4.12, p. 339. No
    finite-dimensional hypothesis, functional or coordinates are supplied. *)
Theorem complex_weierstrass_direction_functional_exists (v:X):v<>0 ->
  exists xi:Hom X C^o,@norm_bounded_linear R XR CR NX N (complex_hom_real xi) /\xi v= 1.
Proof.
move=>hV.
have hNonzero:v!=0 by apply/eqP.
have hPositive:0<NX v by rewrite (real_norm_positive hNXR.1 hNXR.2).
have hNormNonzero:NX v!=0 by rewrite (gt_eqF hPositive).
have [f [hF hValue]]:=@seminorm_norming_functional R XR NX hNXR.1 v.
have [L [hValues hReal]]:=@complex_functional_from_real_exists R X (hom_of_linear f).
have hLNonzero:L v!=0.
  apply/eqP=>hZero;have h:=hReal v.
  rewrite hZero ComplexScalarTheory.re_zero in h.
  have hFV:0=NX v by rewrite -hValue;exact:h.
  by rewrite -hFV eqxx in hNormNonzero.
pose B:=1+N ii*N ii.
have hB:0<=B by apply:addr_ge0 ler01 (mulr_ge0 (complex_modulus_ge0 _) (complex_modulus_ge0 _)).
have hBound x:N (L x)<=B*NX x.
  rewrite hValues.
  have hTriangle:=@complex_modulus_subtract_bound R (e (f x)) (ii*e (f (ii*:x))).
  rewrite complex_modulus_mul !complex_modulus_real in hTriangle.
  have hRotated:`|f (ii*:x)|<=N ii*NX x.
    have h:=hF (ii*:x);by rewrite (complex_norm_scale hNX) in h.
  have hSum:=lerD (hF x) (ler_wpM2l (complex_modulus_ge0 ii) hRotated).
  apply:le_trans hTriangle _;apply:le_trans hSum _.
  have hEquation:NX x+N ii*(N ii*NX x)=B*NX x by rewrite /B;ring.
  by rewrite hEquation.
pose xi:Hom X C^o:=@GRing.scale C [the lmodType C of Hom X C^o] (L v)^-1 L.
exists xi;split.
- exists (N ((L v)^-1)*B);split;first exact:mulr_ge0 (complex_modulus_ge0 _) hB.
  move=>x;rewrite complex_hom_real_values /xi hom_scaleE.
  change (N ((L v)^-1*L x)<=N ((L v)^-1)*B*NX x).
  rewrite complex_modulus_mul -mulrA.
  have hFactor:0<=N ((L v)^-1):=complex_modulus_ge0 ((L v)^-1).
  exact:(ler_wpM2l hFactor (hBound x)).
- rewrite /xi hom_scaleE.
  change ((L v)^-1*L v= 1);exact:mulVf.
Qed.
End Functionals.
