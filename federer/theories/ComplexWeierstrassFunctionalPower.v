(** Federer (1969), 3.4.12, p. 339: the original monic
    dividend xi^k is holomorphic and has the single expected
    mixed coefficient. Reuse the actual complex linear map,
    scalar power closure and vector-valued real line Taylor comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormOpenDomainLaws NormAnalyticUP
  HolomorphicUP HolomorphicLinear HolomorphicFiniteCalculus HolomorphicGermRepresentatives HolomorphicGermUP
  AnalyticDirectionalCoefficient AnalyticDirectionalPolynomialLine AnalyticIteratedDirectionalCoefficients
  ComplexWeierstrassTransverseUP ComplexWeierstrassTransverseLaws ComplexWeierstrassCoefficientUP
  ComplexWeierstrassIteratedGermCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Powers.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).

(** Source for [complex_weierstrass_functional_power_representative]: the
    actual original monic dividend is holomorphic throughout the
    source, extending 3.4.6(2), p. 322, under 3.4.12, p. 339. *)
Theorem complex_weierstrass_functional_power_representative (xi:Hom X C^o) k:
  @norm_bounded_linear R XR CR NX N (complex_hom_real xi) ->
  exists f:@holomorphic_representative_type R X NX hNXR 0,
    holomorphic_representative_value f=(fun x=>(xi x)^+k) /\
    is_holomorphic hNXR hN setT (holomorphic_representative_value f).
Proof.
move=>hXi.
have hLinear:=@holomorphic_bounded_linear R X C^o NX N hNXR hN setT xi
  (fun x _=>@norm_full_domain_interior R XR NX x) hXi.
have hPower:=@holomorphic_scalar_power R X NX hNXR setT xi k hLinear.
have [f hValues]:=@holomorphic_representative_from_domain R X NX hNXR 0 setT
  (fun x=>(xi x)^+k) Logic.I hPower.
exists f;split;first exact:hValues;by rewrite hValues.
Qed.

(** Source for [complex_weierstrass_functional_power_coefficients]: the
    actual original dividend has mixed coefficient one at (k,0)
    and zero elsewhere, extending 3.4.6(2), pp. 322–324, under
    3.4.12, p. 339. All coefficients are actual derivatives. *)
Theorem complex_weierstrass_functional_power_coefficients (K:lmodType C)
    (NK:K->R) (v:X) (xi:Hom X C^o) (inclusion:Hom K X) (projection:Hom X K) k
    (f:@holomorphic_representative_type R X NX hNXR 0) (q:nat->nat->K->C):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  holomorphic_representative_value f=(fun x=>(xi x)^+k) ->
  @norm_analytic R XR CR NX N hNXR hN setT (holomorphic_representative_value f) ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX (holomorphic_germ f) v inclusion i j (q i j)) ->
  forall i j z,q i j z=if ((i==k)&&(j==0))%N then 1 else 0.
Proof.
move=>hSplit hValues hf hQ i j z.
pose F:=holomorphic_representative_value f.
have [D [P [hD hP]]]:=@analytic_iterated_directional_coefficients_exist R XR CR NX N hNXR hN
  setT F v (inclusion z) hf.
have hOriginal:=@complex_weierstrass_iterated_germ_coefficient R X K NX hNX (holomorphic_germ f) f setT
  v inclusion i j (q i j) (D i) (P i j) z (erefl _) Logic.I hf (hQ i j) (hD i).1 (hP i j).1.
have hFirst z':D i (inclusion z')=if (i==k)%N then 1 else 0.
  have hLine (t:R) (ht:`|t|<1):F ((inclusion z':XR)+t*:(v:XR))=
      \sum_(n<k.+1) t^+n*:(if ((n:nat)==k)%N then (1:CR) else 0).
    rewrite /F hValues addrC (complex_weierstrass_line_functional_coordinate hSplit).
    rewrite (bigD1 (Ordinal (ltnSn k))) //= eqxx.
    have hOthers:(\sum_(n<k.+1 | n!=Ordinal (ltnSn k))
        t^+n*:(if ((n:nat)==k)%N then (1:CR) else 0))=0.
      apply:big1=>n hn.
      have hNe:((n:nat)!=k)%N by move:hn;rewrite -val_eqE /=.
      by rewrite (negbTE hNe) scaler0.
    rewrite hOthers addr0.
    change ((ComplexScalars.embed R t)^+k=ComplexScalars.embed R (t^+k)*1).
    by rewrite rmorphXn mulr1.
  have hFinite:=@analytic_directional_polynomial_line_coefficient R XR CR NX N hNXR hN
    setT F i v (inclusion z') (D i) k.+1 (fun n=>if (n==k)%N then 1 else 0) 1
    Logic.I hf (hD i).1 ltr01 hLine.
  case hSmall:(i<k.+1)%N in hFinite *=>//.
  have hNe:(i!=k)%N by apply/eqP=>h;by rewrite h ltnSn in hSmall.
  by rewrite (negbTE hNe).
have hLine (t:R) (ht:`|t|<1):D i ((0:XR)+t*:(inclusion z:XR))=
    \sum_(n<1) t^+n*:(if (i==k)%N then (1:CR) else 0).
  have hInclusion:inclusion (ComplexScalars.embed R t*:z)=(t*:(inclusion z:XR):XR).
    by rewrite linearZ.
  rewrite add0r -hInclusion hFirst big_ord1 /= expr0 scale1r;reflexivity.
have hSecond:=@analytic_directional_polynomial_line_coefficient R XR CR NX N hNXR hN
  setT (D i) j (inclusion z) 0 (P i j) 1 (fun _=>if (i==k)%N then 1 else 0) 1
  Logic.I (hD i).2 (hP i j).1 ltr01 hLine.
rewrite hOriginal hSecond.
clear - R i k;case:j=>[|j];by rewrite ?ltn0 ?ltnS ?leqn0 /= ?andbT ?andbF.
Qed.
End Powers.
