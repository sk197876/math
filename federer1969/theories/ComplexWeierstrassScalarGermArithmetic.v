(** Federer (1969), 3.4.12, p. 339: original complex
    scalar normalization respects actual germs and their derivative
    forms. Reuse bounded target postcomposition and original local
    differential uniqueness; no complex action on a real operator
    carrier is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm ComplexScalarRealBounded NormDifferentialUP NormRegularity NormAnalyticLocal
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearPostcompose
  NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherDifferentialUnique NormHigherDifferentialPostcompose
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermUP
  HolomorphicGermOperationsUP HolomorphicGermSealed HolomorphicGermRingLaws HolomorphicGermRing
  HolomorphicGermJetsSealed HolomorphicGermFormsUP HolomorphicGermFormsSealed SymmetricForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Scalars.
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
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i XR CR NX N hNXR hN).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i XR CR NX N hNXR hN).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i XR CR NX N hNXR hN).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i XR CR NX N hNXR hN).
Variable a:X.
Local Notation G:=(@holomorphic_germ_ring R X NX hNXR a).
Local Notation constant:=(fun c:C=>holomorphic_germ (@holomorphic_constant_representative R X NX hNXR a c)).

(** Source for [complex_weierstrass_constant_germ_product]: original
    complex scalar multiplication agrees with multiplication of the
    actual constant germs, extending 3.4.6, p. 322, under
    3.4.12, p. 339. *)
Lemma complex_weierstrass_constant_germ_product (c d:C):
  (constant c:G)*constant d=constant (c*d).
Proof.
change (@HolomorphicGerms.mul R X NX hNXR a (constant c) (constant d)=constant (c*d)).
rewrite (@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNXR a)).
apply:holomorphic_germ_pointwise_equality=>x;reflexivity.
Qed.

(** Source for [complex_weierstrass_scalar_germ_form]: multiplication
    by the original scalar multiplies every original complex
    derivative form by that scalar, including order zero,
    extending 3.4.6, p. 322, under 3.4.12, p. 339. *)
Lemma complex_weierstrass_scalar_germ_form m (c:C) (alpha:G):
  @HolomorphicGermForms.value R X NX hNX a m ((constant c:G)*alpha)=
    c*:@HolomorphicGermForms.value R X NX hNX a m alpha.
Proof.
have [f hRep]:=@holomorphic_germ_has_representative R X NX hNXR a alpha.
pose F:=holomorphic_representative_value f.
have [U [ha hF]]:=holomorphic_representative_holomorphic f.
have hClass:=norm_analytic_class_all_orders hF.1.
have hOpen x (hx:U x):@norm_domain_interior R XR NX U x:=((hClass 0%N).1 x hx).1.
have [D [hD _]]:=(hClass m).2.
have [M [hValues hM]]:=@complex_scalar_real_bounded_exists R C^o N (@complex_modulus_complex_norm R) c.
have [J [hJ hJBound]]:=@continuous_multilinear_postcompose_family_exists R XR CR CR
  NX N N Z Z ev ZN ev ZN hZ hZ M hM.
have hPost:=@norm_higher_differential_field_postcompose R XR CR CR NX N N hNXR hN hN
  Z Z ev ZN ev ZN hZ hZ M J hJ hJBound U F m D hD a ha.
pose g:=@holomorphic_multiply_representatives R X NX hNXR a
  (@holomorphic_constant_representative R X NX hNXR a c) f.
pose beta:G:=(constant c:G)*alpha.
have hRepG:holomorphic_germ g=beta.
  rewrite /beta -hRep.
  exact:esym (@holomorphic_germ_multiply_equation R X NX hNXR a _ _ _
    (@HolomorphicGerms.laws R X NX hNXR a) _ f).
have hActualG:=(@norm_higher_differential_local_agreement R XR CR NX N hNXR hN Z ev ZN hZ
  m U U U (fun x=>M (F x)) (holomorphic_representative_value g) hOpen
  (fun x _=>iff_refl _) (fun x _ _=>hValues (F x)) a ha (J m (D a))).1 hPost.
have hFullG:=(@norm_higher_differential_open_restriction R XR CR NX N hNXR hN Z ev ZN hZ
  m setT U (holomorphic_representative_value g) (fun x _=>Logic.I) hOpen a ha (J m (D a))).2 hActualG.
have hJetG:=@HolomorphicGermJets.laws R X NX hNXR a m beta g hRepG.
have hEqualG:=norm_higher_differential_unique hNXR hN hZ hJetG hFullG.
have hFullF:=(@norm_higher_differential_open_restriction R XR CR NX N hNXR hN Z ev ZN hZ
  m setT U F (fun x _=>Logic.I) hOpen a ha (D a)).2 (hD a ha).
have hJetF:=@HolomorphicGermJets.laws R X NX hNXR a m alpha f hRep.
have hEqualF:=norm_higher_differential_unique hNXR hN hZ hFullF hJetF.
apply:sform_ext=>t.
rewrite (@HolomorphicGermForms.laws R X NX hNX a m beta t) hEqualG hJ hValues hEqualF
  sform_scaleE (@HolomorphicGermForms.laws R X NX hNX a m alpha t).
reflexivity.
Qed.
End Scalars.
