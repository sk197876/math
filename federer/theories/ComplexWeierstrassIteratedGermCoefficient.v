(** Federer (1969), 3.4.12, p. 339: actual divided
    derivative fields recover the original complex mixed germ
    coefficients. Reuse the target-independent grouping theorem and
    the exact embedding of the real factorial normalizations. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormHigherDifferentialUP NormHigherDifferentialLocal NormAnalyticUP NormAnalyticLocal
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermJetsSealed
  AnalyticDirectionalCoefficient ComplexWeierstrassCoefficientUP ComplexWeierstrassCoefficientValue
  NormWeierstrassIteratedCoefficientValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coefficients.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun k=>@ContinuousMultilinear.space R k XR CR NX N hNXR hN).
Local Notation ev:=(fun k=>@ContinuousMultilinear.evaluation R k XR CR NX N hNXR hN).
Local Notation NZ:=(fun k=>@ContinuousMultilinear.norm R k XR CR NX N hNXR hN).
Local Notation hZ:=(fun k=>@ContinuousMultilinear.laws R k XR CR NX N hNXR hN).

(** Source for [complex_weierstrass_iterated_germ_coefficient]: the
    original split coefficient is the iterated divided derivative
    of every actual representative, extending 3.4.6, pp. 322–323,
    as required by 3.4.12, p. 339. *)
Theorem complex_weierstrass_iterated_germ_coefficient
    (alpha:holomorphic_germ_space hNXR (0:X))
    (p:@holomorphic_representative_type R X NX hNXR 0) (A:set X) v (inclusion:Hom K X)
    i j (q:K->C) (D P:X->C) z:
  holomorphic_germ p=alpha ->A 0 ->
  @norm_analytic R XR CR NX N hNXR hN A (holomorphic_representative_value p) ->
  is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j q ->
  @is_analytic_directional_coefficient R XR CR NX N hNXR hN
    A (holomorphic_representative_value p) i v D ->
  @is_analytic_directional_coefficient R XR CR NX N hNXR hN A D j (inclusion z) P ->q z = P 0.
Proof.
move=>hRep ha hf hQ hD hP.
have hOpen x (hx:A x):@norm_domain_interior R XR NX A x:=
  ((norm_analytic_class_all_orders hf 0%N).1 x hx).1.
pose w:=@HolomorphicGermJets.value R X NX hNXR 0 (i+j)%N alpha.
have hGlobal:=@HolomorphicGermJets.laws R X NX hNXR 0 (i+j)%N alpha p hRep.
have hLocal:=(@norm_higher_differential_open_restriction R XR CR NX N hNXR hN Z ev NZ hZ
  (i+j)%N setT A (holomorphic_representative_value p) (fun x _=>Logic.I) hOpen 0 ha w).1 hGlobal.
have hValue:=@norm_weierstrass_iterated_coefficient_value R XR CR N hN NX hNXR A
  (holomorphic_representative_value p) 0 v (inclusion z) i j D P w ha hf hD hP hLocal.
rewrite (complex_weierstrass_split_coefficient_value hQ z) hValue.
have hCoefficient:(((i`!)%:R:C)*(j`!)%:R)^-1=
    ComplexScalars.embed R ((((i`!)%:R:R)*(j`!)%:R)^-1).
  by rewrite fmorphV rmorphM !rmorph_nat.
by rewrite hCoefficient.
Qed.
End Coefficients.
