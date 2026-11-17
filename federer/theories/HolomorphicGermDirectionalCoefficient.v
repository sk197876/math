(** Federer (1969), 3.4.12, p. 339, extending the
    Taylor argument of 3.4.8(5), p. 328: divided directional
    coefficients are the original complex homogeneous Taylor
    coefficients. Their actual derivative and local field equations
    are proved through the original scalar embedding. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormRegularity NormAnalyticUP NormAnalyticLocal NormHigherDifferentialUP NormHigherDifferentialLocal
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermRepresentatives HolomorphicGermJetsSealed
  HolomorphicGermFormsUP HolomorphicGermFormsSealed AnalyticDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coefficients.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation C:=(ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).

(** Source for [holomorphic_germ_directional_coefficient]: the original
    actual divided coefficient D^k(alpha)[v^k]/k!, extending
    3.1.11, pp. 219–222, under 3.4.12, p. 339. *)
Definition holomorphic_germ_directional_coefficient a k
    (alpha:@holomorphic_germ_ring R X NX hNXR a) (v:X):C:=
  sform_polynomial_value (@HolomorphicGermForms.value R X NX hNX a k alpha) v.

(** Source for [holomorphic_germ_directional_coefficient_real_value]:
    restricting the actual divided coefficient to real calculus
    changes none of its values, supporting 3.4.12, p. 339. *)
Lemma holomorphic_germ_directional_coefficient_real_value a k
    (alpha:@holomorphic_germ_ring R X NX hNXR a) v:
  holomorphic_germ_directional_coefficient k alpha v=
    ((k`!)%:R:R)^-1*:(@ContinuousMultilinear.evaluation R k XR CR NX N hNXR hN
      [ffun _:'I_k=>v] (@HolomorphicGermJets.value R X NX hNXR a k alpha):CR).
Proof.
rewrite /holomorphic_germ_directional_coefficient sform_polynomial_diagonal_value
  (@HolomorphicGermForms.laws R X NX hNX a k alpha).
have hTuple:[ffun i=>tnth [tuple v|_<k] i]=[ffun _:'I_k=>v].
  by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
rewrite hTuple.
pose value:=@ContinuousMultilinear.evaluation R k XR CR NX N hNXR hN
  [ffun _:'I_k=>v] (@HolomorphicGermJets.value R X NX hNXR a k alpha).
change (((k`!)%:R:C)^-1*value = ComplexScalars.embed R (((k`!)%:R:R)^-1)*value).
by rewrite fmorphV rmorph_nat.
Qed.

(** Source for [holomorphic_directional_coefficient_at_germ_centre]: each
    actual local directional coefficient field gives the original
    germ coefficient, extending 3.4.5, p. 319, and the
    complex Taylor argument of 3.4.12, p. 339. *)
Lemma holomorphic_directional_coefficient_at_germ_centre a k
    (alpha:@holomorphic_germ_ring R X NX hNXR a)
    (f:@holomorphic_representative_type R X NX hNXR a) (A:set X) v c:
  holomorphic_germ f=alpha ->A a ->
  @norm_analytic R XR CR NX N hNXR hN A (holomorphic_representative_value f) ->
  @is_analytic_directional_coefficient R XR CR NX N hNXR hN A
    (holomorphic_representative_value f) k v c ->c a=holomorphic_germ_directional_coefficient k alpha v.
Proof.
move=>hRep ha hAnalytic hCoefficient.
rewrite holomorphic_germ_directional_coefficient_real_value.
pose Z i:=@ContinuousMultilinear.space R i XR CR NX N hNXR hN.
pose ev i:=@ContinuousMultilinear.evaluation R i XR CR NX N hNXR hN.
pose NZ i:=@ContinuousMultilinear.norm R i XR CR NX N hNXR hN.
pose hZ i:=@ContinuousMultilinear.laws R i XR CR NX N hNXR hN.
have hOpen x (hx:A x):@norm_domain_interior R XR NX A x:=
  ((norm_analytic_class_all_orders hAnalytic 0%N).1 x hx).1.
have hActual:=(@norm_higher_differential_open_restriction R XR CR NX N hNXR hN Z ev NZ hZ
  k setT A (holomorphic_representative_value f) (fun x _=>Logic.I) hOpen a ha
  (@HolomorphicGermJets.value R X NX hNXR a k alpha)).1
  (@HolomorphicGermJets.laws R X NX hNXR a k alpha f hRep).
exact:(hCoefficient a ha _ hActual).
Qed.
End Coefficients.
