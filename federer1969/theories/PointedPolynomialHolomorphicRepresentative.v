(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 331:
    an original polynomial has an actual
    representative analytic on a full prefix
    cylinder. Select local coefficient witnesses
    and apply the existing polynomial-witness theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP HolomorphicLinear HolomorphicRestriction HolomorphicFiniteCalculus HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormAnalyticUP HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing HolomorphicGermRingLaws
  PointedHolomorphicPullbackUP CommutativePolynomialUP CommutativePolynomialEvaluationUP
  FormalPolynomialDerivativeSealed HolomorphicPrefixPolynomialWitnesses.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointed_polynomial_holomorphic_representative]:
    t_(m+1), s_(m+1) and the remaining
    polynomial numerators may be represented on
    p_m inverse(Y), 3.4.12, p. 339, extending 3.4.8(10), p. 331.
    Finite support, coefficient representatives and
    the neighbourhood are proved existence witnesses. *)
Theorem pointed_polynomial_holomorphic_representative (R:realType) (X Y:lmodType (ComplexScalars.C R))
  (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
  (projection:Hom X Y)
  (E:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)]->
    [the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)]})
  (xi:Hom X (ComplexScalars.C R)^o) (fXi:@holomorphic_representative_type R X NX hNX 0)
  (P:comNzRingType)
  (embed:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)]->P})
  (variable:P) (coefficient:P->nat->@holomorphic_germ_ring R Y NY hNY 0)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (J:{rmorphism P->[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)]}) (W:P):
  is_pointed_holomorphic_germ_pullback projection E ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY (complex_hom_real projection) ->@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->
  (forall x,holomorphic_representative_value fXi x = xi x) ->
  is_commutative_polynomial_evaluation embed variable E (holomorphic_germ fXi) J ->
  exists (U:set Y) (f:@holomorphic_representative_type R X NX hNX 0),
    U 0 /\@open (real_norm_metric_space hNY) U /\
    (holomorphic_germ f:@holomorphic_germ_ring R X NX hNX 0) = J W /\
    @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
      (fun x=>U (projection x)) (holomorphic_representative_value f).
Proof.
move=>hE hProjection hXi hValues hJ.
have [N hSupport]:=polynomial_coefficients_finite hP W.
have hExists (i:'I_N):exists b:@holomorphic_representative_type R Y NY hNY 0,
    holomorphic_germ b = coefficient W i.
  exact:holomorphic_germ_has_representative.
have [b hB]:=choice hExists.
pose derivative:=@FormalPolynomialDerivative.value
  [the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)] P embed variable coefficient hP W.
have hDerivative:=@FormalPolynomialDerivative.laws
  [the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)] P embed variable coefficient hP W.
have [U [f [fD [hOrigin [hOpen [hCoefficients [hGerm [_ [hAnalytic _]]]]]]]]]:=
  @holomorphic_prefix_polynomial_actual_witnesses R X Y NX NY hNX hNY projection E xi fXi
    P embed variable coefficient hP J W derivative N b hE hProjection hXi hValues hJ hDerivative hSupport hB.
exists U,f;by split;[exact:hOrigin|split;[exact:hOpen|split]].
Qed.
