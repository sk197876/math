(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 331:
    transfer the existing finite-polynomial differential
    to an actual representative with the
    same original coefficient expression. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP HolomorphicLinear HolomorphicRestriction HolomorphicFiniteCalculus HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP NormDifferentialUP NormDifferentialLocal NormAnalyticUP
  HolomorphicPrefixPolynomialDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [actual_holomorphic_polynomial_transverse_differential]:
    the bounded numerator t_j has its
    actual transverse differential, supporting the
    original equation differentials in 3.4.12, p. 339, extending 3.4.8(10), p. 331. *)
Theorem actual_holomorphic_polynomial_transverse_differential (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (U:Y->Prop) (P:Hom X Y) (xi:Hom X (ComplexScalars.C R)^o) N (b:'I_N->Y->ComplexScalars.C R) (f:X->ComplexScalars.C R):
  (forall y,U y ->@norm_domain_interior R (restricted_space (ComplexScalars.embed R) Y) NY U y) ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY (complex_hom_real P) ->@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->
  (forall i,@is_holomorphic R Y (ComplexScalars.C R)^o NY (@complex_modulus R) hNY (@complex_modulus_real_norm R) U (b i)) ->
  (forall x,f x = \sum_(i<N) b i (P x)*(xi x)^+(i:nat)) ->
  forall a,U (P a) ->exists L:Hom (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o),
    @has_norm_differential R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (fun x=>U (P x)) f a L /\
    forall v,P v = 0 ->L v = (\sum_(i<N) (i:nat)%:R*b i (P a)*(xi a)^+(i:nat).-1)*xi v.
Proof.
move=>hInterior hP hXi hB hValues a ha.
have [L [hL hDirections]]:=(@holomorphic_prefix_polynomial_differential R X Y NX NY hNX hNY
  U P xi N b hInterior hP hXi hB).2.2 a ha.
exists L;split;last exact:hDirections.
apply:(norm_differential_domain_agreement hNX _ hL)=>x _;exact:esym (hValues x).
Qed.
