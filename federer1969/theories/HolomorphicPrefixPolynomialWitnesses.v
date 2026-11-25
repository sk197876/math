(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 330–331:
    the original polynomial and its derivative
    have actual analytic representatives on one
    original prefix neighbourhood. Apply the
    existing finite analytic neighbourhood and
    checked pointed representative and differential connections. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP HolomorphicLinear HolomorphicRestriction HolomorphicFiniteCalculus HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormDifferentialLocal NormAnalyticUP NormAnalyticOperations NormAnalyticDomain
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing FiniteHolomorphicNeighbourhood
  PointedHolomorphicPullbackUP PointedHolomorphicPolynomialRepresentative PointedHolomorphicPolynomialDerivativeRepresentative
  HolomorphicPrefixPolynomialDifferential CommutativePolynomialUP CommutativePolynomialEvaluationUP
  FormalPolynomialDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_prefix_polynomial_actual_witnesses]:
    common analytic Y and the actual
    W_(m+1), W'_(m+1), 3.4.12, p. 339, extending 3.4.8(10),
    pp. 330–331. The same original
    coefficient representatives occur in the
    polynomial, its formal derivative germ and
    its actual transverse differential. No
    derivative or neighbourhood witness is assumed. *)
Theorem holomorphic_prefix_polynomial_actual_witnesses (R:realType) (X Y:lmodType (ComplexScalars.C R))
  (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
  (projection:Hom X Y)
  (E:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)]->
    [the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)]})
  (xi:Hom X (ComplexScalars.C R)^o) (fXi:@holomorphic_representative_type R X NX hNX 0)
  (T:comNzRingType)
  (embed:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)]->T})
  (variable:T) (coefficient:T->nat->@holomorphic_germ_ring R Y NY hNY 0)
  (hT:is_commutative_polynomial_ring embed variable coefficient)
  (J:{rmorphism T->[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)]})
  (W derivative:T) N (b:'I_N->@holomorphic_representative_type R Y NY hNY 0):
  is_pointed_holomorphic_germ_pullback projection E ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY (complex_hom_real projection) ->@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->
  (forall x,holomorphic_representative_value fXi x = xi x) ->
  is_commutative_polynomial_evaluation embed variable E (holomorphic_germ fXi) J ->
  is_formal_polynomial_derivative coefficient W derivative ->
  (forall i,(N<=i)%N ->coefficient W i = 0) ->
  (forall i:'I_N,holomorphic_germ (b i) = coefficient W i) ->
  exists (U:set Y) (f fD:@holomorphic_representative_type R X NX hNX 0),
    U 0 /\@open (real_norm_metric_space hNY) U /\
    (forall i,@is_holomorphic R Y (ComplexScalars.C R)^o NY (@complex_modulus R) hNY (@complex_modulus_real_norm R)
      U (holomorphic_representative_value (b i))) /\
    (holomorphic_germ f:@holomorphic_germ_ring R X NX hNX 0) = J W /\
    (holomorphic_germ fD:@holomorphic_germ_ring R X NX hNX 0) = J derivative /\
    @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
      (fun x=>U (projection x)) (holomorphic_representative_value f) /\
    @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
      (fun x=>U (projection x)) (holomorphic_representative_value fD) /\
    (forall x,holomorphic_representative_value f x =
      \sum_(i<N) holomorphic_representative_value (b i) (projection x)*(xi x)^+(i:nat)) /\
    (forall x,holomorphic_representative_value fD x =
      \sum_(i<N) (i:nat)%:R*holomorphic_representative_value (b i) (projection x)*(xi x)^+(i:nat).-1) /\
    forall a:X,U (projection a) ->exists L:Hom (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o),
      @has_norm_differential R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (fun x=>U (projection x))
        (holomorphic_representative_value f) a L /\
      forall v:X,projection v = 0 ->L v = holomorphic_representative_value fD a*xi v.
Proof.
move=>hE hProjection hXi hXiValues hJ hDerivative hSupport hB.
have [U [hOrigin [hOpen hAnalytic]]]:=@finite_holomorphic_representative_neighbourhood R Y NY hNY 0
  [the finType of 'I_N] b.
have hInterior y (hy:U y):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) Y) NY U y.
  have hNeighbourhood:=hOpen;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R (restricted_space (ComplexScalars.embed R) Y) NY hNY U y).2 (hNeighbourhood y hy)).
have [f [hValues hGerm]]:=@pointed_holomorphic_polynomial_actual_representative R X Y NX NY hNX hNY
  projection E xi fXi T embed variable coefficient hT J W N b hE hXiValues hJ hSupport hB.
have [fD [hDerivativeValues hDerivativeGerm]]:=@pointed_holomorphic_polynomial_derivative_actual_representative R X Y NX NY hNX hNY
  projection E xi fXi T embed variable coefficient hT J W derivative N b hE hXiValues hJ hDerivative hSupport hB.
have [hF [hD hDifferentials]]:=@holomorphic_prefix_polynomial_differential R X Y NX NY hNX hNY U
  projection xi N (fun i=>holomorphic_representative_value (b i)) hInterior hProjection hXi hAnalytic.
pose A:=fun x:X=>U (projection x).
pose NS:=@complex_modulus R.
pose hNS:=@complex_modulus_real_norm R.
have hFActual:@is_holomorphic R X (ComplexScalars.C R)^o NX NS hNX hNS A (holomorphic_representative_value f).
  apply:(@holomorphic_domain_agreement R X (ComplexScalars.C R)^o NX NS hNX hNS A _ _ _ hF)=>x _.
  exact:esym (hValues x).
have hDActual:@is_holomorphic R X (ComplexScalars.C R)^o NX NS hNX hNS A (holomorphic_representative_value fD).
  apply:(@holomorphic_domain_agreement R X (ComplexScalars.C R)^o NX NS hNX hNS A _ _ _ hD)=>x _.
  exact:esym (hDerivativeValues x).
exists U,f,fD;split;first exact:hOrigin.
split;first exact:hOpen.
split;first exact:hAnalytic.
split;first exact:hGerm.
split;first exact:hDerivativeGerm.
split;first exact:hFActual.
split;first exact:hDActual.
split;first exact:hValues.
split;first exact:hDerivativeValues.
move=>a ha;have [L [hL hDirection]]:=hDifferentials a ha.
exists L;split.
- apply:(@norm_differential_domain_agreement R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX A _ _ a L _ hL)=>x _.
  exact:esym (hValues x).
- move=>v hZero;rewrite hDirection //;by rewrite hDerivativeValues.
Qed.
