(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 327, 331:
    the bounded original numerators have actual
    finite expressions on one prefix neighbourhood.
    Retain the chosen coefficients and apply
    the existing finite-neighbourhood, polynomial-representative
    and differential theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  HolomorphicUP HolomorphicRestriction HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing
  FiniteHolomorphicNeighbourhood PointedHolomorphicPullbackUP PointedHolomorphicPolynomialRepresentative
  HolomorphicPrefixPolynomialDifferential CommutativePolynomialUP CommutativePolynomialEvaluationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointed_polynomial_holomorphic_family]:
    the functions sum_i b_(i,j)(p_m(x))
    omega_(m+1)(x)^i on the original cylinder,
    3.4.12, p. 339, extending 3.4.8(10), pp. 327, 331. The
    exact same original coefficients give their
    germ and actual finite-expression equations. *)
Theorem pointed_polynomial_holomorphic_family (R:realType) (X Y:lmodType (ComplexScalars.C R))
  (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
  (projection:Hom X Y)
  (E:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)]->
    [the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)]})
  (xi:Hom X (ComplexScalars.C R)^o) (fXi:@holomorphic_representative_type R X NX hNX 0)
  (P:comNzRingType)
  (embed:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)]->P})
  (variable:P) (coefficient:P->nat->@holomorphic_germ_ring R Y NY hNY 0)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (J:{rmorphism P->[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)]})
  (I:finType) (W:I->P) N (b:I->'I_N->@holomorphic_representative_type R Y NY hNY 0):
  is_pointed_holomorphic_germ_pullback projection E ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY (complex_hom_real projection) ->@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->
  (forall x,holomorphic_representative_value fXi x = xi x) ->
  is_commutative_polynomial_evaluation embed variable E (holomorphic_germ fXi) J ->
  (forall j i,(N<=i)%N ->coefficient (W j) i = 0) ->
  (forall j i,holomorphic_germ (b j i) = coefficient (W j) i) ->
  exists (U:set Y) (f:I->@holomorphic_representative_type R X NX hNX 0),
    U 0 /\@open (real_norm_metric_space hNY) U /\
    (forall j i,@is_holomorphic R Y (ComplexScalars.C R)^o NY (@complex_modulus R) hNY (@complex_modulus_real_norm R)
      U (holomorphic_representative_value (b j i))) /\
    (forall j,(holomorphic_germ (f j):@holomorphic_germ_ring R X NX hNX 0) = J (W j)) /\
    (forall j,@is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
      (fun x=>U (projection x)) (holomorphic_representative_value (f j))) /\
    forall j x,holomorphic_representative_value (f j) x =
      \sum_(i<N) holomorphic_representative_value (b j i) (projection x)*(xi x)^+(i:nat).
Proof.
move=>hE hProjection hXi hValues hJ hSupport hB.
pose index:=[the finType of (I*'I_N)%type].
pose coefficients (q:index):=b q.1 q.2.
have [U [hOrigin [hOpen hCoefficients]]]:=@finite_holomorphic_representative_neighbourhood R Y NY hNY 0
  index coefficients.
have hExists j:=@pointed_holomorphic_polynomial_actual_representative R X Y NX NY hNX hNY projection E xi fXi
  P embed variable coefficient hP J (W j) N (b j) hE hValues hJ (hSupport j) (hB j).
have [f hF]:=choice hExists.
have hInterior y (hy:U y):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) Y) NY U y.
  have hNeighbourhood:=hOpen;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R (restricted_space (ComplexScalars.embed R) Y) NY hNY U y).2 (hNeighbourhood y hy)).
exists U,f;split;first exact:hOrigin.
split;first exact:hOpen.
split;first by move=>j i;exact:hCoefficients (j,i).
split;first by move=>j;exact:(hF j).2.
split;last by move=>j;exact:(hF j).1.
move=>j.
have hA:=(@holomorphic_prefix_polynomial_differential R X Y NX NY hNX hNY U projection xi N
  (fun i=>holomorphic_representative_value (b j i)) hInterior hProjection hXi
  (fun i=>hCoefficients (j,i))).1.
apply:(@holomorphic_domain_agreement R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX
  (@complex_modulus_real_norm R) (fun x=>U (projection x)) _ _ _ hA)=>x _.
exact:esym ((hF j).1 x).
Qed.
