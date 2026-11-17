(** Federer (1969), 3.4.12, p. 339, extending the prefix
    cylinder in 3.4.8(10), p. 331. The original finite polynomial
    and its formal derivative are holomorphic throughout the cylinder.
    Apply existing bounded linear, composition, power and finite-sum laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormLinearDomainLaws
  HolomorphicUP HolomorphicLinear HolomorphicFiniteCalculus HolomorphicProduct
  HolomorphicArithmetic HolomorphicRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_prefix_polynomial_holomorphy]:
    the original coefficient representatives define both polynomial
    expressions on the whole prefix cylinder, 3.4.12, p. 339.
    No independent derivative coefficients are chosen; zero powers,
    zero-dimensional spaces and the empty family remain. *)
Theorem holomorphic_prefix_polynomial_holomorphy (R:realType)
    (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (U:set Y) (projection:Hom X Y) (xi:Hom X (ComplexScalars.C R)^o)
    N (b:'I_N->Y->ComplexScalars.C R):
  (forall y,U y ->@norm_domain_interior R (restricted_space (ComplexScalars.embed R) Y) NY U y) ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY (complex_hom_real projection) ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->
  (forall i,@is_holomorphic R Y (ComplexScalars.C R)^o NY (@complex_modulus R)
    hNY (@complex_modulus_real_norm R) U (b i)) ->
  let A:=fun x:X=>U (projection x) in
  let F:=fun x:X=>\sum_(i<N) b i (projection x)*(xi x)^+(i:nat) in
  let derivative:=fun x:X=>\sum_(i<N) (i:nat)%:R*b i (projection x)*(xi x)^+(i:nat).-1 in
  @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R)
    hNX (@complex_modulus_real_norm R) A F /\
  @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R)
    hNX (@complex_modulus_real_norm R) A derivative.
Proof.
move=>hOpen hProjection hXi hB A F derivative.
pose C:=ComplexScalars.C R.
pose NC:=@complex_modulus R.
pose hNC:=@complex_modulus_real_norm R.
have hAOpen x (hx:A x):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX A x.
  exact:(@norm_bounded_linear_preimage_interior R
    (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) Y) NX NY hNX
    (complex_hom_real projection) U x hProjection (hOpen _ hx)).
have hP:=@holomorphic_bounded_linear R X Y NX NY hNX hNY A projection hAOpen hProjection.
have hXiHol:=@holomorphic_bounded_linear R X C^o NX NC hNX hNC A xi hAOpen hXi.
have hCoefficient i:@is_holomorphic R X C^o NX NC hNX hNC A (fun x=>b i (projection x)).
  exact:(@holomorphic_compose_on R X Y C^o NX NY NC hNX hNY hNC A U
    projection (b i) (fun x hx=>hx) hP (hB i)).
have hTerm i:@is_holomorphic R X C^o NX NC hNX hNC A
    (fun x=>b i (projection x)*(xi x)^+(i:nat)).
  exact:(holomorphic_product (hCoefficient i) (holomorphic_scalar_power (i:nat) hXiHol)).
have hDerivativeTerm (i:'I_N):@is_holomorphic R X C^o NX NC hNX hNC A
    (fun x=>(i:nat)%:R*b i (projection x)*(xi x)^+(i:nat).-1).
  have hBase:=holomorphic_product (hCoefficient i)
    (holomorphic_scalar_power (i:nat).-1 hXiHol).
  have hConstant:=@holomorphic_constant R X C^o NX NC hNX hNC A (i:nat)%:R hAOpen.
  have hProduct:=holomorphic_product hConstant hBase.
  apply:(@holomorphic_domain_agreement R X C^o NX NC hNX hNC A _ _ _ hProduct)=>x _.
  exact:mulrA.
split.
- exact:(@holomorphic_finite_sum R X C^o NX NC hNX hNC A [the finType of 'I_N]
    _ hAOpen hTerm).
- exact:(@holomorphic_finite_sum R X C^o NX NC hNX hNC A [the finType of 'I_N]
    _ hAOpen hDerivativeTerm).
Qed.
