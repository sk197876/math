(** Federer (1969), 3.4.12, p. 339, extending the actual
    polynomial differentials of 3.4.8(10), p. 331. The existing
    chain rule and the complex polynomial connection give the
    differential in every original transverse direction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormDifferentialLinear
  NormDifferentialChain NormDifferentialLocal NormDifferentialDirectional
  NormLinearDomainLaws HolomorphicUP HolomorphicLinear HolomorphicDifferentialUP
  HolomorphicDifferentialExistence HolomorphicPrefixPolynomialHolomorphy
  ComplexPolynomialDirectionalDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Polynomial.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Local Notation C:=(ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Variables (NX:X->R) (NY:Y->R).
Variable hNX:@is_real_norm R XR NX.
Variable hNY:@is_real_norm R YR NY.
Variables (U:set Y) (projection:Hom X Y) (xi:Hom X C^o).
Variable N:nat.
Variable b:'I_N->Y->C.
Local Notation NC:=(@complex_modulus R).
Local Notation hNC:=(@complex_modulus_real_norm R).

(** Source for [holomorphic_prefix_polynomial_differential]:
    the formal derivative of the original polynomial gives its
    actual transverse differential on the entire prefix cylinder,
    3.4.12, p. 339. The original coefficient functions and every
    vector in the prefix kernel are retained. *)
Theorem holomorphic_prefix_polynomial_differential:
  (forall y,U y ->@norm_domain_interior R (restricted_space (ComplexScalars.embed R) Y) NY U y) ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY (complex_hom_real projection) ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NC (complex_hom_real xi) ->
  (forall i,@is_holomorphic R Y C^o NY NC hNY hNC U (b i)) ->
  let A:=fun x:X=>U (projection x) in
  let F:=fun x:X=>\sum_(i<N) b i (projection x)*(xi x)^+(i:nat) in
  let derivative:=fun x:X=>\sum_(i<N) (i:nat)%:R*b i (projection x)*(xi x)^+(i:nat).-1 in
  @is_holomorphic R X C^o NX NC hNX hNC A F /\
  @is_holomorphic R X C^o NX NC hNX hNC A derivative /\
  forall a:X,A a ->exists L:Hom XR CR,
    @has_norm_differential R XR CR NX NC A F a L /\
    forall v:X,projection v=0 ->L v=derivative a*xi v.
Proof.
move=>hOpen hProjection hXi hB A F derivative.
have hHol:=@holomorphic_prefix_polynomial_holomorphy R X Y NX NY hNX hNY
  U projection xi N b hOpen hProjection hXi hB.
split;first exact:hHol.1.
split;first exact:hHol.2.
move=>a hA.
have hAOpen x (hx:A x):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX A x.
  exact:(@norm_bounded_linear_preimage_interior R XR YR NX NY hNX
    (complex_hom_real projection) U x hProjection (hOpen _ hx)).
have hEach i:exists D:Hom YR CR,
    @has_norm_differential R YR CR NY NC U (b i) (projection a) D.
  have [D [L [hL hValues]]]:=holomorphic_differential_exists (hB i) hA.
  by exists L.
pose D:=fun i=>projT1 (cid (hEach i)).
have hD i:=projT2 (cid (hEach i)).
pose E:=fun i=>hom_comp (D i) (complex_hom_real projection).
have hLinear:=@norm_differential_linear R XR YR NX NY hNX hNY A a
  (complex_hom_real projection) (hAOpen a hA) hProjection.
have hCoefficient i:@has_norm_differential R XR CR NX NC A
    (fun x=>b i (projection x)) a (E i).
  have hChain:=@norm_differential_chain R XR YR CR NX NY NC hNX hNY hNC A U
    (complex_hom_real projection) (b i) a (complex_hom_real projection) (D i) hLinear (hD i).
  exact:(@norm_differential_restrict R XR CR NX NC
    (fun x=>A x /\U (projection x)) A (fun x=>b i (projection x)) a (E i)
    (fun x hx=>conj hx hx) (hAOpen a hA) hChain).
have [L [hL _]]:=@complex_polynomial_directional_differential R XR NX hNX A a 0 N
  (fun i x=>b i (projection x)) E (complex_hom_real xi) (hAOpen a hA)
  hXi hCoefficient (fun i=>linear0 (E i)).
exists L;split;first exact:hL.
move=>v hZero.
have hZeroD i:E i v=0 by rewrite /E hom_compE complex_hom_real_values hZero linear0.
have [M [hM hValue]]:=@complex_polynomial_directional_differential R XR NX hNX A a v N
  (fun i x=>b i (projection x)) E (complex_hom_real xi) (hAOpen a hA)
  hXi hCoefficient hZeroD.
have hEqual:L=M:=norm_differential_unique hNX hNC hL hM.
by rewrite hEqual.
Qed.
End Polynomial.
