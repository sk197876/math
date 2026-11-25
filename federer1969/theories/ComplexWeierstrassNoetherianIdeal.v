(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: the
    original holomorphic division theorem and a Noetherian
    transverse ring give finite generators for the
    original ideal. The actual finite remainder module
    supplies the generators; they are not theorem premises. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus HolomorphicLinear Hom RealNormUP NormDifferentialUP HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermRing CommutativeIdealUP CommutativeIdealSealed RingSubmoduleUP RingSubmoduleSealed
  RingScalarRestriction NoetherianIdealRemainders ComplexWeierstrassRegularUP ComplexWeierstrassDivisionUP
  ComplexWeierstrassDivisionWithTransverse ComplexWeierstrassTransverseUP ComplexWeierstrassTransversePullback
  ComplexWeierstrassFunctionalPower ComplexWeierstrassRemainderModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [complex_weierstrass_noetherian_ideal]: the
    original proper ideal has finite generators by
    I = O Phi + (M intersect I), 3.4.7,
    p. 325. The divisor retains its actual
    directional order; no finite basis or fixed
    set of coefficients is added to the ideal's hypotheses. *)
Theorem complex_weierstrass_noetherian_ideal (R:realType) (X K:lmodType (ComplexScalars.C R))
    (NX:X->R) (NK:K->R) (hNX:is_complex_norm NX) (hNK:is_complex_norm NK)
    (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K)
    (hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection)
    k (Phi:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)
    (I:set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)):
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->
  is_noetherian_commutative_ring
    [the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))] ->
  is_commutative_ideal I ->I Phi ->is_complex_weierstrass_regular_germ hNX Phi k v ->
  is_finitely_generated_commutative_ideal I.
Proof.
move=>hXi hA hI hPhi hRegular.
pose A:=[the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))].
pose B:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
pose embed:=@complex_weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit.
pose V:=[the lmodType A of (ring_restricted_space embed B^o)].
have [fXi [hXiValues _]]:=@complex_weierstrass_functional_power_representative R X NX hNX xi 1 hXi.
have hXiActual x:holomorphic_representative_value fXi x = xi x by rewrite hXiValues expr1.
pose powers:'I_k->V:=fun i=>(holomorphic_germ fXi:B)^+i.
pose F:=map powers (enum 'I_k).
pose M:=@GeneratedRingSubmodule.value A V [set x|x \in F].
have hM:=@GeneratedRingSubmodule.laws A V [set x|x \in F].
have hFiniteM:is_finitely_generated_ring_submodule M by exists F.
have hGenerators i:(i<k)%N ->M ((holomorphic_germ fXi:B)^+i).
  move=>hi;apply:(generated_ring_submodule_contains hM).
  apply/mapP;exists (Ordinal hi);first exact:mem_enum.
  reflexivity.
apply:(@noetherian_ideal_from_remainders A B embed Phi M I hA hFiniteM hI hPhi)=>Psi hPsi.
have [Q [rho [hDivision _]]]:=@complex_weierstrass_division_with_transverse R X K NX NK hNX hNK
  v xi inclusion projection k Phi Psi hSplit hXi hRegular.
exists Q,rho;split.
- exact:(@complex_weierstrass_remainder_in_transverse_module R X K NX NK hNX hNK
    v xi inclusion projection hSplit k fXi M rho hXi hXiActual
    (generated_ring_submodule_laws hM) hGenerators
    (complex_weierstrass_division_polynomial_remainder hDivision)).
- exact:complex_weierstrass_division_identity hDivision.
Qed.
