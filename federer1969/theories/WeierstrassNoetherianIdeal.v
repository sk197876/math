(** Federer (1969), 3.4.7, p. 325: the
    original analytic division theorem and a Noetherian
    transverse ring give finite generators for the
    original ideal. The actual finite remainder module
    supplies the generators; they are not theorem premises. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRing CommutativeIdealUP CommutativeIdealSealed RingSubmoduleUP RingSubmoduleSealed
  RingScalarRestriction NoetherianIdealRemainders WeierstrassRegularUP WeierstrassDivisionUP
  WeierstrassDivisionWithTransverse WeierstrassTransverseUP WeierstrassTransversePullback
  WeierstrassFunctionalPower WeierstrassRemainderModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_noetherian_ideal]: the
    original proper ideal has finite generators by
    I = O Phi + (M intersect I), 3.4.7,
    p. 325. The divisor retains its actual
    directional order; no finite basis or fixed
    set of coefficients is added to the ideal's hypotheses. *)
Theorem weierstrass_noetherian_ideal (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection)
    k (Phi:@analytic_germ_ring R X NX hNX 0)
    (I:set (@analytic_germ_ring R X NX hNX 0)):
  norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->
  is_noetherian_commutative_ring
    [the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))] ->
  is_commutative_ideal I ->I Phi ->is_weierstrass_regular_germ Phi k v ->
  is_finitely_generated_commutative_ideal I.
Proof.
move=>hXi hA hI hPhi hRegular.
pose A:=[the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))].
pose B:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
pose embed:=@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit.
pose V:=[the lmodType A of (ring_restricted_space embed B^o)].
have [fXi [hXiValues _]]:=@weierstrass_functional_power_representative R X NX hNX xi 1 hXi.
have hXiActual x:analytic_representative_value fXi x = xi x by rewrite hXiValues expr1.
pose powers:'I_k->V:=fun i=>(analytic_germ fXi:B)^+i.
pose F:=map powers (enum 'I_k).
pose M:=@GeneratedRingSubmodule.value A V [set x|x \in F].
have hM:=@GeneratedRingSubmodule.laws A V [set x|x \in F].
have hFiniteM:is_finitely_generated_ring_submodule M by exists F.
have hGenerators i:(i<k)%N ->M ((analytic_germ fXi:B)^+i).
  move=>hi;apply:(generated_ring_submodule_contains hM).
  apply/mapP;exists (Ordinal hi);first exact:mem_enum.
  reflexivity.
apply:(@noetherian_ideal_from_remainders A B embed Phi M I hA hFiniteM hI hPhi)=>Psi hPsi.
have [Q [rho [hDivision _]]]:=@weierstrass_division_with_transverse R X K NX NK hNX hNK
  v xi inclusion projection k Phi Psi hSplit hXi hRegular.
exists Q,rho;split.
- exact:(@weierstrass_remainder_in_transverse_module R X K NX NK hNX hNK
    v xi inclusion projection hSplit k fXi M rho hXi hXiActual
    (generated_ring_submodule_laws hM) hGenerators
    (weierstrass_division_polynomial_remainder hDivision)).
- exact:weierstrass_division_identity hDivision.
Qed.
