(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 332–333:
    the actual local model has nonempty
    remainder germ under the original
    vanishing-ideal hypothesis. Transfer that hypothesis
    through the actual orthogonal map and
    apply the original contradiction argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric LinearBasis GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness OrthogonalGroupTopology HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing
  CommutativeIdealUP SetGermUP HolomorphicGermVanishingSealed HolomorphicIdealVarietyGermSealed HolomorphicRotatedGermIdeal
  HolomorphicPrefixGermMap HolomorphicPrimeLocalModelUP HolomorphicPrimeLocalModelLaws HolomorphicRotatedIdealRecovery
  HolomorphicPrimeVarietyNonempty.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Nonempty.
Variable R:realType.
Variables n m:nat.
Hypothesis hMN:(m<=n)%N.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Y:=(coordinate_space (ComplexScalars.C R) m).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation NY:=(@holomorphic_coordinate_norm R m).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R m)).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Local Notation Top:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable P:Hom X Y.
Variable I:set G.
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Variable g:@unitary_group R X Herm hHerm (n+n) eR heR.
Local Notation Ig:=(@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g).
Variable hI:is_finitely_generated_commutative_ideal I.
Variable hIg:is_finitely_generated_commutative_ideal Ig.
Variable k:nat.
Variable first:'I_(n-m).
Variable U:set Y.
Variable d:@holomorphic_representative_type R Y NY hNY 0.
Variable b:'I_(n-m)->'I_k->@holomorphic_representative_type R Y NY hNY 0.
Variable f:'I_(n-m)->@holomorphic_representative_type R X NX hNX 0.
Variable Z:set X.
Variable K:set G.
Variable hK:is_finitely_generated_commutative_ideal K.

(** Source for [holomorphic_prime_local_model_nonempty_original]:
    gamma_0(Z) differs from the empty
    germ when I=ideal(var I),
    3.4.12, p. 339, extending 3.4.8(10), pp. 332–333.
    The hypothesis concerns the original I;
    its transfer to I_g is proved. *)
Theorem holomorphic_prime_local_model_nonempty_original:
  @is_holomorphic_prime_local_model R n m hMN e he omega P Ig hIg k first U d b f Z K hK ->
  I = @HolomorphicSetIdeal.value R X NX hNX 0 (@HolomorphicIdealVarietyGerm.value R X NX hNX 0 I hI) ->
  @set_germ Top 0 Z<>@set_germ Top 0 set0.
Proof.
move=>hModel hRecovered.
have hRotated:=@holomorphic_rotated_ideal_variety_recovery R X Herm hHerm (n+n) eR heR I g hI hIg hRecovered.
pose E:=@holomorphic_prefix_germ_map R X NX hNX n e he omega m hMN.
have hOutside:=@holomorphic_prime_local_model_delta_outside R n m hMN e he omega P Ig hIg
  k first U d b f Z K hK hModel.
have hEnlarged:=@holomorphic_prime_local_model_enlarged_ideal R n m hMN e he omega P Ig hIg
  k first U d b f Z K hK hModel.
have hVariety:=@holomorphic_prime_local_model_variety R n m hMN e he omega P Ig hIg
  k first U d b f Z K hK hModel.
have hContains:K (E (holomorphic_germ d)).
  apply:(generated_commutative_ideal_contains hEnlarged);right;by [].
exact:(@holomorphic_variety_remainder_nonempty R X NX hNX 0 Ig K hIg hK
  (E (holomorphic_germ d)) (@set_germ Top 0 Z) hRotated hOutside hContains hVariety).
Qed.
End Nonempty.
