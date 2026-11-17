(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 327, 330–333:
    the complete original prime-ideal local
    reduction theorem, including its nonempty-germ
    conclusion under I=ideal(var I).
    All objects remain local witnesses to
    the independently specified model laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric LinearBasis OrthonormalFamilies GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness OrthogonalGroupTopology NormDifferentialUP NormFiniteLinearBound
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing HolomorphicCoordinateGermsSealed
  FieldPrefixCoordinatesSealed HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws
  HolomorphicRotatedGermIdeal HolomorphicReductionActual HolomorphicReductionOriginalEquations
  SetGermUP SetGermSealed HolomorphicZeroGermSealed HolomorphicIdealVarietyGermSealed
  CommutativeIdealUP CommutativePolynomialUP CommutativePolynomialSealed
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed
  PointedHolomorphicFunctionalGermExistence OriginalHolomorphicPolynomialCylinderWitnesses OrdinalCoordinateTail
  HolomorphicPrimeLocalModelUP HolomorphicPrimeLocalModelAssembly HolomorphicReductionPrimeModelExistence
  HolomorphicGermNoetherian HolomorphicGermVanishingSealed HolomorphicPrimeLocalModelNonempty.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalPrimeModel.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family Herm e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Variable I:set G.
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Variable g:@unitary_group R X Herm hHerm (n+n) eR heR.
Variable m:'I_n.
Hypothesis hMN:((m:nat)<=n)%N.
Local Notation Y:=(coordinate_space (ComplexScalars.C R) m).
Local Notation NY:=(@holomorphic_coordinate_norm R m).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R m)).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)].
Local Notation PY:=(@holomorphic_representative_type R Y NY hNY 0).
Local Notation PX:=(@holomorphic_representative_type R X NX hNX 0).
Local Notation vy:=(@holomorphic_representative_value R Y NY hNY 0).
Local Notation vx:=(@holomorphic_representative_value R X NX hNX 0).
Local Notation Ig:=(@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g).
Local Notation P:=(@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega m hMN).
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation gamma:=(fun j:'I_n=>@HolomorphicCoordinateGerms.value R X NX (@holomorphic_coordinate_norm_laws R n) n e he omega j).

(** Source for [federer_3_4_12_10]:
    the original positive-dimensional prime reduction,
    3.4.12, p. 339, extending 3.4.8(10), pp. 327, 330–333.
    Retain the original E_m membership,
    all defining equations and coefficient values,
    variety decomposition, nonvanishing derivative,
    functional submanifold, local holomorphic covering,
    larger-ideal assertion and nonempty-germ conclusion. *)
Theorem federer_3_4_12_10:
  is_prime_commutative_ideal I ->(0<m)%N ->
  @holomorphic_reduction_actual_E R X Herm hHerm n e he omega I (widen_ord (leqnSn n) m) g ->
  exists k (first:'I_(n-m)) (U:set Y) (d:PY) (b:'I_(n-m)->'I_k->PY)
    (f:'I_(n-m)->PX) (Z:set X) (K:set G),
    exists (hI:is_finitely_generated_commutative_ideal I)
      (hIg:is_finitely_generated_commutative_ideal Ig) (hK:is_finitely_generated_commutative_ideal K),
      @is_holomorphic_prime_local_model R n m hMN e he omega P Ig hIg k first U d b f Z K hK /\
      (I = @HolomorphicSetIdeal.value R X NX hNX 0 (@HolomorphicIdealVarietyGerm.value R X NX hNX 0 I hI) ->
        @set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 Z <>
        @set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 set0).
Proof.
move=>hPrime hPositive hEm.
have [k [first [U [d [b [f [Z [K data]]]]]]]]:=
  @holomorphic_reduction_prime_local_model_exists R n e he omega hDual I g m hMN hPrime hPositive hEm.
have [hIg [hK hModel]]:=data.
have hI:=@finite_holomorphic_germ_ring_noetherian R X NX (@holomorphic_coordinate_norm_laws R n) n e 0 he I hPrime.1.
exists k,first,U,d,b,f,Z,K,hI,hIg,hK;split;first exact:hModel.
move=>hRecovered.
exact:(@holomorphic_prime_local_model_nonempty_original R n m hMN e he omega P I g hI hIg
  k first U d b f Z K hK hModel hRecovered).
Qed.
End OriginalPrimeModel.
