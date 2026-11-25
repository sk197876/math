(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(13), pp. 335–336:
    a positive original E_m reduction of an irreducible
    variety has m equal to its actual ideal depth.
    Apply the proved model (10), upper-null representative
    from (11), and positive measure of every nonempty
    m-dimensional holomorphic manifold germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import StandardHermitianBasisValues UnitaryGroupHaar UnitaryComplexMapSealed HolomorphicRotatedCompositionInverse FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm InnerMetric
  HilbertFormCompactness OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  HolomorphicGermRing CommutativeIdealUP SetGermUP SetGermSealed SetGermOrder SetGermBooleanOrder
  HolomorphicGermVanishingSealed HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermSealed HolomorphicIdealVarietyGermExistence
  HolomorphicReductionActual HolomorphicReductionLociUP AnalyticReductionDepthUP HolomorphicDepthSealed
  HolomorphicRotatedGermIdeal HolomorphicRotatedIdealDepth HolomorphicRotatedIdealRecovery
  HolomorphicPrimeLocalModelUP HolomorphicPrimeLocalModelLaws Federer3412PrimeReduction
  FunctionalHolomorphicManifold HolomorphicGermHigherDegreeNull HolomorphicSubmanifoldGermNonNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ReductionDimension.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation E:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).

(** Source for [holomorphic_prime_positive_reduction_dimension]:
    the uniqueness of the possible positive E_m index
    in 3.4.8(13), pp. 335–336. The prime
    ideal is an actual vanishing ideal. No measure,
    model or dimension-comparison conclusion is assumed. *)
Theorem holomorphic_prime_positive_reduction_dimension (I:set G) (m:'I_n) (g:O):
  is_prime_commutative_ideal I ->(exists sigma:@set_germ_space E 0,I=ideal sigma) ->
  (0<m)%N ->
  @holomorphic_reduction_actual_E R X Herm hHerm n e he omega I (widen_ord (leqnSn n) m) g ->
  depth I=(m:nat).
Proof.
move=>hPrime [sigma hVanishing] hPositive hEm.
have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
have hON:=@standard_hermitian_basis_orthonormal R n.
have hTail:forall j:'I_n,(m<=j)%N ->@holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g.
  exact:((holomorphic_reduction_E_membership
    (@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega I) m g).1 hEm).2.1.
have hDepthBound:(depth I<=m)%N.
  apply:(analytic_reduction_depth_minimal (@HolomorphicDepth.laws R X Herm hHerm n e he omega I)).
  by exists g.
apply/eqP;rewrite eqn_leq hDepthBound /=.
case:(leqP m (depth I))=>// hSmall.
have hMN:(m<=n)%N:=ltnW (ltn_ord m).
have [k [first [U [d [b [f [Z [K [hI [hIg [hK [hModel hNonempty]]]]]]]]]]]]:=
  @federer_3_4_12_10 R n e he omega hDual I g m hMN hPrime hPositive hEm.
have hRecovered:=@given_holomorphic_vanishing_ideal_variety_recovery R X NX hNX 0 I hI sigma hVanishing.
have hZNonempty:=hNonempty hRecovered.
pose Ig:=@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g.
pose alpha:=@HolomorphicIdealVarietyGerm.value R X NX hNX 0 Ig hIg.
have hRotatedRecovery:=@holomorphic_rotated_ideal_variety_recovery R X Herm hHerm (n+n) eR heR
  I g hI hIg hRecovered.
have [mulO [invO [unitO [hO [mulU [invU [unitU [hU [hLocal hHaar]]]]]]]]]:=
  @unitary_group_haar_exists R X Herm hHerm (n+n) eR heR.
have hRotatedDepth:=@holomorphic_rotated_ideal_depth R X Herm hHerm n e he mulO invO unitO hO mulU invU unitU hU omega I g.
have hAlphaDepth:(depth (ideal alpha)<m)%N.
  rewrite -hRotatedRecovery hRotatedDepth;exact:hSmall.
have hVariety:=@HolomorphicIdealVarietyGermUP.holomorphic_ideal_variety_germ_is_variety R X NX hNX 0 Ig alpha
  (@HolomorphicIdealVarietyGerm.laws R X NX hNX 0 Ig hIg).
have hDoubled:(depth (ideal alpha)+depth (ideal alpha)<m+m)%N.
  by rewrite !addnn ltn_double.
have [S [hSGerm hNull]]:=@holomorphic_germ_higher_degree_null_representative R n alpha (m+m) hVariety hDoubled.
have hFields:=hModel.
do 15 (case:hFields=>_ hFields).
have hManifold:=functional_holomorphic_submanifold_holomorphic hFields.1.
have hJoin:=holomorphic_prime_local_model_variety hModel.
have hSub:set_germ_subset (@set_germ E 0 Z) (@set_germ E 0 S).
  rewrite hSGerm /alpha hJoin;exact:set_germ_subset_join_right.
exfalso;exact:(holomorphic_submanifold_germ_nonnull hManifold hZNonempty hSub hNull).
Qed.
End ReductionDimension.
