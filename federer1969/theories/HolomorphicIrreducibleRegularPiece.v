(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(16), p. 337:
    assemble the original regular piece in the original
    coordinates from the proved prime reduction theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FunctionalHolomorphicWhole StandardHermitianBasisValues UnitaryGroupHaar UnitaryComplexMapSealed HolomorphicRotatedCompositionInverse FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm HilbertFormCompactness NormFiniteLinearBound
  NormBoundedLinearTopology OrthogonalGroupTopology OrthogonalGroupHaarMeasure HolomorphicGermRing
  HolomorphicGermNoetherian CommutativeIdealUP SetGermUP SetGermSealed SetGermExistence SetGermLaws SetGermOrder SetGermBoundary SetGermDifferenceOrder
  SetGermInversePreimageOrder HolomorphicVarietyGermUP HolomorphicIrreducibleGermUP HolomorphicIrreducibleProperPrime
  FiniteHolomorphicVarietyUP FiniteHolomorphicLinearPullback HolomorphicGermVanishingSealed HolomorphicGermVanishingIdeal
  HolomorphicDepthSealed AnalyticReductionDepthUP HolomorphicReductionActual HolomorphicReductionLociUP
  HolomorphicPrimeDepthReductionExists HolomorphicRotatedGermIdeal HolomorphicRotatedVanishingIdeal
  HolomorphicRotatedIdealRecovery HolomorphicVarietyGermSeparation HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermSealed
  HolomorphicFiniteStratificationUP HolomorphicStratificationInductionUP HolomorphicEmptyStratification
  HolomorphicFullDimensionalStratification Federer3412PrimeReduction HolomorphicPrimeModelStratification
  HolomorphicStratificationUnitaryPullback HolomorphicPrimeModelRegularCut
  FunctionalHolomorphicFullDimension FunctionalHolomorphicManifold FunctionalHolomorphicLinearPullback
  HolomorphicSubmanifoldUP HolomorphicFullDimensionWholeGerm HolomorphicRotatedVarietyRepresentative
  HolomorphicVarietyGermBooleanClosure SetGermContinuousPreimage HolomorphicPrimeLocalModelUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RegularPiece.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).
Local Notation hON:=(@standard_hermitian_basis_orthonormal R n).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).

(** Source for [holomorphic_irreducible_regular_piece]: the actual
    m-dimensional holomorphic submanifold Z and proper exceptional
    germ beta in the proof of 3.4.8(16),
    p. 337. The positive full-dimensional endpoint uses
    the whole space. In the remaining case the
    original E_m theorem supplies (10) internally. *)
Theorem holomorphic_irreducible_regular_piece (alpha:@set_germ_space T 0):
  @is_nonempty_irreducible_holomorphic_germ R X NX hNX 0 alpha ->
  (0<depth (ideal alpha))%N ->
  exists beta:@set_germ_space T 0,exists Z:set X,
    @is_holomorphic_variety_germ R X NX hNX 0 beta /\
    @is_holomorphic_submanifold R X NX hNX (depth (ideal alpha)) Z /\
    alpha=@SetGerms.join T 0 beta (germ Z) /\~set_germ_subset alpha beta.
Proof.
move=>hAlpha hPositive.
pose m:=depth (ideal alpha).
have hBound:(m<=n)%N:=analytic_reduction_depth_bound
  (@HolomorphicDepth.laws R X Herm hHerm n e he omega (ideal alpha)).
case:(eqVneq m n)=>hEqual.
- have hWhole:=@holomorphic_full_dimension_whole_germ R n alpha hAlpha.1.1 hAlpha.2 hEqual.
  exists (germ set0),setT;split;first exact:holomorphic_variety_germ_empty.
  split.
  + change (@is_holomorphic_submanifold R X NX hNX m setT).
    rewrite hEqual;exact:functional_holomorphic_submanifold_holomorphic (functional_holomorphic_whole R n).
  split.
  + rewrite set_germ_union_commutative set_germ_union_empty;exact:hWhole.
  + move=>hSub;apply:hAlpha.2;exact:set_germ_subset_empty hSub.
- have hStrict:(m<n)%N by rewrite ltn_neqAle hEqual hBound.
  pose mi:'I_n:=Ordinal hStrict.
  have [U [H [hU0 [hH hHGerm]]]]:=hAlpha.1.1.
  pose I:set [the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)]:=ideal alpha.
  have hPrime:is_prime_commutative_ideal I.
    exact:(@holomorphic_irreducible_proper_prime_equivalence R X NX hNX 0 alpha hAlpha.1.1).1 hAlpha.
  have hDual i j:omega i (e j) = if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
  have [g hEm]:=@holomorphic_prime_depth_reduction_E_exists R X Herm hHerm n e he omega hDual hON
    I mi hPrime hPositive erefl.
  have [k [first [Y0 [delta [b [f [Z [K [hI [hIg [hK [hModel hModelNonempty]]]]]]]]]]]]:=
    @federer_3_4_12_10 R n e he omega hDual I g mi hBound hPrime hPositive hEm.
  pose Ig:=@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g.
  have hOriginal:=@given_holomorphic_vanishing_ideal_variety_recovery R X NX hNX 0 I hI alpha erefl.
  have hRecovered:=@holomorphic_rotated_ideal_variety_recovery R X Herm hHerm (n+n) eR heR I g hI hIg hOriginal.
  have [beta [hBeta [hSplit hNot]]]:=@holomorphic_prime_model_regular_cut R n mi hBound
    I g hIg k first Y0 delta b f Z K hK hModel hRecovered.
  have [W [D [hW0 [hD hDGerm]]]]:=hBeta.
  pose u:=@UnitaryComplexMap.value R X Herm hHerm (n+n) eR heR g.
  have hRotated:=@holomorphic_rotated_variety_representative R X Herm hHerm n e he I hI g hIg U H
    hU0 hH (esym (congr1 ideal hHGerm)).
  have [mulO [invO [unitO [hO [mulU [invU [unitU [hU [hLocal hHaar]]]]]]]]]:=
    @unitary_group_haar_exists R X Herm hHerm (n+n) eR heR.
  pose v:=@UnitaryComplexMap.value R X Herm hHerm (n+n) eR heR (invU g).
  have [hVU hUV]:=@unitary_complex_original_inverse R X Herm hHerm n e he mulO invO unitO hO mulU invU unitU hU g.
  have hUBound:=@norm_finite_linear_bounded R XR XR NX NX hNX hNX (n+n) eR heR (complex_hom_real u).
  have hUC:=@norm_bounded_linear_continuous R XR XR NX NX hNX hNX (complex_hom_real u) hUBound.
  have hVBound:=@norm_finite_linear_bounded R XR XR NX NX hNX hNX (n+n) eR heR (complex_hom_real v).
  have hV:=@norm_bounded_linear_continuous R XR XR NX NX hNX hNX (complex_hom_real v) hVBound.
  have hV0:v 0 = 0:=linear0 v.
  have hOnto y:exists x,v x = y by exists (u y);exact:hVU y.
  have hCancel E:v @^-1` (u @^-1` E) = E.
    apply:funext=>x;change (E (u (v x)) = E x);by rewrite hUV.
  have hUnion:alpha=germ ((v @^-1` D) `|` (v @^-1` Z)).
    rewrite hRotated -hDGerm in hSplit.
    rewrite (@set_germ_union_equation T 0 _ _ _ (@SetGerms.laws T 0)) in hSplit.
    have hBack:=@set_germ_continuous_preimage_equality T T v 0 0
      (u @^-1` H) (D `|` Z) hV hV0 hSplit.
    rewrite hCancel hHGerm in hBack;exact:hBack.
  exists (germ (v @^-1` D)),(v @^-1` Z);split.
  + exists (v @^-1` W),(v @^-1` D);split;first by change (W (v 0));rewrite hV0.
    split;last exact:erefl.
    exact:finite_holomorphic_linear_pullback hVBound hD.
  split.
  + have hFields:=hModel;do 15 (case:hFields=>_ hFields).
    exact:functional_holomorphic_submanifold_holomorphic
      (functional_holomorphic_linear_pullback hVBound hOnto hFields.1).
  split.
  + by rewrite (@set_germ_union_equation T 0 _ _ _ (@SetGerms.laws T 0)).
  + move=>hContained;apply:hNot.
    rewrite hRotated -hDGerm.
    apply:(@set_germ_inverse_preimage_subset_reflect T T v u 0 0 (u @^-1` H) D
      hUC (linear0 u) hVU).
    by rewrite hCancel hHGerm.
Qed.
End RegularPiece.
