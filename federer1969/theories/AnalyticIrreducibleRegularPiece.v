(** Federer (1969), 3.4.8(16), p. 337:
    assemble the original regular piece in the original
    coordinates from the proved prime reduction theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm HilbertFormCompactness NormFiniteLinearBound
  NormBoundedLinearTopology OrthogonalGroupTopology OrthogonalGroupHaarMeasure AnalyticGermRing
  AnalyticGermNoetherian CommutativeIdealUP SetGermUP SetGermSealed SetGermExistence SetGermLaws SetGermOrder SetGermBoundary SetGermDifferenceOrder
  SetGermInversePreimageOrder AnalyticVarietyGermUP AnalyticIrreducibleGermUP AnalyticIrreducibleProperPrime
  FiniteAnalyticVarietyUP FiniteAnalyticLinearPullback GermVanishingSealed GermVanishingIdeal
  AnalyticDepthSealed AnalyticReductionDepthUP AnalyticReductionActual AnalyticReductionLociUP
  AnalyticPrimeDepthReductionExists AnalyticRotatedGermIdeal AnalyticRotatedVanishingIdeal
  AnalyticRotatedIdealRecovery AnalyticVarietyGermSeparation IdealVarietyGermUP IdealVarietyGermSealed
  AnalyticFiniteStratificationUP AnalyticStratificationInductionUP AnalyticEmptyStratification
  AnalyticFullDimensionalStratification Federer348PrimeReduction AnalyticPrimeModelStratification
  AnalyticStratificationOrthogonalPullback AnalyticPrimeModelRegularCut
  FunctionalAnalyticWhole FunctionalAnalyticManifold FunctionalAnalyticLinearPullback
  AnalyticSubmanifoldUP AnalyticFullDimensionWholeGerm AnalyticRotatedVarietyRepresentative
  AnalyticVarietyGermBooleanClosure SetGermContinuousPreimage AnalyticPrimeLocalModelUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RegularPiece.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation hON:=(@euclidean_coordinate_orthonormal_family R n).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).

(** Source for [analytic_irreducible_regular_piece]: the actual
    m-dimensional analytic submanifold Z and proper exceptional
    germ beta in the proof of 3.4.8(16),
    p. 337. The positive full-dimensional endpoint uses
    the whole space. In the remaining case the
    original E_m theorem supplies (10) internally. *)
Theorem analytic_irreducible_regular_piece (alpha:@set_germ_space T 0):
  @is_nonempty_irreducible_analytic_germ R X NX hNX 0 alpha ->
  (0<depth (ideal alpha))%N ->
  exists beta:@set_germ_space T 0,exists Z:set X,
    @is_analytic_variety_germ R X NX hNX 0 beta /\
    @is_euclidean_analytic_submanifold R n (depth (ideal alpha)) Z /\
    alpha=@SetGerms.join T 0 beta (germ Z) /\~set_germ_subset alpha beta.
Proof.
move=>hAlpha hPositive.
pose m:=depth (ideal alpha).
have hBound:(m<=n)%N:=analytic_reduction_depth_bound
  (@AnalyticDepth.laws R X B hB n e he omega (ideal alpha)).
case:(eqVneq m n)=>hEqual.
- have hWhole:=@analytic_full_dimension_whole_germ R n alpha hAlpha.1.1 hAlpha.2 hEqual.
  exists (germ set0),setT;split;first exact:analytic_variety_germ_empty.
  split.
  + change (@is_euclidean_analytic_submanifold R n m setT).
    rewrite hEqual;exact:functional_analytic_submanifold_analytic (functional_analytic_whole R n).
  split.
  + rewrite set_germ_union_commutative set_germ_union_empty;exact:hWhole.
  + move=>hSub;apply:hAlpha.2;exact:set_germ_subset_empty hSub.
- have hStrict:(m<n)%N by rewrite ltn_neqAle hEqual hBound.
  pose mi:'I_n:=Ordinal hStrict.
  have [U [H [hU0 [hH hHGerm]]]]:=hAlpha.1.1.
  pose I:set [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]:=ideal alpha.
  have hPrime:is_prime_commutative_ideal I.
    exact:(@analytic_irreducible_proper_prime_equivalence R X NX hNX 0 alpha hAlpha.1.1).1 hAlpha.
  have hDual i j:omega i (e j) = if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
  have [g hEm]:=@analytic_prime_depth_reduction_E_exists R X B hB n e he hON omega hDual
    I mi hPrime hPositive erefl.
  have [k [first [Y0 [delta [b [f [Z [K [hI [hIg [hK [hModel hModelNonempty]]]]]]]]]]]]:=
    @federer_3_4_8_10 R n e he hON omega hDual I g mi hBound hPrime hPositive hEm.
  pose Ig:=@analytic_rotated_germ_ideal R X B hB n e he I g.
  have hOriginal:=@given_vanishing_ideal_variety_recovery R X NX hNX 0 I hI alpha erefl.
  have hRecovered:=@analytic_rotated_ideal_variety_recovery R X B hB n e he I g hI hIg hOriginal.
  have [beta [hBeta [hSplit hNot]]]:=@analytic_prime_model_regular_cut R n mi hBound
    I g hIg k first Y0 delta b f Z K hK hModel hRecovered.
  have [W [D [hW0 [hD hDGerm]]]]:=hBeta.
  pose u:=@orthogonal_element_map R X B hB n e he g.
  have hRotated:=@analytic_rotated_variety_representative R X B hB n e he I hI g hIg U H
    hU0 hH (esym (congr1 ideal hHGerm)).
  have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
  pose v:=@orthogonal_element_map R X B hB n e he (invO g).
  have [hVU hUV]:=@orthogonal_element_inv R X B hB n e he mulO invO unitO hO g.
  have hUBound:=@norm_finite_linear_bounded R X X NX NX hNX hNX n e he u.
  have hU:=@norm_bounded_linear_continuous R X X NX NX hNX hNX u hUBound.
  have hVBound:=@norm_finite_linear_bounded R X X NX NX hNX hNX n e he v.
  have hV:=@norm_bounded_linear_continuous R X X NX NX hNX hNX v hVBound.
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
    exact:finite_analytic_linear_pullback hVBound hD.
  split.
  + have hFields:=hModel;do 15 (case:hFields=>_ hFields).
    exact:functional_analytic_submanifold_analytic
      (functional_analytic_linear_pullback hVBound hOnto hFields.1).
  split.
  + by rewrite (@set_germ_union_equation T 0 _ _ _ (@SetGerms.laws T 0)).
  + move=>hContained;apply:hNot.
    rewrite hRotated -hDGerm.
    apply:(@set_germ_inverse_preimage_subset_reflect T T v u 0 0 (u @^-1` H) D
      hU (linear0 u) hVU).
    by rewrite hCancel hHGerm.
Qed.
End RegularPiece.
