(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), pp. 327, 333–335:
    complete the original irreducible-germ induction case.
    The actual depth selects E_m; proved (10) supplies
    its entire prime model. Construct the strata in
    those coordinates, then return every law and actual
    representative by the proved orthogonal transport. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import StandardHermitianBasisValues UnitaryComplexMapSealed UnitaryGroupHaar HolomorphicRotatedCompositionInverse FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
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
  HolomorphicStratificationUnitaryPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IrreducibleStratification.
Variable R:realType.
Variable m:nat.
Hypothesis hInduction:forall d,(d<m.+1)%N ->holomorphic_stratification_at_bound R d.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).
Local Notation hON:=(@standard_hermitian_basis_orthonormal R n).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).

(** Source for [holomorphic_irreducible_stratification_from_induction]:
    every corrected assertion for an original nonempty
    irreducible alpha of positive dimension in
    3.4.12, p. 339, extending 3.4.8(11), pp. 333–335. No coordinate
    choice, regular model, finite component bound or
    original ideal recovery is an extra hypothesis. *)
Theorem holomorphic_irreducible_stratification_from_induction (U H U0 S0:set X):
  U 0 ->@is_finite_holomorphic_variety R X NX hNX U H ->
  U0 0 ->@is_finite_holomorphic_variety R X NX hNX U0 S0 ->
  @is_nonempty_irreducible_holomorphic_germ R X NX hNX 0 (germ H) ->
  depth (ideal (germ H)) = m.+1 ->
  exists mu,exists V S G:'I_mu->set X,
    @is_holomorphic_finite_stratification R n (germ H) (germ S0) m.+1 U0 S0 mu V S G /\
    forall i,S i `<=` H.
Proof.
move=>hU0 hH hU00 hS0 hIrreducible hDepth.
case:(pselect (set_germ_subset (germ H) (germ S0)))=>hContained.
- have hEmpty:@SetGerms.meet T 0 (germ H) (@SetGerms.neg T 0 (germ S0)) = germ set0.
    have hUnion:set_germ_subset (germ H) (@SetGerms.join T 0 (germ S0) (germ set0)).
      by rewrite set_germ_union_empty.
    apply:set_germ_subset_empty.
    exact:(@set_germ_difference_union_cancel T 0 (germ H) (germ set0) (germ S0) hUnion).
  exists 0%N,(fun _=>set0),(fun _=>set0),(fun _=>set0);split.
  + exact:holomorphic_empty_stratification hEmpty.
  + by move=>i;have:=ltn_ord i;rewrite ltn0.
- case:(eqVneq n m.+1)=>hEqual.
  + subst n;exact:(@holomorphic_full_dimensional_stratification_from_induction R m hInduction U H U0 S0
      hU0 hH hU00 hS0 hIrreducible.2 hDepth).
  + have hMN:(m.+1<=n)%N.
      have hBound:=analytic_reduction_depth_bound (@HolomorphicDepth.laws R X Herm hHerm n e he omega (ideal (germ H))).
      by rewrite hDepth in hBound.
    have hMNStrict:(m.+1<n)%N.
      rewrite ltn_neqAle eq_sym hEqual hMN;by [].
    pose mi:'I_n:=Ordinal hMNStrict.
    pose I:set [the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)]:=ideal (germ H).
    have hPrime:is_prime_commutative_ideal I.
      exact:(@holomorphic_irreducible_proper_prime_equivalence R X NX hNX 0 (germ H) hIrreducible.1.1).1 hIrreducible.
    have hDual i j:omega i (e j) = if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
    have [g hEm]:=@holomorphic_prime_depth_reduction_E_exists R X Herm hHerm n e he omega hDual hON
      I mi hPrime (ltn0Sn m) hDepth.
    have [k [first [Y0 [delta [b [f [Z [K [hI [hIg [hK [hModel hModelNonempty]]]]]]]]]]]]:=
      @federer_3_4_12_10 R n e he omega hDual I g mi hMN hPrime (ltn0Sn m) hEm.
    pose u:=@UnitaryComplexMap.value R X Herm hHerm (n+n) eR heR g.
    have hUBound:=@norm_finite_linear_bounded R XR XR NX NX hNX hNX (n+n) eR heR (complex_hom_real u).
    have hU:=@norm_bounded_linear_continuous R XR XR NX NX hNX hNX (complex_hom_real u) hUBound.
    have hUZ:u 0 = 0:=linear0 u.
    have hUH:=finite_holomorphic_linear_pullback hUBound hH.
    have hUS0:=finite_holomorphic_linear_pullback hUBound hS0.
    have hRotatedIdeal:=@holomorphic_rotated_vanishing_ideal R X Herm hHerm (n+n) eR heR g H.
    pose Ig:=@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g.
    have hRecovered:=@given_holomorphic_vanishing_ideal_variety_recovery R X NX hNX 0 Ig hIg
      (germ (u @^-1` H)) hRotatedIdeal.
    have hHRotated:@is_holomorphic_variety_germ R X NX hNX 0 (germ (u @^-1` H)).
      exists (u @^-1` U),(u @^-1` H);split;first by change (U (u 0));rewrite hUZ.
      by split.
    have hVariety:=@HolomorphicIdealVarietyGermUP.holomorphic_ideal_variety_germ_is_variety R X NX hNX 0 Ig
      (@HolomorphicIdealVarietyGerm.value R X NX hNX 0 Ig hIg) (@HolomorphicIdealVarietyGerm.laws R X NX hNX 0 Ig hIg).
    have hHGerm:germ (u @^-1` H) = @HolomorphicIdealVarietyGerm.value R X NX hNX 0 Ig hIg.
      apply:(@holomorphic_variety_germ_ideal_injective R X NX hNX 0
        (germ (u @^-1` H)) (@HolomorphicIdealVarietyGerm.value R X NX hNX 0 Ig hIg) hHRotated hVariety).
      by rewrite -hRotatedIdeal -hRecovered.
    have hTail:forall j:'I_n,(m.+1<=j)%N ->@holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g.
      have hE:=(holomorphic_reduction_E_membership
        (@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega I) mi g).1 hEm.
      exact:hE.2.1.
    have [mulO [invO [unitO [hO [mulU [invU [unitU [hGroup [hLocal hHaar]]]]]]]]]:=
      @unitary_group_haar_exists R X Herm hHerm (n+n) eR heR.
    pose v:=@UnitaryComplexMap.value R X Herm hHerm (n+n) eR heR (invU g).
    have [hVU hUV]:=@unitary_complex_original_inverse R X Herm hHerm n e he
      mulO invO unitO hO mulU invU unitU hGroup g.
    have hVBound:=@norm_finite_linear_bounded R XR XR NX NX hNX hNX (n+n) eR heR (complex_hom_real v).
    have hV:=@norm_bounded_linear_continuous R XR XR NX NX hNX hNX (complex_hom_real v) hVBound.
    have hVZ:v 0 = 0:=linear0 v.
    have hNotRotated:~set_germ_subset (@HolomorphicIdealVarietyGerm.value R X NX hNX 0 Ig hIg)
        (germ (u @^-1` S0)).
      rewrite -hHGerm;move=>hSub;apply:hContained.
      exact:(@set_germ_inverse_preimage_subset_reflect T T u v 0 0 H S0 hV hVZ hUV hSub).
    have hSource0:(u @^-1` U) 0 by change (U (u 0));rewrite hUZ.
    have hStart0:(u @^-1` U0) 0 by change (U0 (u 0));rewrite hUZ.
    have [mu [V [S [G [hLaws hInside]]]]]:=@holomorphic_prime_model_stratification_from_induction
      R n m hMN hInduction I g hIg k first Y0 delta b f Z K hK
      (u @^-1` U) (u @^-1` H) (u @^-1` U0) (u @^-1` S0)
      hPrime hModel hRecovered hTail hSource0 hUH hHGerm hStart0 hUS0 hNotRotated.
    rewrite -hHGerm in hLaws.
    have hBack:=@holomorphic_stratification_unitary_pullback R n (invU g)
      (u @^-1` H) (u @^-1` U0) (u @^-1` S0) m.+1 mu V S G hLaws.
    have hCancel E:v @^-1` (u @^-1` E) = E.
      apply:funext=>x;change (E (u (v x)) = E x);by rewrite hUV.
    rewrite !hCancel in hBack.
    exists mu,(fun i=>v @^-1` V i),(fun i=>v @^-1` S i),(fun i=>v @^-1` G i);split.
    * exact:hBack.
    * move=>i x hx;have hMember:=hInside i (v x) hx.
      change (H (u (v x))) in hMember;by rewrite hUV in hMember.
Qed.
End IrreducibleStratification.
