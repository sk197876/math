(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    pp. 326, 329–330: every original prime ideal and original
    B-tail point gives C_m and the complete B-tail for almost
    every actual suffix unitary rotation. All quotient and fraction
    objects are local witnesses supplied by the existing opaque interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import HolomorphicGermFormsSealed HolomorphicReductionLociUP HolomorphicReductionActual
  HolomorphicRotatedGermIdeal HolomorphicUnitaryPullbackComposition PointedHolomorphicLinearPullbackForms
  HolomorphicCoordinateSubringFamilySealed UnitaryCoordinateFixing HolomorphicUnitaryPrefixInvariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import AnalyticReductionDepthUP HolomorphicDepthSealed HolomorphicReductionHaarSuffix HolomorphicReductionATailDepthDrop UnitaryCoordinateFixingHaar MeasureAlmostPositiveWitness TopologicalGroupLaws UnitaryGroupClosed.
From Federer Require Import OrthonormalFamilies Bilinear TensorUP ComplexScalarLaws HermitianComplexLinearity HermitianBasisCoordinates UnitaryHermitianPreservation OrdinalCoordinateTail OrdinalCoordinateTailSum Annihilator FiniteDualDimension DualityAnnihilator.
Import ComplexScalarTheory.
From Federer Require Import UnitarySuffixCovector FiniteCoordinates HolomorphicCoordinateNorm
  HolomorphicScalarsSealed HolomorphicCoordinateGermsSealed HolomorphicPrefixGermMap
  HolomorphicReductionActual HolomorphicReductionLociUP HolomorphicRotatedIdealPrime
  HolomorphicReductionOriginalFieldInputs HolomorphicReductionPrimitiveHaar HolomorphicPrimitiveRotationRelations
  HolomorphicIntegralRotationDirections CommutativeIdealUP CommutativeSubringUP
  CommutativeQuotientSealed CommutativeQuotientLaws FractionFieldSealed CoefficientFractionFieldSealed
  HaarIntegralUP MeasureUP MeasureAlmostBasic.
Section DepthSelection.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hH).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@orthogonal_group R XR B hB (n+n) eR heR).
Local Notation U:=(@unitary_group R X H hH (n+n) eR heR).
Local Notation M:=(@holomorphic_germ_metric R X NX hNXR 0).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Local Notation mapg:=(fun g:U=>@UnitaryComplexMap.value R X H hH (n+n) eR heR g).
Local Notation P:=(fun g:U=>@holomorphic_unitary_germ_map R X H hH (n+n) eR heR g).
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable hDual:forall i k,omega i (e k)=if i==k then 1 else 0.
Variable hON:orthonormal_family H e.
Variable I:set G.

(** Source for [holomorphic_prime_depth_reduction_E_exists]: the
    actual least positive depth selects an original E_m point,
    extending 3.4.8(11), p. 334, under 3.4.12, p. 339.
    Apply the proved suffix Haar theorem. Original A-tail depth
    reduction excludes A_m without a generic-direction assumption. *)
Theorem holomorphic_prime_depth_reduction_E_exists (m:'I_n):
  is_prime_commutative_ideal I ->(0<m)%N ->
  @HolomorphicDepth.value R X H hH n e he omega I = (m:nat) ->
  exists g,@holomorphic_reduction_actual_E R X H hH n e he omega I
    (widen_ord (leqnSn n) m) g.
Proof.
move=>hPrime hPositive hDepth.
have hLaws:=@HolomorphicDepth.laws R X H hH n e he omega I.
have [g hAll]:=analytic_reduction_depth_attained hLaws.
rewrite hDepth in hAll.
have [mulO [invO [unitO [hO [mulU [invU [unitU [hU [hLocalU
  [mulF [invF [unitF [hF [hLocalF [mu hMu]]]]]]]]]]]]]]]:=
  @unitary_coordinate_fixing_haar_exists R X H hH (n+n) eR heR n e [set i:'I_n|(i<m)%N].
have hAlmost:=@holomorphic_reduction_suffix_haar_almost_C_B R X H hH n e he omega hDual hON
  I g m mulO invO unitO hO mulU invU unitU hU mulF invF unitF hF mu hPrime hAll hMu.1.
have [lambda [hLambda hMeasure hRest]]:=hMu.1.
have hMass:mu setT<>0%E.
  rewrite hMu.2;move=>hEqual.
  have hOne:(1:R) = 0:=EFin_inj hEqual.
  have hDifferent:(1:R)!=0 by rewrite oner_eq0.
  apply:(negP hDifferent);apply/eqP;exact:hOne.
have [q [_ [hC hAllRot]]]:=measure_almost_positive_set_witness hMeasure hMass hAlmost.
pose g':=mulU g (set_val q).
have hPrevBound:(m.-1<n)%N:=leq_ltn_trans (leq_pred m) (ltn_ord m).
pose j:'I_n:=Ordinal hPrevBound.
have hPrevSucc:(j:nat).+1 = (m:nat) by rewrite /j /= prednK.
have hDepthPrev:@HolomorphicDepth.value R X H hH n e he omega I = (j:nat).+1 by rewrite hPrevSucc.
have hTailPrev:forall k:'I_n,((j:nat).+1<=k)%N ->
    @holomorphic_reduction_actual_B R X H hH n e he omega I k g'.
  move=>k;rewrite hPrevSucc;exact:hAllRot k.
have hIndex:(@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) = widen_ord (leqnSn n) m.
  apply:val_inj;exact:hPrevSucc.
have hExcluded:~@holomorphic_reduction_actual_A R X H hH n e he omega I
    (widen_ord (leqnSn n) m) g'.
  move=>hA;rewrite -hIndex in hA.
  have hDrop:=@holomorphic_reduction_A_tail_depth_drop R X H hH n e he hON omega hDual
    I hPrime.1 hPrime.2.1 j g' hTailPrev hA.
  by rewrite hDepthPrev ltnn in hDrop.
exists g';apply:(holomorphic_reduction_E_membership
  (@holomorphic_reduction_actual_laws R X H hH n e he omega I) m g').2.
by split;last split.
Qed.
End DepthSelection.
