(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 330: the actual integral quotient supplies every original
    B_j witness after each suffix unitary rotation. Monicity and
    the original line Taylor theorem prove nonzero directional order. *)
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
From Federer Require Import TopologicalGroupLaws UnitaryGroupClosed.
From Federer Require Import OrthonormalFamilies Bilinear TensorUP ComplexScalarLaws HermitianComplexLinearity HermitianBasisCoordinates UnitaryHermitianPreservation OrdinalCoordinateTail OrdinalCoordinateTailSum Annihilator FiniteDualDimension DualityAnnihilator.
Import ComplexScalarTheory.
From Federer Require Import HolomorphicCoordinateGermsSealed HolomorphicCoordinateGermsExistence HolomorphicCoordinateLinearCombination HolomorphicGermRepresentatives HolomorphicScalarsSealed.
From Federer Require Import UnitarySuffixCovector.
From Federer Require Import HolomorphicCoordinateNorm FiniteCoordinates HolomorphicPrefixGermMap
  HolomorphicPrefixComplexScalars UnitaryPrimitiveCoordinateGerm CoefficientFractionFieldUP.
From Federer Require Import CommutativeQuotientUP CommutativeSubringUP CommutativeSubringLaws FractionFieldUP
  IntegralRingElementUP HolomorphicFixedPrefixPullback HolomorphicPrefixPolynomialSubring
  HolomorphicPrefixSubringMonotonicity HolomorphicPrefixGermSubring HolomorphicPrefixGermSubringLaws
  HolomorphicCoordinateSubringFamilyUP HolomorphicCoordinateSubringFamilySealed FieldPrefixCoordinatesUP
  FieldPrefixCoordinatesSealed FieldPrefixBasisValues HolomorphicPrefixGermMapLaws
  HolomorphicReductionLociUP HolomorphicReductionActual HolomorphicRotatedCompositionInverse
  HolomorphicMonicLineJet HolomorphicMonicPrefixRepresentative.
Section Relations.
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
Variable g:U.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Variable hPi:is_commutative_ideal_quotient (@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g) pi.
Variables L M:fieldType.
Variable inclusion:{rmorphism C->L}.
Variable hFraction:is_commutative_fraction_field inclusion.
Variable m:'I_n.
Variable hMN:((m:nat)<=n)%N.
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R
  (coordinate_space (ComplexScalars.C R) m) (@holomorphic_coordinate_norm R m)
  (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0)].
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN).
Variable eta:{rmorphism A->M}.
Variable phi:{rmorphism M->L}.
Local Notation scalar:=(GRing.RMorphism.clone A C (pi \o E) _).
Variable hCoefficient:is_coefficient_fraction_field
  (GRing.RMorphism.clone A L (inclusion \o scalar) _) eta phi.
Local Notation gamma:=(@HolomorphicCoordinateGerms.value R X NX hNX n e he omega).
Local Notation scalarPrefix:=(@HolomorphicScalars.map R (coordinate_space (ComplexScalars.C R) m)
  (@holomorphic_coordinate_norm R m) (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0).
Local Notation scalarAmbient:=(@HolomorphicScalars.map R X NX hNXR 0).
Local Notation F:=(@holomorphic_suffix_rotation_group R X H hH (n+n) eR heR n e m).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.

Variables (mulF:F->F->F) (invF:F->F) (unitF:F).
Variable hF:is_subgroup_restriction mulU invU unitU F mulF invF unitF.
Local Notation Q:=(@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega).
Variable hIntegral:forall c:C,is_integral_ring_element scalar c.
(** Source for [holomorphic_integral_suffix_rotation_B]: the
    original integral quotient supplies B_j
    after an original Q_m rotation,
    3.4.8(8), p. 330. In fact this
    deduction holds for every original suffix
    rotation. Monicity gives a nonzero
    highest directional coefficient without requiring
    lower coefficients to vanish at zero. *)
Theorem holomorphic_integral_suffix_rotation_B (q:F) (j:'I_n):
  (m<=j)%N ->@holomorphic_reduction_actual_B R X H hH n e he omega I j (mulU g (set_val q)).
Proof.
move=>hMJ.
pose pullback:=@holomorphic_unitary_germ_map R X H hH (n+n) eR heR (invU (set_val q)).
have hInverseQ:F (invU (set_val q)).
  rewrite -(subgroup_restriction_inv hF q);exact:set_valP (invF q).
have hFixed:=@holomorphic_fixed_prefix_germ R X H hH n e he omega hDual hON m
  (invU (set_val q)) hInverseQ hMN.
pose c:=pi (pullback (gamma j)).
have [k [beta [hK hRelation]]]:=hIntegral c.
pose Phi:G:=(gamma j)^+k-\sum_(i<k) E (beta i)*(gamma j)^+(i:nat).
have hIdeal:@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I (mulU g (set_val q)) Phi.
  apply:(@holomorphic_rotated_composition_inverse R X H hH n e he mulO invO unitO hO mulU invU unitU hU I g (set_val q) Phi).2.
  apply:(commutative_quotient_kernel hPi _).1.
  change (pi (pullback Phi) = 0).
  rewrite /Phi !rmorphB !rmorph_sum !rmorphXn.
  under eq_bigr do rewrite !rmorphM !rmorphXn hFixed.
  change (c^+k-\sum_(i<k) scalar (beta i)*c^+(i:nat) = 0).
  by rewrite hRelation subrr.
have hQLaws:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
have hRing:is_commutative_subring (Q (j:nat).+1).
  rewrite (holomorphic_coordinate_subring_family_member hQLaws (ltn_ord j)).
  exact:(@holomorphic_prefix_germ_subring_laws R X NX hNXR n e he omega (j:nat).+1 (ltn_ord j)).
have hGamma:Q (j:nat).+1 (gamma j).
  rewrite (holomorphic_coordinate_subring_family_member hQLaws (ltn_ord j)).
  exact:(@holomorphic_next_prefix_coordinate_member R X NX hNX n e he omega j).
have hCoefficients a:Q (j:nat).+1 (E a).
  apply:(@holomorphic_coordinate_prefix_subring_monotone R X NX hNX n e he omega m (j:nat).+1
    (leq_trans hMJ (leqnSn (j:nat))) (ltn_ord j)).
  rewrite (holomorphic_coordinate_subring_family_member hQLaws hMN).
  apply/holomorphic_prefix_germ_subring_membership;by exists a.
have hPowers i:Q (j:nat).+1 ((gamma j)^+i):=@commutative_subring_power G _ hRing (gamma j) i hGamma.
have hSum:Q (j:nat).+1 (\sum_(i<k) E (beta i)*(gamma j)^+(i:nat)).
  apply:(commutative_subring_finite_sum hRing)=>i _ _.
  exact:(@commutative_subring_multiply G _ hRing _ _ (hCoefficients (beta i)) (hPowers i)).
have hMember:Q (j:nat).+1 Phi.
  exact:(@commutative_subring_add G _ hRing _ _ (hPowers k)
    (@commutative_subring_opp G _ hRing _ hSum)).
pose P:=@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega m hMN.
have hP:=@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega m hMN.
have hPZero:=@field_prefix_basis_outside (ComplexScalars.C R) X n e omega m hMN P hP hDual j hMJ.
have hE:=@holomorphic_prefix_germ_map_specification R X NX hNXR n e he omega m hMN.
have [fXi hValues]:=@holomorphic_coordinate_representative_exists R X NX hNX n e he omega j.
have hGerm:=@HolomorphicCoordinateGerms.laws R X NX hNX n e he omega j fXi hValues.
have hXiOne:omega j (e j) = 1 by rewrite hDual eqxx.
have [f [a [hRep hLine]]]:=@holomorphic_monic_prefix_line_representative R X (coordinate_space (ComplexScalars.C R) m) NX
  (@holomorphic_coordinate_norm R m) hNXR
  (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) P E (omega j) fXi k beta (e j)
  hE hValues hPZero hXiOne.
rewrite hGerm in hRep.
have hJet:=@holomorphic_monic_line_nonzero_directional_jet R X NX hNX f k (e j) a hK hLine.
rewrite hRep in hJet.
have hLoci:=@holomorphic_reduction_actual_laws R X H hH n e he omega I.
apply:(holomorphic_reduction_B_membership hLoci j (mulU g (set_val q))).2.
by exists Phi.
Qed.
End Relations.
