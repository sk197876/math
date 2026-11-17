(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    pp. 329–330: almost every original suffix unitary rotation
    gives the actual primitive inverse coordinate. The original
    quotient, coefficient field and suffix classes remain unchanged. *)
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
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric StandardHermitianCoordinates IntegralRingElementUP CommutativeIdealUP CommutativeQuotientUP FractionFieldUP CoefficientFractionFieldUP
  HolomorphicReductionActual HolomorphicReductionLociUP HolomorphicReductionFieldInputs
  RingScalarRestriction RingSubmoduleUP CommutativeSubringUP CommutativePolynomialSealed
  FiniteFieldConjugatedPrimitiveDirectionsNull UnitarySuffixSphereHaarNull
  HolomorphicRotatedCompositionInverse UnitaryPrimitiveFieldCoordinate HausdorffMeasure HaarIntegralUP.
Section PrimitiveHaar.
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
Variable hI:is_commutative_ideal I.
Variable hProper:~I 1.
Variable g:U.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Variable hPi:is_commutative_ideal_quotient
  (@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g) pi.
Variables L M:fieldType.
Variable inclusion:{rmorphism C->L}.
Variable hFraction:is_commutative_fraction_field inclusion.
Variable m:'I_n.
Variable hMN:((m:nat)<=n)%N.
Variable hAllB:forall j:'I_n,(m<=j)%N ->@holomorphic_reduction_actual_B R X H hH n e he omega I j g.
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R
  (coordinate_space (ComplexScalars.C R) m) (@holomorphic_coordinate_norm R m)
  (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0)].
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN).
Variable eta:{rmorphism A->M}.
Variable phi:{rmorphism M->L}.
Variable hCoefficient:is_coefficient_fraction_field
  (GRing.RMorphism.clone A L (inclusion \o (pi \o E)) _) eta phi.
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
(** Source for [holomorphic_reduction_original_primitive_haar_null]: the
    exact original primitive coordinate is obtained for Haar-almost
    every original suffix rotation, 3.4.12, p. 339. *)
Theorem holomorphic_reduction_original_primitive_haar_null (mu:set F->\bar R):
  is_left_haar_measure mulF mu ->
  mu [set q:F|~is_generated_commutative_subring
    (fun y:L=>y=inclusion (pi (P (invU (set_val q)) (gamma m))) \/exists a:M,y=phi a) setT]=0%:E.
Proof.
move=>hMu.
pose rotated:=@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g.
have hRotI:=@holomorphic_rotated_germ_ideal_is_ideal R X H hH (n+n) eR heR I g hI.
have hRotProper:=@holomorphic_rotated_germ_ideal_proper R X H hH (n+n) eR heR I g hProper.
have hB (j:'I_n) (hJ:(m<=j)%N):exists alpha,rotated alpha /\
    @HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega (j:nat).+1 alpha /\
    has_nonzero_holomorphic_directional_jet hNX alpha (e j).
  have hOriginal:=(holomorphic_reduction_B_membership
    (@holomorphic_reduction_actual_laws R X H hH n e he omega I) j g).1 (@hAllB j hJ).
  exact:hOriginal.
have hFinite:=@holomorphic_reduction_fraction_field_finite R X NX hNX n e he omega hDual
  rotated hRotI hRotProper C pi hPi m hMN hB L inclusion hFraction M eta phi hCoefficient.
have hGenerated:=@holomorphic_reduction_fraction_coordinate_generators R X NX hNX n e he omega hDual
  rotated hRotI hRotProper C pi hPi m hMN hB L inclusion hFraction M eta phi hCoefficient.
pose complexScalar:{rmorphism ComplexScalars.C R->M}:=GRing.RMorphism.clone (ComplexScalars.C R) M
  (eta \o scalarPrefix) _.
pose bad:=fun v:R_n R ((n-m)+(n-m))=>~is_generated_commutative_subring
  (fun y:L=>y=\sum_i phi (eta (scalarPrefix
    (ComplexScalarTheory.conjugate ((complex_from_real_coordinates v) i))))*
      inclusion (pi (gamma (ordinal_coordinate_tail_index hMN i))) \/exists a:M,y=phi a) setT.
have [_ hDirectionNull]:=@finite_field_conjugated_primitive_directions_null R M L complexScalar phi (n-m)%N
  (fun i=>inclusion (pi (gamma (ordinal_coordinate_tail_index hMN i))))
  (CommutativePolynomial.space M) (CommutativePolynomial.embed M) (CommutativePolynomial.variable M)
  (@CommutativePolynomial.coefficient M) (CommutativePolynomial.laws M) hFinite hGenerated.
have hSphereSets:[set v:R_n R ((n-m)+(n-m))|inner_norm
    (@euclidean_inner_productP R ((n-m)+(n-m))) v= 1 /\bad v]=
    [set v:R_n R ((n-m)+(n-m))|bad v /\inner_norm
      (@euclidean_inner_productP R ((n-m)+(n-m))) v= 1].
  by apply/seteqP;split=>v [h1 h2];split.
have hSphereNull:@hausdorff_measure R (inner_metric_space
    (@euclidean_inner_productP R ((n-m)+(n-m)))) ((n-m)+(n-m)-1)
    [set v|inner_norm (@euclidean_inner_productP R ((n-m)+(n-m))) v= 1 /\bad v]=0%:E.
  rewrite hSphereSets;exact:hDirectionNull.
have hHaar:=@unitary_suffix_sphere_haar_coordinate_null R X H hH n e he hON omega hDual m hMN
  mulO invO unitO hO mulU invU unitU hU mulF invF unitF hF mu bad hMu hSphereNull.
have hSets:[set q:F|bad (complex_real_coordinates
      [ffun i=>omega (ordinal_coordinate_tail_index hMN i) (mapg (set_val q) (e m))])]=
    [set q:F|~is_generated_commutative_subring
      (fun y:L=>y=inclusion (pi (P (invU (set_val q)) (gamma m))) \/exists a:M,y=phi a) setT].
  apply:funext=>q;change (bad (complex_real_coordinates
    [ffun i=>omega (ordinal_coordinate_tail_index hMN i) (mapg (set_val q) (e m))])=
      ~is_generated_commutative_subring
        (fun y:L=>y=inclusion (pi (P (invU (set_val q)) (gamma m))) \/exists a:M,y=phi a) setT).
  rewrite /bad complex_real_coordinatesK.
  have hInverse:=(@unitary_complex_original_inverse R X H hH n e he
    mulO invO unitO hO mulU invU unitU hU (set_val q)).2.
  have hCoordinate:=@unitary_primitive_field_coordinate R X H hH n e he omega hDual hON
    C pi L M inclusion m hMN eta phi hCoefficient (set_val q) (invU (set_val q)) hInverse (set_valP q).
  have hSum:(\sum_i phi (eta (scalarPrefix (ComplexScalarTheory.conjugate
      ([ffun i=>omega (ordinal_coordinate_tail_index hMN i) (mapg (set_val q) (e m))] i))))*
      inclusion (pi (gamma (ordinal_coordinate_tail_index hMN i))))=
      inclusion (pi (P (invU (set_val q)) (gamma m))).
    rewrite hCoordinate;apply:eq_bigr=>i _;by rewrite ffunE.
  by rewrite hSum.
by rewrite -hSets.
Qed.
End PrimitiveHaar.
