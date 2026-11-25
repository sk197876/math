(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 330: actual primitive suffix rotations give the original
    C_m denominator and numerator relations. Reuse the existing
    denominator theorem and original polynomial coordinate subrings. *)
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
From Federer Require Import CommutativeQuotientUP CommutativeSubringUP FractionFieldUP
  CoefficientFractionFieldLaws CommutativePolynomialSealed CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationSealed PolynomialScalarComposition PrimitiveFieldOriginalRepresentative
  HolomorphicFixedPrefixPullback HolomorphicPrefixPolynomialSubring HolomorphicPrefixGermSubring
  HolomorphicCoordinateSubringFamilyUP HolomorphicCoordinateSubringFamilySealed
  HolomorphicReductionLociUP HolomorphicReductionActual HolomorphicRotatedCompositionInverse.
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
(** Source for [holomorphic_reduction_primitive_rotation_C]:
    every original primitive rotation gives
    the original C_m relations, 3.4.8(8),
    p. 330. Each denominator lies in
    the original Q_m outside I_(gq), and
    each numerator lies in the original
    Q_(m+1). No such relation is assumed. *)
Theorem holomorphic_reduction_primitive_rotation_C (q:F):
  is_generated_commutative_subring
    (fun y:L=>y = inclusion (pi (@holomorphic_unitary_germ_map R X H hH (n+n) eR heR
      (invU (set_val q)) (gamma m))) \/exists a:M,y = phi a) setT ->
  @holomorphic_reduction_actual_C R X H hH n e he omega I m (mulU g (set_val q)).
Proof.
move=>hGenerated.
pose pullback:=@holomorphic_unitary_germ_map R X H hH (n+n) eR heR (invU (set_val q)).
have hInverseQ:F (invU (set_val q)).
  rewrite -(subgroup_restriction_inv hF q);exact:set_valP (invF q).
have hFixed:=@holomorphic_fixed_prefix_germ R X H hH n e he omega hDual hON m
  (invU (set_val q)) hInverseQ hMN.
pose P:=CommutativePolynomial.space A.
pose embed:=CommutativePolynomial.embed A.
pose variable:=CommutativePolynomial.variable A.
pose coefficient:=@CommutativePolynomial.coefficient A.
have hP:=CommutativePolynomial.laws A.
pose J:=@CommutativePolynomialEvaluation.map A P G embed variable coefficient hP E (gamma m).
have hJ:=@CommutativePolynomialEvaluation.laws A P G embed variable coefficient hP E (gamma m).
pose composite:{rmorphism G->C}:=GRing.RMorphism.clone G C (pi \o pullback) _.
pose EC:{rmorphism P->C}:=GRing.RMorphism.clone P C (composite \o J) _.
have hBase:=@polynomial_evaluation_after_ring_map A P G C embed variable E (gamma m) J composite hJ.
have hEC:is_commutative_polynomial_evaluation embed variable scalar (pi (pullback (gamma m))) EC.
  apply:(polynomial_evaluation_change_parameters hBase).
  - move=>a;change (pi (pullback (E a)) = pi (E a));by rewrite hFixed.
  - by [].
pose hJN:=leq_trans (leqnSn (m:nat)) (ltn_ord m).
have hJBound:is_commutative_polynomial_evaluation embed variable
    (@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hJN) (gamma m) J.
  apply:(polynomial_evaluation_change_parameters hJ).
  - move=>a;by rewrite (bool_irrelevance hMN hJN).
  - by [].
have hNumerator H0:@holomorphic_prefix_germ_subring R X NX hNXR n e he omega (m:nat).+1 (ltn_ord m) (J H0).
  exact:(@holomorphic_prefix_polynomial_member R X NX hNX n e he omega m P embed variable coefficient hP J hJBound H0).
have hLoci:=@holomorphic_reduction_actual_laws R X H hH n e he omega I.
have hQ:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
apply:(holomorphic_reduction_C_membership hLoci m (mulU g (set_val q))).2.
move=>j hMJ.
pose c:=pi (pullback (gamma j)).
have [delta [H0 [hDelta hRelation]]]:=@primitive_field_original_coefficient_representative
  A P C L M embed variable coefficient hP scalar inclusion eta phi (pi (pullback (gamma m))) EC
  hFraction hCoefficient hEC hGenerated c.
exists (E delta),(J H0);split.
- rewrite (holomorphic_coordinate_subring_family_member hQ hMN).
  apply/holomorphic_prefix_germ_subring_membership;by exists delta.
- split.
  + move=>hIn.
    have hOriginal:=(@holomorphic_rotated_composition_inverse R X H hH n e he mulO invO unitO hO mulU invU unitU hU
      I g (set_val q) (E delta)).1 hIn.
    have hZero:pi (pullback (E delta)) = 0:=(commutative_quotient_kernel hPi _).2 hOriginal.
    rewrite hFixed in hZero.
    apply:hDelta;apply:(@coefficient_fraction_scalar_kernel A L M
      (GRing.RMorphism.clone A L (inclusion \o scalar) _) eta phi hCoefficient delta).2.
    change (inclusion (pi (E delta)) = 0);by rewrite hZero rmorph0.
  + split.
    * rewrite (holomorphic_coordinate_subring_family_member hQ (ltn_ord m));exact:hNumerator.
    * apply:(@holomorphic_rotated_composition_inverse R X H hH n e he mulO invO unitO hO mulU invU unitU hU
        I g (set_val q) (E delta*gamma j-J H0)).2.
      apply:(commutative_quotient_kernel hPi _).1.
      change (pi (pullback (E delta*gamma j-J H0)) = 0).
      rewrite !rmorphB !rmorphM hFixed.
      change (scalar delta*c-EC H0 = 0);by rewrite hRelation subrr.
Qed.
End Relations.
