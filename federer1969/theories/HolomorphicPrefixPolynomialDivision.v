(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 331:
    division inside an original coordinate
    prefix retains its quotient and bounded
    polynomial remainder in that prefix.
    Apply the existing exact prefix diagrams
    and original-centre holomorphic division. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ComplexModulus ComplexScalarNorm HolomorphicLinear NormFiniteLinearBound FieldPrefixCoordinatesUP HolomorphicCoordinateGermsExistence ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct FieldCoordinateFunctional
  EuclideanStiefelInnerSplitting OrthonormalFamilies OrthogonalGroupTopology HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermRepresentatives HolomorphicGermValueSealed HolomorphicCoordinateGermsSealed
  FieldPrefixCoordinatesSealed HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws HolomorphicPrefixGermInjective
  HolomorphicPrefixNestedComposition HolomorphicPrefixCoordinateGerm HolomorphicCoordinatePrefixSplit
  HolomorphicRotatedGermIdeal HolomorphicReductionActual HolomorphicReductionLociUP HolomorphicPrefixRegularWitness
  HolomorphicOriginalPreparedPolynomial ComplexWeierstrassRegularUP ComplexWeierstrassFunctionalPower
  CommutativeIdealUP NoetherianRingSurjection CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationSealed CommutativePolynomialEvaluationLaws PolynomialScalarComposition
  DistinguishedPolynomialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import HolomorphicPrefixGermSubring HolomorphicOriginalPolynomialDivision.
Section PrefixDivision.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Variable I:set G.
Variable g:@unitary_group R X Herm hHerm (n+n) eR heR.
Variable m:'I_n.
Local Notation Y:=(coordinate_space (ComplexScalars.C R) (m:nat).+1).
Local Notation NY:=(@holomorphic_coordinate_norm R (m:nat).+1).
Local Notation hNYC:=(@holomorphic_coordinate_norm_laws R (m:nat).+1).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R (m:nat).+1)).
Local Notation Z:=(coordinate_space (ComplexScalars.C R) (m:nat)).
Local Notation NZ:=(@holomorphic_coordinate_norm R (m:nat)).
Local Notation hNZC:=(@holomorphic_coordinate_norm_laws R (m:nat)).
Local Notation hNZ:=(complex_norm_real (@holomorphic_coordinate_norm_laws R (m:nat))).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R Z NZ hNZ 0)].
Local Notation A1:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)].
Local Notation hMN:=(leq_trans (leqnSn (m:nat)) (ltn_ord m)).
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN).
Local Notation E1:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega (m:nat).+1 (ltn_ord m)).
Local Notation Gamma:=(@HolomorphicCoordinateGerms.value R X NX hNX n e he omega m).
Variable P:comNzRingType.
Variable embed:{rmorphism A->P}.
Variable variable:P.
Variable coefficient:P->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism P->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.

(** Source for [holomorphic_prefix_distinguished_division]:
    the original holomorphic division used in
    the induction over Q_j, 3.4.8(10),
    p. 331. Both quotient and remainder
    retain the original next prefix, and
    the coefficient germs remain at zero.
    No division or coefficient-independence proof is repeated. *)
Theorem holomorphic_prefix_distinguished_division (H:P) k:
  is_distinguished_polynomial coefficient (@HolomorphicGermValue.map R Z NZ hNZ 0) H k ->
  (0<k)%N ->forall alpha:G,
    @holomorphic_prefix_germ_subring R X NX hNXR n e he omega (m:nat).+1 (ltn_ord m) alpha ->
  exists a:G,exists r:P,
    (forall i,(k<=i)%N ->coefficient r i = 0) /\
    alpha = a*J H+J r /\
    @holomorphic_prefix_germ_subring R X NX hNXR n e he omega (m:nat).+1 (ltn_ord m) a.
Proof.
move=>hDistinguished hK alpha hPrefix.
have [beta hBeta]:=(@holomorphic_prefix_germ_subring_membership R X NX hNXR n e he omega
  (m:nat).+1 (ltn_ord m) alpha).1 hPrefix.
pose omegaY:=fun i:'I_(m:nat).+1=>@field_coordinate_functional (ComplexScalars.C R) (m:nat).+1 i.
pose projection:=@FieldPrefixCoordinates.projection (ComplexScalars.C R) Y (m:nat).+1 omegaY (m:nat) (leqnSn (m:nat)).
pose section:=@FieldPrefixCoordinates.inclusion (ComplexScalars.C R) Y (m:nat).+1 (@coordinate_basis (ComplexScalars.C R) (m:nat).+1)
  (m:nat) (leqnSn (m:nat)).
have hProjection:=@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) Y (m:nat).+1 omegaY (m:nat) (leqnSn (m:nat)).
have hSection:=@FieldPrefixCoordinates.inclusion_laws (ComplexScalars.C R) Y (m:nat).+1 (@coordinate_basis (ComplexScalars.C R) (m:nat).+1)
  (m:nat) (leqnSn (m:nat)).
have hDualY i l:omegaY i (@coordinate_basis (ComplexScalars.C R) (m:nat).+1 l) = if i==l then 1 else 0.
  by rewrite /omegaY /field_coordinate_functional /= /coordinate_basis ffunE eq_sym.
have hSplit:=@holomorphic_last_coordinate_prefix_split R (m:nat) projection section hProjection hSection.
pose xi:=omegaY ord_max.
have hXi:=@norm_finite_linear_bounded R (restricted_space (ComplexScalars.embed R) Y)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY (@complex_modulus R)
  hNY (@complex_modulus_real_norm R) ((m:nat).+1+(m:nat).+1)
  (ordered_real_basis (@coordinate_basis (ComplexScalars.C R) (m:nat).+1))
  (ordered_real_basisP (@coordinate_basisP (ComplexScalars.C R) (m:nat).+1)) (complex_hom_real xi).
have [fXi [hXiValues _]]:=@complex_weierstrass_functional_power_representative R Y NY hNYC xi 1 hXi.
have hValues y:holomorphic_representative_value fXi y=xi y by rewrite hXiValues expr1.
pose EB:=@holomorphic_prefix_germ_map R Y NY hNY (m:nat).+1 (@coordinate_basis (ComplexScalars.C R) (m:nat).+1)
  (@coordinate_basisP (ComplexScalars.C R) (m:nat).+1) omegaY (m:nat) (leqnSn (m:nat)).
have hEB:=@holomorphic_prefix_germ_map_specification R Y NY hNY (m:nat).+1 (@coordinate_basis (ComplexScalars.C R) (m:nat).+1)
  (@coordinate_basisP (ComplexScalars.C R) (m:nat).+1) omegaY (m:nat) (leqnSn (m:nat)).
have hComposition a:E a = E1 (EB a).
  exact:(@holomorphic_adjacent_prefix_germ_composition R X NX hNXR n omega (m:nat) hMN (ltn_ord m)
    (@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega (m:nat) hMN)
    (@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega (m:nat).+1 (ltn_ord m)) projection E E1 EB
    (@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega (m:nat) hMN)
    (@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega (m:nat).+1 (ltn_ord m)) hProjection
    (@holomorphic_prefix_germ_map_specification R X NX hNXR n e he omega (m:nat) hMN)
    (@holomorphic_prefix_germ_map_specification R X NX hNXR n e he omega (m:nat).+1 (ltn_ord m)) hEB a).
have hCoordinate:E1 (holomorphic_germ fXi) = Gamma.
  apply:(@holomorphic_prefix_last_coordinate_germ R X NX hNX n e he omega m fXi)=>y.
  exact:hValues y.
pose JY:=@CommutativePolynomialEvaluation.map A P A1 embed variable coefficient hP EB (holomorphic_germ fXi).
have hJY:=@CommutativePolynomialEvaluation.laws A P A1 embed variable coefficient hP EB (holomorphic_germ fXi).
pose composite:{rmorphism P->G}:=GRing.RMorphism.clone P G (E1 \o JY) _.
have hComposite:=@polynomial_evaluation_after_ring_map A P A1 G embed variable EB (holomorphic_germ fXi) JY E1 hJY.
have hCompositeOriginal:is_commutative_polynomial_evaluation embed variable E Gamma composite.
  apply:(polynomial_evaluation_change_parameters hComposite).
  - move=>a;exact:esym (hComposition a).
  - exact:hCoordinate.
have hJEquation T:J T = E1 (JY T).
  exact:(@polynomial_evaluation_unique A P G embed variable coefficient hP E Gamma J composite hJ hCompositeOriginal T).
have [a [r [hSupport hDivision]]]:=@holomorphic_original_distinguished_division R Y Z NY NZ hNYC hNZC
  (@coordinate_basis (ComplexScalars.C R) (m:nat).+1 ord_max) xi section projection hSplit fXi hXi hValues EB hEB
  P embed variable coefficient hP JY hJY H k hDistinguished hK beta.
exists (E1 a),r;split;first exact:hSupport.
split.
- by rewrite -hBeta hDivision rmorphD rmorphM -!hJEquation.
- apply/holomorphic_prefix_germ_subring_membership;by exists a.
Qed.
End PrefixDivision.
