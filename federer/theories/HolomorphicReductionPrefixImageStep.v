(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8), p. 329:
    each original prefix quotient is finite over
    the preceding coefficient ring and generated
    by its last coordinate. The existing
    preparation and division theorems supply this
    assertion through the actual image quotient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicLinear HolomorphicCoordinateNorm FieldCoordinateFunctional HolomorphicCoordinatePrefixSplit HolomorphicPrefixRegularWitness NormFiniteLinearBound Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  EuclideanScalarCoordinateMaps EuclideanStiefelInnerSplitting OrthogonalGroupTopology
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermRepresentatives HolomorphicCoordinateGermsSealed
  FieldPrefixCoordinatesSealed HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws
  HolomorphicPrefixNestedComposition HolomorphicPrefixCoordinateGerm HolomorphicCoordinatePrefixSplit
  HolomorphicReductionLociUP HolomorphicCoordinateSubringFamilySealed
  CommutativeIdealUP CommutativeQuotientUP CommutativeFieldKernel
  CommutativeSubringUP CommutativeSubringRealisationUP CommutativeRingImageQuotient
  RingScalarRestriction RingSubmoduleUP ComplexWeierstrassFunctionalPower RegularHolomorphicQuotientAtZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixStep.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:is_complex_norm NX.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Hypothesis hProper:~I 1.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Hypothesis hPi:is_commutative_ideal_quotient I pi.
Variable j:'I_n.
Local Notation Y:=(coordinate_space (ComplexScalars.C R) (j:nat).+1).
Local Notation NY:=(@holomorphic_coordinate_norm R (j:nat).+1).
Local Notation hNY:=(@holomorphic_coordinate_norm_laws R (j:nat).+1).
Local Notation Z:=(coordinate_space (ComplexScalars.C R) (j:nat)).
Local Notation NZ:=(@holomorphic_coordinate_norm R (j:nat)).
Local Notation hNZ:=(@holomorphic_coordinate_norm_laws R (j:nat)).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R Z NZ (complex_norm_real hNZ) 0)].
Local Notation A1:=[the comNzRingType of (@holomorphic_germ_ring R Y NY (complex_norm_real hNY) 0)].
Local Notation hJN:=(leq_trans (leqnSn (j:nat)) (ltn_ord j)).
Local Notation E0:=(@holomorphic_prefix_germ_map R X NX (complex_norm_real hNX) n e he omega (j:nat) hJN).
Local Notation E1:=(@holomorphic_prefix_germ_map R X NX (complex_norm_real hNX) n e he omega (j:nat).+1 (ltn_ord j)).
Local Notation Gamma:=(@HolomorphicCoordinateGerms.value R X NX hNX n e he omega j).
Variable D:comNzRingType.
Variable inclusion:{rmorphism D->C}.
Hypothesis hImage:is_commutative_subring_realisation
  (fun y:C=>exists beta:A1,y = pi (E1 beta)) inclusion.

(** Source for [holomorphic_reduction_prefix_image_step]:
    the original p(Q_(j+1)) is a finite
    simple algebra over the original Q_j,
    with generator p(gamma_j), 3.4.8(8), p. 329.
    Its coefficient and generator equations identify
    the actual original classes. All witnesses
    are local; no finite-module conclusion is assumed. *)
Theorem holomorphic_reduction_prefix_image_step:
  (exists alpha,I alpha /\
    @HolomorphicCoordinateSubringFamily.value R X NX (complex_norm_real hNX) n e he omega (j:nat).+1 alpha /\
    has_nonzero_holomorphic_directional_jet hNX alpha (e j)) ->
  exists scalar:{rmorphism A->D},exists coordinate:D,
    (forall a:A,inclusion (scalar a) = pi (E0 a)) /\
    inclusion coordinate = pi Gamma /\
    is_finitely_generated_ring_submodule
      (setT:set [the lmodType A of ring_restricted_space scalar D^o]) /\
    is_generated_commutative_subring
      (fun d:D=>d = coordinate \/exists a:A,d = scalar a) setT.
Proof.
move=>hMember.
pose f1:{rmorphism A1->C}:=GRing.RMorphism.clone A1 C (pi \o E1) _.
have [rho [hTriangle hRho]]:=@commutative_ring_image_quotient A1 C D f1 inclusion hImage.
have [beta [hBeta [k hRegular]]]:=@holomorphic_prefix_regular_witness
  R X NX hNX n e he omega hDual I j hI hProper hMember.
have hKernel:f1 beta = 0:= (commutative_quotient_kernel hPi (E1 beta)).2 hBeta.
pose omegaY:=fun i:'I_(j:nat).+1=>@field_coordinate_functional (ComplexScalars.C R) (j:nat).+1 i.
pose P:=@FieldPrefixCoordinates.projection (ComplexScalars.C R) Y (j:nat).+1 omegaY (j:nat) (leqnSn (j:nat)).
pose S:=@FieldPrefixCoordinates.inclusion (ComplexScalars.C R) Y (j:nat).+1 (@coordinate_basis (ComplexScalars.C R) (j:nat).+1)
  (j:nat) (leqnSn (j:nat)).
have hP:=@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) Y (j:nat).+1 omegaY (j:nat) (leqnSn (j:nat)).
have hS:=@FieldPrefixCoordinates.inclusion_laws (ComplexScalars.C R) Y (j:nat).+1 (@coordinate_basis (ComplexScalars.C R) (j:nat).+1)
  (j:nat) (leqnSn (j:nat)).
have hDualY i l:omegaY i (@coordinate_basis (ComplexScalars.C R) (j:nat).+1 l) = if i==l then 1 else 0.
  by rewrite /omegaY /field_coordinate_functional /= /coordinate_basis ffunE eq_sym.
have hSplit:=@holomorphic_last_coordinate_prefix_split R (j:nat) P S hP hS.
pose xi:=omegaY ord_max.
have hXi:=@norm_finite_linear_bounded R (restricted_space (ComplexScalars.embed R) Y)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY (@complex_modulus R)
  (complex_norm_real hNY) (@complex_modulus_real_norm R) ((j:nat).+1+(j:nat).+1)
  (ordered_real_basis (@coordinate_basis (ComplexScalars.C R) (j:nat).+1))
  (ordered_real_basisP (@coordinate_basisP (ComplexScalars.C R) (j:nat).+1)) (complex_hom_real xi).
have [fXi [hXiValues _]]:=@complex_weierstrass_functional_power_representative R Y NY hNY xi 1 hXi.
have hValues y:holomorphic_representative_value fXi y = xi y by rewrite hXiValues expr1.
have [EB [hEB [hFinite hGenerated]]]:=@regular_holomorphic_quotient_original_centre
  R Y Z NY NZ hNY hNZ (@coordinate_basis (ComplexScalars.C R) (j:nat).+1 ord_max) xi S P hSplit
  fXi hXi hValues D (fun a:A1=>f1 a = 0) rho
  (@commutative_ring_kernel_ideal A1 C f1) hRho beta k hKernel hRegular.
pose scalar:{rmorphism A->D}:=GRing.RMorphism.clone A D (rho \o EB) _.
pose coordinate:D:=rho (holomorphic_germ fXi).
have hComposition a:E0 a = E1 (EB a).
  exact:(@holomorphic_adjacent_prefix_germ_composition R X NX (complex_norm_real hNX) n omega (j:nat) hJN (ltn_ord j)
    (@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega (j:nat) hJN)
    (@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega (j:nat).+1 (ltn_ord j)) P E0 E1 EB
    (@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega (j:nat) hJN)
    (@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega (j:nat).+1 (ltn_ord j)) hP
    (@holomorphic_prefix_germ_map_specification R X NX (complex_norm_real hNX) n e he omega (j:nat) hJN)
    (@holomorphic_prefix_germ_map_specification R X NX (complex_norm_real hNX) n e he omega (j:nat).+1 (ltn_ord j)) hEB a).
have hCoordinate:E1 (holomorphic_germ fXi) = Gamma.
  apply:(@holomorphic_prefix_last_coordinate_germ R X NX hNX n e he omega j fXi)=>y.
  exact:hValues y.
exists scalar,coordinate;split.
- move=>a;change (inclusion (rho (EB a)) = pi (E0 a)).
  rewrite hTriangle;change (pi (E1 (EB a)) = pi (E0 a)).
  by rewrite -hComposition.
- split.
  + change (inclusion (rho (holomorphic_germ fXi)) = pi Gamma).
    rewrite hTriangle;change (pi (E1 (holomorphic_germ fXi)) = pi Gamma).
    by rewrite hCoordinate.
  by split.
Qed.
End PrefixStep.
