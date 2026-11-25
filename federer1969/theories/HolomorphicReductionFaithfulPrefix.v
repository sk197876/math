(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10),
    p. 330: exclusion from the original A_m makes the
    original prefix coefficient map faithful. Reuse exact membership,
    the original quotient kernel and the proved prefix injection. *)
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
From Federer Require Import HolomorphicPrefixGermMap HolomorphicPrefixGermSubring
  HolomorphicPrefixGermInjective HolomorphicCoordinateSubringFamilyUP HolomorphicCoordinateSubringFamilySealed
  HolomorphicReductionLociUP HolomorphicReductionActual CommutativeQuotientUP.
Section Faithful.
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
Variable I:set G.
Variable g:U.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Variable m:'I_n.
Variable hMN:((m:nat)<=n)%N.
(** Source for [holomorphic_reduction_not_A_faithful_prefix]: the
    actual original coefficient monomorphism under m positive and
    the original not-A_m condition, 3.4.12, p. 339. *)
Theorem holomorphic_reduction_not_A_faithful_prefix:
  is_commutative_ideal_quotient (@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g) pi ->
  (0<m)%N ->~@holomorphic_reduction_actual_A R X H hH n e he omega I (widen_ord (leqnSn n) m) g ->
  injective (fun a=>pi (@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN a)).
Proof.
move=>hPi hPositive hNotA a b hEqual.
pose E:=@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN.
pose alpha:=E (a-b).
have hKernel:@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g alpha.
  apply:(commutative_quotient_kernel hPi _).1.
  by rewrite /alpha !rmorphB hEqual subrr.
have hQ:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
have hMember:@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega m alpha.
  rewrite (holomorphic_coordinate_subring_family_member hQ hMN).
  apply/holomorphic_prefix_germ_subring_membership;by exists (a-b).
have hLoci:=@holomorphic_reduction_actual_laws R X H hH n e he omega I.
have hZero:alpha=0.
  apply:contrapT=>hNonzero;apply:hNotA.
  apply:(holomorphic_reduction_A_membership hLoci (widen_ord (leqnSn n) m) g).2.
  split;first exact:hPositive.
  exists alpha;by split;last split.
have hInjective:=@holomorphic_prefix_germ_map_injective R X NX hNXR n e he omega hDual m hMN.
have hDifference:a-b=0.
  apply:hInjective;change (alpha=E 0);by rewrite hZero rmorph0.
by apply/eqP;rewrite -subr_eq0 hDifference eqxx.
Qed.
End Faithful.
