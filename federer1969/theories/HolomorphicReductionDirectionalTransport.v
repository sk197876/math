(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),
    p. 329: the actual nonzero complex directional derivative
    gives original B_j membership after its fixed-tail rotation. *)
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
Section Transport.
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
Local Notation Q:=(@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.

(** Source for [holomorphic_reduction_directional_transport]: the
    exact original complex derivative transformation supplies B_(j+1),
    3.4.12, p. 339. *)
Theorem holomorphic_reduction_directional_transport (j:'I_n) (g h:U) (alpha:G):
  @holomorphic_prefix_rotation_group R X H hH (n+n) eR heR n e (j:nat).+1 h ->
  @holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g alpha ->Q (j:nat).+1 alpha ->
  has_nonzero_holomorphic_directional_jet hNX alpha (mapg h (e j)) ->
  @holomorphic_reduction_actual_B R X H hH n e he omega I j (mulU g h).
Proof.
move=>hFix hI hQ [k [hPositive hNonzero]].
have hLaws:=@holomorphic_reduction_actual_laws R X H hH n e he omega I.
apply/(holomorphic_reduction_B_membership hLaws j (mulU g h)).
exists (P h alpha);split.
- apply/(@holomorphic_rotated_germ_ideal_composition R X H hH n e he
    mulO invO unitO hO mulU invU unitU hU I g h (P h alpha)).
  by exists alpha.
- split.
  + exact:(@holomorphic_unitary_prefix_subring_invariant R X H hH n e he omega hDual
      (j:nat).+1 (ltn_ord j) h hFix alpha hQ).
  + exists k;split;first exact:hPositive.
    rewrite (@pointed_holomorphic_linear_pullback_form_diagonal R X X NX NX hNX hNX 0 0
      (mapg h) (P h) (@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR h)
      (linear0 (mapg h)) k alpha (e j)).
    exact:hNonzero.
Qed.
End Transport.
