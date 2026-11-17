(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),(7),
    p. 329: original A_j membership is constant on each original
    unitary H_j coset. Actual inverse rotations prove the reverse
    implication; no coset-invariance conclusion is assumed. *)
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
Section Cosets.
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


(** Source for [holomorphic_reduction_A_prefix_stable]: actual
    coordinate subring invariance, germ injectivity and ideal
    composition preserve original A_j, 3.4.12, p. 339. *)
Lemma holomorphic_reduction_A_prefix_stable (j:'I_n.+1) (g h:U):
  @holomorphic_prefix_rotation_group R X H hH (n+n) eR heR n e j h ->
  @holomorphic_reduction_actual_A R X H hH n e he omega I j g ->
  @holomorphic_reduction_actual_A R X H hH n e he omega I j (mulU g h).
Proof.
move=>hFix hA.
have hLaws:=@holomorphic_reduction_actual_laws R X H hH n e he omega I.
have [hPositive [alpha [hI [hQ hNonzero]]]]:=(holomorphic_reduction_A_membership hLaws j g).1 hA.
apply/(holomorphic_reduction_A_membership hLaws j (mulU g h));split;first exact:hPositive.
exists (P h alpha);split.
- apply/(@holomorphic_rotated_germ_ideal_composition R X H hH n e he
    mulO invO unitO hO mulU invU unitU hU I g h (P h alpha)).
  by exists alpha.
- split.
  + exact:(@holomorphic_unitary_prefix_subring_invariant R X H hH n e he omega hDual
      j (ltn_ord j) h hFix alpha hQ).
  + move=>hZero;apply:hNonzero.
    apply:(@holomorphic_unitary_germ_map_injective R X H hH (n+n) eR heR h).
    by rewrite hZero rmorph0.
Qed.

(** Source for [holomorphic_reduction_A_prefix_coset]: the
    original right-coset dichotomy for complex A_j,
    3.4.12, p. 339. *)
Theorem holomorphic_reduction_A_prefix_coset (j:'I_n.+1) (g h:U):
  @holomorphic_prefix_rotation_group R X H hH (n+n) eR heR n e j h ->
  (@holomorphic_reduction_actual_A R X H hH n e he omega I j (mulU g h) <->
   @holomorphic_reduction_actual_A R X H hH n e he omega I j g).
Proof.
move=>hFix;split.
- move=>hA.
  have hSub:=@unitary_coordinate_fixing_subgroup R X H hH (n+n) eR heR n e
    mulO invO unitO hO mulU invU unitU hU [set i:'I_n|(j<=i)%N].
  have hInverse:=subgroup_inv hSub hFix.
  have hRestored:=holomorphic_reduction_A_prefix_stable hInverse hA.
  have hLocal:=@subgroup_restriction_locally_compact_hausdorff O mulO invO unitO U mulU invU unitU hU
    (@orthogonal_group_lch R XR B hB (n+n) eR heR mulO invO unitO hO)
    (@unitary_group_closed R X H hH (n+n) eR heR).
  have hGroup:=topological_group_laws (lch_group_topological hLocal).
  by rewrite (@group_mulgK U mulU invU unitU hGroup h g) in hRestored.
- exact:holomorphic_reduction_A_prefix_stable hFix.
Qed.
End Cosets.
