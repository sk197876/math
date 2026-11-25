(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),
    p. 329: every original prefix-fixing unitary transformation
    preserves the exact original coordinate germ subring. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import HolomorphicCoordinateSubringFamilyUP HolomorphicCoordinateSubringFamilySealed
  HolomorphicPrefixGermInvariance UnitaryCoordinateFixing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Invariance.
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
Variable p:nat.
Variable hPN:(p<=n)%N.

(** Source for [holomorphic_unitary_prefix_subring_invariant]:
    original Q_p membership is preserved by H_p, without an
    invariance premise, 3.4.12, p. 339. *)
Theorem holomorphic_unitary_prefix_subring_invariant (h:U):
  @holomorphic_prefix_rotation_group R X H hH (n+n) eR heR n e p h ->
  forall alpha,@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega p alpha ->
    @HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega p (P h alpha).
Proof.
move=>hHaar alpha hAlpha.
have hQ:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
rewrite (holomorphic_coordinate_subring_family_member hQ hPN) in hAlpha *.
apply:(@holomorphic_prefix_germ_subring_invariant R X NX hNXR n e he omega p hPN (mapg h) (P h)
  hDual (@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR h) _ alpha hAlpha).
move=>i hi;rewrite (@UnitaryComplexMap.laws R X H hH (n+n) eR heR h).
exact:((@unitary_coordinate_fixing_membership R X H hH (n+n) eR heR n e [set k:'I_n|(p<=k)%N] h).1 hHaar i hi).
Qed.
End Invariance.
