(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),
    p. 329: the actual nonzero complex directional derivative
    gives original B_j membership after its fixed-tail rotation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import HolomorphicReductionDirectionalTransport HolomorphicGermFormsSealed HolomorphicReductionLociUP HolomorphicReductionActual
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


(** Source for [holomorphic_reduction_tail_prefix_stable]: every
    later directional witness survives the original prefix rotation,
    extending the minimal-depth argument of 3.4.8(11), p. 334,
    under 3.4.12, p. 339. Apply the existing transport
    theorem to the same germ and fixed tail direction. *)
Theorem holomorphic_reduction_tail_prefix_stable m (g h:U):
  @holomorphic_prefix_rotation_group R X H hH (n+n) eR heR n e m h ->
  (forall j:'I_n,(m<=j)%N ->@holomorphic_reduction_actual_B R X H hH n e he omega I j g) ->
  forall j:'I_n,(m<=j)%N ->@holomorphic_reduction_actual_B R X H hH n e he omega I j (mulU g h).
Proof.
move=>hPrefix hAll j hMJ.
have hFix:forall i:'I_n,(m<=i)%N ->mapg h (e i) = e i.
  move=>i hi;rewrite (@UnitaryComplexMap.laws R X H hH (n+n) eR heR h).
  exact:((@unitary_coordinate_fixing_membership R X H hH (n+n) eR heR n e [set i:'I_n|(m<=i)%N] h).1 hPrefix i hi).
have hLoci:=@holomorphic_reduction_actual_laws R X H hH n e he omega I.
have [alpha [hAlpha [hQ hDirectional]]]:=(holomorphic_reduction_B_membership hLoci j g).1 (hAll j hMJ).
apply:(@holomorphic_reduction_directional_transport R X H hH n e he omega hDual I
  mulO invO unitO hO mulU invU unitU hU j g h alpha).
- apply/unitary_coordinate_fixing_membership=>i hJI.
  rewrite -(@UnitaryComplexMap.laws R X H hH (n+n) eR heR h).
  exact:hFix i (leq_trans (leq_trans hMJ (leqnSn j)) hJI).
- exact:hAlpha.
- exact:hQ.
- by rewrite (hFix j hMJ).
Qed.
End Transport.
