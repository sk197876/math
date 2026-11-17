(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),
    p. 329: actual unitary composition reverses on the original
    holomorphic germs and transports each original rotated ideal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import PointedHolomorphicPullbackComposition HolomorphicRotatedGermIdeal HolomorphicUnitaryPullbackComposition HolomorphicGermRepresentatives HolomorphicGermRingLaws HolomorphicGermSealed HolomorphicReductionLociUP HolomorphicReductionActual AnalyticReductionDepthUP HolomorphicDepthSealed TopologicalGroupLaws UnitaryGroupClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Rotation.
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
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.


Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
(** Source for [holomorphic_reduction_rotated_B_composition]:
    the exact directional-locus equation under the
    coordinate change in 3.4.12, p. 339, extending 3.4.8(11), p. 334. *)
Lemma holomorphic_reduction_rotated_B_composition (I:set G) (g h:U) j:
  @holomorphic_reduction_actual_B R X H hH n e he omega
    (@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g) j h <->
  @holomorphic_reduction_actual_B R X H hH n e he omega I j (mulU g h).
Proof.
have hLawsI:=@holomorphic_reduction_actual_laws R X H hH n e he omega I.
have hLawsIg:=@holomorphic_reduction_actual_laws R X H hH n e he omega
  (@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g).
rewrite (holomorphic_reduction_B_membership hLawsI) (holomorphic_reduction_B_membership hLawsIg).
split;move=>[alpha [hAlpha hRest]];exists alpha;split;try exact:hRest.
- apply:(@holomorphic_rotated_germ_ideal_composition R X H hH n e he
    mulO invO unitO hO mulU invU unitU hU I g h alpha).2.
  exact:(holomorphic_rotated_germ_ideal_membership _ _ _).1 hAlpha.
- apply/holomorphic_rotated_germ_ideal_membership.
  exact:(@holomorphic_rotated_germ_ideal_composition R X H hH n e he
    mulO invO unitO hO mulU invU unitU hU I g h alpha).1 hAlpha.
Qed.

(** Source for [holomorphic_rotated_ideal_depth]:
    the original depth is unchanged under
    the orthogonal change used in 3.4.12, p. 339, extending 3.4.8(11),
    p. 334. Both inequalities follow from
    explicit witnesses for the same B_j tails. *)
Theorem holomorphic_rotated_ideal_depth (I:set G) (g:U):
  @HolomorphicDepth.value R X H hH n e he omega
    (@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g) =
  @HolomorphicDepth.value R X H hH n e he omega I.
Proof.
pose Ig:=@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g.
have hI:=@HolomorphicDepth.laws R X H hH n e he omega I.
have hIg:=@HolomorphicDepth.laws R X H hH n e he omega Ig.
have hLocal:=@subgroup_restriction_locally_compact_hausdorff O mulO invO unitO U mulU invU unitU hU
  (@orthogonal_group_lch R XR B hB (n+n) eR heR mulO invO unitO hO)
  (@unitary_group_closed R X H hH (n+n) eR heR).
have hGroup:=topological_group_laws (lch_group_topological hLocal).
apply/eqP;rewrite eqn_leq;apply/andP;split.
- apply:(analytic_reduction_depth_minimal hIg).
  have [h hTail]:=analytic_reduction_depth_attained hI.
  exists (mulU (invU g) h)=>j hDJ.
  apply:(holomorphic_reduction_rotated_B_composition I g (mulU (invU g) h) j).2.
  rewrite (group_mulKVg hGroup);exact:hTail j hDJ.
- apply:(analytic_reduction_depth_minimal hI).
  have [h hTail]:=analytic_reduction_depth_attained hIg.
  exists (mulU g h)=>j hDJ.
  exact:(holomorphic_reduction_rotated_B_composition I g h j).1 (hTail j hDJ).
Qed.
End Rotation.
