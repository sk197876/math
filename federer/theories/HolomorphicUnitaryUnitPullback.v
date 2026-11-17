(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),
    p. 329: actual unitary composition reverses on the original
    holomorphic germs and transports each original rotated ideal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import PointedHolomorphicPullbackComposition HolomorphicRotatedGermIdeal HolomorphicUnitaryPullbackComposition HolomorphicGermRepresentatives HolomorphicGermRingLaws HolomorphicGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Unit.
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


(** Source for [holomorphic_unitary_unit_germ_map]: the identity
    coordinate change fixes the actual original germ, extending
    3.4.8(11), p. 334, under 3.4.12, p. 339.
    Apply the existing representative equation of unitary pullback. *)
Lemma holomorphic_unitary_unit_germ_map (alpha:G):P unitU alpha = alpha.
Proof.
have [f <-]:=@holomorphic_germ_has_representative R X NX hNXR 0 alpha.
have [q [hQ hValues]]:=@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR unitU f.
rewrite hQ;apply:holomorphic_germ_pointwise_equality=>x.
rewrite hValues (@UnitaryComplexMap.laws R X H hH (n+n) eR heR unitU).
rewrite (subgroup_restriction_unit hU).
by rewrite (@orthogonal_element_unit R XR B hB (n+n) eR heR mulO invO unitO hO).
Qed.
(** Source for [holomorphic_rotated_unit_ideal]: the original
    ideal in identity coordinates equals itself, extending
    3.4.8(11), p. 334, under 3.4.12, p. 339. *)
Lemma holomorphic_rotated_unit_ideal (I:set G):
  @holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I unitU = I.
Proof.
apply/seteqP;split=>alpha.
- move/holomorphic_rotated_germ_ideal_membership=>[beta [hBeta hValue]].
  by rewrite holomorphic_unitary_unit_germ_map in hValue;rewrite -hValue.
- move=>hAlpha;apply/holomorphic_rotated_germ_ideal_membership;exists alpha;split;first exact:hAlpha.
  exact:holomorphic_unitary_unit_germ_map.
Qed.
End Unit.
