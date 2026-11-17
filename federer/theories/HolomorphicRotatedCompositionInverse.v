(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 330: the actual selected unitary group inverse tests
    membership in the original composed rotated ideal. Use the
    existing pointed germ retraction and actual group inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import PointedHolomorphicPullbackComposition HolomorphicRotatedGermIdeal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import PointedHolomorphicPullbackRetraction HolomorphicUnitaryPullbackComposition.
Section Inverses.
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

(** Source for [unitary_complex_original_inverse]: both actual
    original inverse-map equations, 3.4.12, p. 339. *)
Lemma unitary_complex_original_inverse (q:U):
  cancel (mapg q) (mapg (invU q)) /\cancel (mapg (invU q)) (mapg q).
Proof.
split=>x;rewrite !(@UnitaryComplexMap.laws R X H hH (n+n) eR heR)
  (subgroup_restriction_inv hU).
- exact:(@orthogonal_element_inv R XR B hB (n+n) eR heR mulO invO unitO hO (set_val q)).1.
- exact:(@orthogonal_element_inv R XR B hB (n+n) eR heR mulO invO unitO hO (set_val q)).2.
Qed.
(** Source for [holomorphic_original_unitary_germ_inverse]: actual
    selected inverse pullbacks cancel on both sides,
    3.4.12, p. 339. *)
Lemma holomorphic_original_unitary_germ_inverse (q:U):
  cancel (P q) (P (invU q)) /\cancel (P (invU q)) (P q).
Proof.
have [hLeft hRight]:=unitary_complex_original_inverse q.
have hQ:=@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR q.
have hInv:=@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR (invU q).
split.
- exact:(@pointed_holomorphic_germ_pullback_retraction R X X NX NX hNXR hNXR 0 0
    (mapg q) (mapg (invU q)) (P q) (P (invU q)) hQ hInv hRight).
- exact:(@pointed_holomorphic_germ_pullback_retraction R X X NX NX hNXR hNXR 0 0
    (mapg (invU q)) (mapg q) (P (invU q)) (P q) hInv hQ hLeft).
Qed.
(** Source for [holomorphic_rotated_composition_inverse]: the literal
    original inverse-membership equivalence for I_(gq),
    3.4.12, p. 339. *)
Theorem holomorphic_rotated_composition_inverse (I:set G) (g q:U) (beta:G):
  @holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I (mulU g q) beta <->
    @holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g (P (invU q) beta).
Proof.
rewrite (@holomorphic_rotated_germ_ideal_composition R X H hH n e he
  mulO invO unitO hO mulU invU unitU hU I g q beta).
have [hLeft hRight]:=holomorphic_original_unitary_germ_inverse q.
split.
- move=>[alpha [hAlpha hBeta]];by rewrite -hBeta hLeft.
- move=>hBeta;exists (P (invU q) beta);split;first exact:hBeta.
  exact:hRight.
Qed.
End Inverses.
