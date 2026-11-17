(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),
    p. 329: actual unitary composition reverses on the original
    holomorphic germs and transports each original rotated ideal. *)
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
Section Composition.
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

(** Source for [unitary_complex_map_composition]: actual original
    unitary multiplication agrees with composition of complex maps,
    3.4.12, p. 339. *)
Lemma unitary_complex_map_composition (g h:U) x:
  mapg (mulU g h) x=mapg g (mapg h x).
Proof.
rewrite !(@UnitaryComplexMap.laws R X H hH (n+n) eR heR) (subgroup_restriction_mul hU).
exact:(@orthogonal_element_mulE R XR B hB (n+n) eR heR mulO invO unitO hO (set_val g) (set_val h) x).
Qed.

(** Source for [holomorphic_unitary_germ_map_composition]: original
    unitary pullback reverses multiplication, 3.4.12, p. 339. *)
Lemma holomorphic_unitary_germ_map_composition (g h:U) (alpha:G):
  P (mulU g h) alpha = P h (P g alpha).
Proof.
have hComposition:=@pointed_holomorphic_pullback_composes R X X X NX NX NX hNXR hNXR hNXR
  0 0 0 (mapg h) (mapg g) (P h) (P g)
  (@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR h)
  (@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR g).
exact:(@pointed_holomorphic_pullback_map_extensional R X X NX NX hNXR hNXR 0 0
  (mapg (mulU g h)) (fun x=>mapg g (mapg h x)) (P (mulU g h)) (fun beta=>P h (P g beta))
  (@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR (mulU g h)) hComposition
  (unitary_complex_map_composition g h) alpha).
Qed.

(** Source for [holomorphic_rotated_germ_ideal_composition]: the
    literal original relation I_(gh)=(I_g)_h for complex germs,
    3.4.12, p. 339. *)
Lemma holomorphic_rotated_germ_ideal_composition (I:set G) (g h:U) (beta:G):
  @holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I (mulU g h) beta <->
  exists alpha,@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g alpha /\P h alpha=beta.
Proof.
rewrite holomorphic_rotated_germ_ideal_membership;split.
- move=>[gamma [hGamma hValue]];exists (P g gamma);split.
  + apply/holomorphic_rotated_germ_ideal_membership;by exists gamma.
  + by rewrite -holomorphic_unitary_germ_map_composition.
- move=>[alpha [/holomorphic_rotated_germ_ideal_membership[gamma [hGamma hValue]] hBeta]].
  exists gamma;split;first exact:hGamma.
  by rewrite holomorphic_unitary_germ_map_composition hValue.
Qed.
End Composition.
