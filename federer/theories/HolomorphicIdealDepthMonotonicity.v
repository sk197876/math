(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), p. 333:
    an irreducible component has no larger
    dimension than the original variety germ.
    These supporting laws follow from the original
    directional witnesses and reverse ideal inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology HolomorphicGermRing HolomorphicRotatedGermIdeal
  HolomorphicReductionLociUP HolomorphicReductionActual AnalyticReductionDepthUP
  AnalyticReductionDepthLaws HolomorphicDepthSealed SetGermUP SetGermOrder HolomorphicGermVanishingSealed
  HolomorphicGermVanishingMonotonicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Depth.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation G:=(@holomorphic_germ_ring R X NX hNXR 0).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).

(** Source for [holomorphic_rotated_ideal_inclusion]:
    original ideal inclusion is preserved under
    the coordinate change in 3.4.8(11),
    p. 333. This is a supporting law. *)
Lemma holomorphic_rotated_ideal_inclusion (I J:set G) (g:O):
  I `<=` J ->
  @holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g `<=`
    @holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR J g.
Proof.
move=>hIJ alpha /holomorphic_rotated_germ_ideal_membership [beta [hBeta hEqual]].
apply/holomorphic_rotated_germ_ideal_membership;exists beta;split;[exact:hIJ beta hBeta|exact:hEqual].
Qed.

(** Source for [holomorphic_reduction_B_ideal_monotone]:
    a directional witness in a smaller ideal
    remains one in a larger ideal, supporting
    3.4.8(11), p. 333. *)
Lemma holomorphic_reduction_B_ideal_monotone (I J:set G):
  I `<=` J ->forall j g,
  @holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g ->
  @holomorphic_reduction_actual_B R X Herm hHerm n e he omega J j g.
Proof.
move=>hIJ j g.
have hI:=@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega I.
have hJ:=@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega J.
move/(holomorphic_reduction_B_membership hI j g)=>[alpha [hAlpha [hQ hDirection]]].
apply/(holomorphic_reduction_B_membership hJ j g);exists alpha;split.
- exact:(@holomorphic_rotated_ideal_inclusion I J g hIJ alpha hAlpha).
- by split.
Qed.

(** Source for [holomorphic_ideal_depth_antitone]:
    a larger original ideal has no larger
    depth, supporting the component reduction in
    3.4.8(11), p. 333. No properness
    or finite-generation premise is needed here. *)
Lemma holomorphic_ideal_depth_antitone (I J:set G):I `<=` J ->(depth J<=depth I)%N.
Proof.
move=>hIJ;apply:(@analytic_reduction_depth_monotone n O
  (@holomorphic_reduction_actual_B R X Herm hHerm n e he omega I)
  (@holomorphic_reduction_actual_B R X Herm hHerm n e he omega J)
  (depth I) (depth J)).
- exact:holomorphic_reduction_B_ideal_monotone hIJ.
- exact:HolomorphicDepth.laws.
- exact:HolomorphicDepth.laws.
Qed.

(** Source for [holomorphic_variety_ideal_depth_monotone]:
    local containment of variety germs implies
    the corresponding dimension inequality in
    3.4.8(11), p. 333. Dimension is
    expressed by its original defining ideal depth. *)
Lemma holomorphic_variety_ideal_depth_monotone
  (alpha beta:@set_germ_space (Topological.clone (real_norm_metric_space hNXR) _) 0):
  set_germ_subset alpha beta ->
  (depth (@HolomorphicSetIdeal.value R X NX hNXR 0 alpha)<=
    depth (@HolomorphicSetIdeal.value R X NX hNXR 0 beta))%N.
Proof.
move=>hAB;apply:holomorphic_ideal_depth_antitone.
exact:(@holomorphic_set_ideal_antitone R X NX hNXR 0 alpha beta hAB).
Qed.
End Depth.
