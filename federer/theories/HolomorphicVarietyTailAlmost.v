(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    a nonempty original holomorphic variety germ has
    a Haar-conull reduction tail above its original depth.
    Reuse finite irreducible decomposition, component dimension
    monotonicity and the existing component Haar theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology subtype_topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm HilbertFormCompactness
  InnerMetric HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  HolomorphicGermRing SetGermUP SetGermFiniteUnion HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicReductionActual HolomorphicVarietyGermUP HolomorphicIrreducibleGermCoverUP
  NoetherianHolomorphicIrreducibleCover HolomorphicGermNoetherian HolomorphicIdealDepthMonotonicity
  MeasureAlmostUP HolomorphicFiniteUnionTailAlmost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Tail.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T 0).
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).

Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation Orth:=(@orthogonal_group R XR B hB (n+n) eR heR).
Variables (mulO:Orth->Orth->Orth) (invO:Orth->Orth) (unitO:Orth).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR)
  Orth mulO invO unitO.
Variables (mulU:O->O->O) (invU:O->O) (unitU:O).
Hypothesis hU:is_subgroup_restriction mulO invO unitO O mulU invU unitU.

(** Source for [holomorphic_variety_reduction_tail_almost]: all
    original directional witnesses above dim alpha hold
    for Haar almost every rotation, supporting the depth
    comparison of 3.4.12, p. 339, extending 3.4.11, p. 338. The
    ideal is the actual original vanishing ideal;
    no generic statement for arbitrary ideals is inferred. *)
Theorem holomorphic_variety_reduction_tail_almost (alpha:G) (theta:set O->\bar R):
  @is_holomorphic_variety_germ R X NX hNX 0 alpha ->alpha<>@set_germ T 0 set0 ->
  is_normalised_haar_measure mulU theta ->
  measure_almost_everywhere theta [set g|forall j:'I_n,(depth (ideal alpha)<=j)%N ->
    @holomorphic_reduction_actual_B R X Herm hHerm n e he omega (ideal alpha) j g].
Proof.
move=>hHolomorphic hNonempty hTheta.
have [F hCover]:=@noetherian_finite_irreducible_holomorphic_germ_cover R X NX hNX 0
  (@finite_holomorphic_germ_ring_noetherian R X NX (@holomorphic_coordinate_norm_laws R n) n e 0 he) alpha hHolomorphic.
have hUnion:=irreducible_holomorphic_germ_cover_union hCover.
have hF:F<>[::].
  move=>hEmpty;apply:hNonempty;rewrite hEmpty in hUnion;exact:esym hUnion.
have hComponent beta (hBeta:beta \in F):(depth (ideal beta)<=depth (ideal alpha))%N.
  apply:(@holomorphic_variety_ideal_depth_monotone R X Herm hHerm n e he omega beta alpha).
  rewrite -hUnion;exact:set_germ_finite_union_member hBeta.
have hAlmost:=@holomorphic_finite_irreducible_union_tail_almost R n mulO invO unitO hO mulU invU unitU hU
  F (depth (ideal alpha)) theta hTheta hF
  (irreducible_holomorphic_germ_cover_members hCover) hComponent.
by rewrite hUnion in hAlmost.
Qed.
End Tail.
