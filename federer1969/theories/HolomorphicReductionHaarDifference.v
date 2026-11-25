(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(7),
    pp. 326, 329: original A_p minus B_p is unitary Haar
    null. Apply existing compact-group coset averaging to the actual
    Borel sets, original fixed-coordinate subgroup and proved
    original null sections. *)
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
From Federer Require Import TopologicalGroupLaws UnitaryGroupClosed UnitaryCoordinateFixingHaar.
From Federer Require Import OrthonormalFamilies CommutativeIdealUP HaarIntegralUP CompactGroupHaarNormalisation
  MeasureUP MeasureBasic MeasureAlmostBasic TopologicalBorel HolomorphicReductionActualBorel HolomorphicReductionACosets
  HolomorphicReductionHaarFibre UnitaryFixingSphereAction UnitaryCoordinateCountableBase CompactGroupBorelCosetNull.
Section Difference.
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
Variable hI:is_commutative_ideal I.
Variable hProper:~I 1.
Variable hON:orthonormal_family H e.
Local Notation Q:=(@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.


Variable j:'I_n.
Local Notation p:=((j:nat).+1).
Local Notation aIndex:=(@Ordinal n.+1 p (ltn_ord j)).
Local Notation J:=([set i:'I_n|(p<=i)%N]).
Local Notation F:=(@holomorphic_prefix_rotation_group R X H hH (n+n) eR heR n e p).
Local Notation A:=(@holomorphic_reduction_actual_A R X H hH n e he omega I aIndex).
Local Notation Bj:=(@holomorphic_reduction_actual_B R X H hH n e he omega I j).

(** Source for [holomorphic_reduction_A_minus_B_haar_null]: the
    entire original assertion A_p minus B_p is Haar null, with the
    original complex ideal and coordinates, 3.4.12, p. 339. *)
Theorem holomorphic_reduction_A_minus_B_haar_null (theta:set U->\bar R):
  is_normalised_haar_measure mulU theta ->theta (A `\` Bj)=0%:E.
Proof.
move=>hTheta.
pose Bad:set U:=A `\` Bj.
have hSub:=@unitary_coordinate_fixing_subgroup R X H hH (n+n) eR heR n e
  mulO invO unitO hO mulU invU unitU hU J.
have [mulF [invF [unitF hF]]]:=subgroup_restriction_exists hSub.
have hLocalU:=@subgroup_restriction_locally_compact_hausdorff O mulO invO unitO U mulU invU unitU hU
  (@orthogonal_group_lch R XR B hB (n+n) eR heR mulO invO unitO hO)
  (@unitary_group_closed R X H hH (n+n) eR heR).
have hLocalF:=@unitary_fixing_group_lch R X H hH (n+n) eR heR n e J
  mulO invO unitO hO mulU invU unitU hU mulF invF unitF hF.
have hCompactF:=@unitary_coordinate_fixing_compact R X H hH (n+n) eR heR n e J.
have [beta hBeta]:=normalised_haar_measure_exists R hLocalF hCompactF.
have [lambda [hLambda hNu hRep hRegular]]:=hBeta.1.
have [baseU hBaseU]:=@unitary_group_countable_base R X H hH (n+n) eR heR.
have [baseF hBaseF]:=@unitary_coordinate_fixing_countable_base R X H hH (n+n) eR heR n e J.
have hBad:borel_set Bad.
  exact:(borel_set_difference
    (@holomorphic_reduction_actual_A_borel R X H hH n e he omega hDual I hI aIndex)
    (@holomorphic_reduction_actual_B_borel R X H hH n e he omega hDual I hI j)).
have hCosets (g:U):beta [set h:F|Bad (mulU g (set_val h))]=0%:E.
  case:(pselect (A g))=>hA.
  - have hAlmost:=@holomorphic_reduction_haar_fibre_almost_B R X H hH n e he hON omega hDual I hI hProper
      j mulO invO unitO hO mulU invU unitU hU mulF invF unitF hF beta g hBeta.1 hA.
    apply:(@measure_null_subset R (Choice.clone F _) beta hNu _ _ _ hAlmost).
    by move=>h [hFirst hNotSecond].
  - have hEmpty:[set h:F|Bad (mulU g (set_val h))]=set0.
      apply/seteqP;split;last by [].
      move=>h [hFirst hNotSecond];exfalso;apply:hA.
      exact:((@holomorphic_reduction_A_prefix_coset R X H hH n e he omega hDual I
        mulO invO unitO hO mulU invU unitU hU aIndex g (set_val h) (set_valP h)).1 hFirst).
    rewrite hEmpty;exact:measure_empty.
exact:(@compact_group_borel_coset_null R U F mulU invU unitU mulF invF unitF hLocalU hLocalF
  (@unitary_group_compact R X H hH (n+n) eR heR) baseU baseF hBaseU hBaseF set_val
  (@set_type_val_continuous U F) theta beta Bad hTheta hBeta hBad hCosets).
Qed.
End Difference.
