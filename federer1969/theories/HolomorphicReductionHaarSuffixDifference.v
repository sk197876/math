(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(9),
    pp. 327, 330: the original B-tail minus C_m is unitary
    Haar null. Apply the proved compact Borel coset averaging theorem
    to the actual original suffix group and its null sections. *)
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
From mathcomp Require Import cardinality.
From Federer Require Import HolomorphicReductionHaarSuffix HolomorphicReductionSuffixCosets.
Section SuffixDifference.
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
Variable hON:orthonormal_family H e.
Local Notation Q:=(@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.


Variable m:'I_n.
Local Notation J:=([set i:'I_n|(i<m)%N]).
Local Notation F:=(@holomorphic_suffix_rotation_group R X H hH (n+n) eR heR n e m).
Local Notation Bj:=(@holomorphic_reduction_actual_B R X H hH n e he omega I).
Local Notation S:=([set g:U|forall j:'I_n,(m<=j)%N ->Bj j g]).
Local Notation Cm:=(@holomorphic_reduction_actual_C R X H hH n e he omega I m).
(** Source for [holomorphic_reduction_B_minus_C_haar_null]: the
    complete original complex counterpart of (9), with precisely the
    original prime ideal and normalized unitary Haar measure,
    3.4.12, p. 339. *)
Theorem holomorphic_reduction_B_minus_C_haar_null (theta:set U->\bar R):
  is_prime_commutative_ideal I ->is_normalised_haar_measure mulU theta ->theta (S `\` Cm)=0%:E.
Proof.
move=>hPrime hTheta.
pose Bad:set U:=S `\` Cm.
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
have hSBorel:borel_set S.
  pose D:set 'I_n:=fun j=>(m<=j)%N.
  change (borel_set (\bigcap_(j in D) Bj j)).
  apply:(@borel_set_countable_intersection U (Choice.clone 'I_n _) D Bj).
  - exact:(finite_set_countable (@finite_finset (Finite.clone 'I_n _) D)).
  - exists m;exact:leqnn.
  - move=>j _;exact:(@holomorphic_reduction_actual_B_borel R X H hH n e he omega hDual I hPrime.1 j).
have hBad:borel_set Bad.
  exact:(borel_set_difference hSBorel
    (@holomorphic_reduction_actual_C_borel R X H hH n e he omega hDual I hPrime.1 m)).
have hCosets (g:U):beta [set q:F|Bad (mulU g (set_val q))]=0%:E.
  case:(pselect (S g))=>hS.
  - have hAlmost:=@holomorphic_reduction_suffix_haar_almost_C_B R X H hH n e he omega hDual hON I g m
      mulO invO unitO hO mulU invU unitU hU mulF invF unitF hF beta hPrime hS hBeta.1.
    apply:(@measure_null_subset R (Choice.clone F _) beta hNu _ _ _ hAlmost).
    move=>q [hAll hNotC] [hC hAllB];exact:hNotC hC.
  - have hEmpty:[set q:F|Bad (mulU g (set_val q))]=set0.
      apply/seteqP;split;last by [].
      move=>q [hAll hNotC];exfalso;apply:hS.
      exact:((@holomorphic_reduction_B_suffix_coset R X H hH n e he omega hDual hON I hPrime.1 hPrime.2.1 m
        mulO invO unitO hO mulU invU unitU hU mulF invF unitF hF g q).1 hAll).
    rewrite hEmpty;exact:measure_empty.
exact:(@compact_group_borel_coset_null R U F mulU invU unitU mulF invF unitF hLocalU hLocalF
  (@unitary_group_compact R X H hH (n+n) eR heR) baseU baseF hBaseU hBaseF set_val
  (@set_type_val_continuous U F) theta beta Bad hTheta hBeta hBad hCosets).
Qed.
End SuffixDifference.
