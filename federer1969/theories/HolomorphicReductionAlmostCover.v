(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(13),
    p. 335: the original E_0 through E_n cover almost every
    unitary rotation. Apply the existing finite B-tail covering
    argument to the two proved original exceptional differences. *)
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
From Federer Require Import HolomorphicReductionHaarDifference HolomorphicReductionHaarSuffixDifference ReductionTailCover MeasureAlmostUP.
Section AlmostCover.
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


Local Notation A:=(@holomorphic_reduction_actual_A R X H hH n e he omega I).
Local Notation Bj:=(@holomorphic_reduction_actual_B R X H hH n e he omega I).
Local Notation C:=(@holomorphic_reduction_actual_C R X H hH n e he omega I).
Local Notation E:=(@holomorphic_reduction_actual_E R X H hH n e he omega I).
(** Source for [holomorphic_prime_reductions_almost_cover]: the
    complement of the original union E_0 through E_n
    is Haar null, 3.4.8(13), p. 335.
    Both zero and full prefixes remain. The proof
    adds no measurability or generic-direction premise. *)
Theorem holomorphic_prime_reductions_almost_cover (theta:set U->\bar R):
  is_prime_commutative_ideal I ->is_normalised_haar_measure mulU theta ->
  measure_almost_everywhere theta (\bigcup_m E m).
Proof.
move=>hPrime hTheta.
have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
pose N1:set U:=\bigcup_(j in @setT 'I_n) (A (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) `\` Bj j).
pose N2:set U:=\bigcup_(m in @setT 'I_n) ([set g|forall j:'I_n,(m<=j)%N ->Bj j g] `\` C m).
have hN1:theta N1=0%E.
  have hEach (j:'I_n) (hj:setT j):theta (A (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) `\` Bj j)=0%E.
    exact:(@holomorphic_reduction_A_minus_B_haar_null R X H hH n e he omega hDual I hPrime.1 hPrime.2.1 hON
      mulO invO unitO hO mulU invU unitU hU j theta hTheta).
  exact (@measure_null_countable_union R (Choice.clone U _) [the choiceType of 'I_n]
    theta hMeasure setT (fun j:'I_n=>A (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) `\` Bj j)
    (countableP setT) hEach).
have hN2:theta N2=0%E.
  have hEach (m:'I_n) (hm:setT m):theta ([set g|forall j:'I_n,(m<=j)%N ->Bj j g] `\` C m)=0%E.
    exact:(@holomorphic_reduction_B_minus_C_haar_null R X H hH n e he omega hDual I hON
      mulO invO unitO hO mulU invU unitU hU m theta hPrime hTheta).
  exact (@measure_null_countable_union R (Choice.clone U _) [the choiceType of 'I_n]
    theta hMeasure setT (fun m:'I_n=>[set g|forall j:'I_n,(m<=j)%N ->Bj j g] `\` C m)
    (countableP setT) hEach).
have hNull:=measure_null_union hMeasure hN1 hN2.
have hBadSubset:(~` (\bigcup_m E m)) `<=` N1 `|` N2.
move=>g hNotCovered.
apply:contrapT=>hOutside;apply:hNotCovered.
have hLoci:=@holomorphic_reduction_actual_laws R X H hH n e he omega I.
have hA0:~A ord0 g.
  by move/(holomorphic_reduction_A_membership hLoci ord0 g)=>[hPositive _];rewrite ltn0 in hPositive.
have hAB (j:'I_n):A (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) g ->Bj j g.
  move=>hA;apply:contrapT=>hNot;apply:hOutside;left;exists j;first exact:Logic.I.
  by split.
have hBC (m:'I_n):(forall j:'I_n,(m<=j)%N ->Bj j g) ->C m g.
  move=>hTail;apply:contrapT=>hNot;apply:hOutside;right;exists m;first exact:Logic.I.
  by split.
have [m hEm]:=@reduction_tail_cover n U A E Bj C g hA0
  (fun m=>holomorphic_reduction_E_membership hLoci m g)
  (holomorphic_reduction_E_last_membership hLoci g) hAB hBC.
by exists m.
exact (@measure_null_subset R (Choice.clone U _) theta hMeasure
  (~` (\bigcup_m E m)) (N1 `|` N2) hBadSubset hNull).
Qed.
End AlmostCover.
