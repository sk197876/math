(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.11, p. 338:
    the actual leading ideal has a Haar-conull
    reduction tail at the original variety-germ dimension.
    Reuse the original conull tail, the proved cross-ideal
    Haar averaging theorem and its actual leading-polynomial
    fibre connection. No dimension theorem for an arbitrary
    ideal is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import StandardHermitianBasisValues FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  InnerMetric HomInner HilbertFormCompactness OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  HolomorphicGermRing CommutativeIdealUP SetGermUP HolomorphicGermVanishingSealed HolomorphicGermVanishingIdeal
  HolomorphicIdealPropriety HolomorphicDepthSealed HolomorphicReductionActual HolomorphicVarietyGermUP
  HolomorphicInitialIdealSealed HolomorphicInitialIdealLaws HolomorphicVarietyTailAlmost
  HolomorphicReductionBContainedA HolomorphicReductionCrossIdealHaar HolomorphicInitialIdealHaarFibre
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
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

Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation Orth:=(@orthogonal_group R XR B hB (n+n) eR heR).
Variables (mulO:Orth->Orth->Orth) (invO:Orth->Orth) (unitO:Orth).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR)
  Orth mulO invO unitO.
Variables (mulU:O->O->O) (invU:O->O) (unitU:O).
Hypothesis hU:is_subgroup_restriction mulO invO unitO O mulU invU unitU.

(** Source for [holomorphic_initial_ideal_tail_almost]: the
    original leading ideal's simultaneous generic directional
    witnesses, supporting the depth inequality in 3.4.11,
    p. 338. Source holomorphicity and nonempty germ
    are the original hypotheses; every tail index remains. *)
Theorem holomorphic_initial_ideal_tail_almost (alpha:G) (theta:set O->\bar R):
  @is_holomorphic_variety_germ R X NX hNX 0 alpha ->alpha<>@set_germ T 0 set0 ->
  is_normalised_haar_measure mulU theta ->
  measure_almost_everywhere theta [set g|forall j:'I_n,(depth (ideal alpha)<=j)%N ->
    @holomorphic_reduction_actual_B R X Herm hHerm n e he omega
      (@HolomorphicInitialIdeal.value R X NX hNX (ideal alpha)) j g].
Proof.
move=>hHolomorphic hNonempty hTheta.
pose I:set [the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)]:=ideal alpha.
pose K:=@HolomorphicInitialIdeal.value R X NX hNX I.
have hI:=@holomorphic_set_ideal_ring_laws R X NX hNX 0 alpha.
have hK:=@holomorphic_initial_ideal_is_ideal R X NX hNX I.
have hProper:~I 1 by move=>hOne;apply:hNonempty;exact:(holomorphic_set_ideal_contains_one alpha).1 hOne.
have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
have hON:=@standard_hermitian_basis_orthonormal R n.
have hTail:=@holomorphic_variety_reduction_tail_almost R n mulO invO unitO hO mulU invU unitU hU alpha theta
  hHolomorphic hNonempty hTheta.
have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
pose Bj:=fun j:'I_n=>@holomorphic_reduction_actual_B R X Herm hHerm n e he omega K j.
have hEach (j:'I_n) (hJ:(depth I<=j)%N):measure_almost_everywhere theta (Bj j).
  pose A:=@holomorphic_reduction_actual_A R X Herm hHerm n e he omega I
    (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)).
  have hAlmostA:measure_almost_everywhere theta A.
    apply:(@measure_almost_everywhere_mono R (Choice.clone O _) theta hMeasure _ A _ hTail).
    move=>g hG;exact:(@holomorphic_reduction_B_contained_A R X Herm hHerm n e he omega I j g (hG j hJ)).
  have hDefect:theta (A `\` Bj j)=0%E.
    apply:(@holomorphic_reduction_cross_ideal_haar_null R X Herm hHerm n e he omega hDual I hI mulO invO unitO hO mulU invU unitU hU K hK j _ theta hTheta).
    move=>mulH invH unitH hH mu g hMu hAg.
    exact:(@holomorphic_initial_ideal_haar_fibre R X Herm hHerm n e he hON omega hDual I hI hProper j
      mulO invO unitO hO mulU invU unitU hU mulH invH unitH hH mu g hMu hAg).
  have hAlmostImp:measure_almost_everywhere theta [set g|A g ->Bj j g].
    exact:(measure_almost_everywhere_on_implication theta A (Bj j)).1 hDefect.
  have hBoth:=measure_almost_everywhere_and hMeasure hAlmostA hAlmostImp.
  apply:(@measure_almost_everywhere_mono R (Choice.clone O _) theta hMeasure _ (Bj j) _ hBoth).
  by move=>g [hA hImp];exact:hImp hA.
have hCount:countable [set j:'I_n|(depth I<=j)%N].
  exact:finite_set_countable (@finite_finset [the finType of 'I_n] _).
have hAll:=@measure_almost_everywhere_countable R (Choice.clone O _) [the choiceType of 'I_n]
  theta hMeasure [set j:'I_n|(depth I<=j)%N] Bj hCount hEach.
exact:hAll.
Qed.
End Tail.
