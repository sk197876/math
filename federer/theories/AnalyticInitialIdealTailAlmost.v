(** Federer (1969), 3.4.11, p. 338:
    the actual leading ideal has a Haar-conull
    reduction tail at the original variety-germ dimension.
    Reuse the original conull tail, the proved cross-ideal
    Haar averaging theorem and its actual leading-polynomial
    fibre connection. No dimension theorem for an arbitrary
    ideal is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  InnerMetric HomInner HilbertFormCompactness OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  AnalyticGermRing CommutativeIdealUP SetGermUP GermVanishingSealed GermVanishingIdeal
  AnalyticIdealPropriety AnalyticDepthSealed AnalyticReductionActual AnalyticVarietyGermUP
  AnalyticInitialIdealSealed AnalyticInitialIdealLaws AnalyticVarietyTailAlmost
  AnalyticReductionBContainedA AnalyticReductionCrossIdealHaar AnalyticInitialIdealHaarFibre
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
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T 0).
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he)
  O mulO invO unitO.

(** Source for [analytic_initial_ideal_tail_almost]: the
    original leading ideal's simultaneous generic directional
    witnesses, supporting the depth inequality in 3.4.11,
    p. 338. Source analyticity and nonempty germ
    are the original hypotheses; every tail index remains. *)
Theorem analytic_initial_ideal_tail_almost (alpha:G) (theta:set O->\bar R):
  @is_analytic_variety_germ R X NX hNX 0 alpha ->alpha<>@set_germ T 0 set0 ->
  is_normalised_haar_measure mulO theta ->
  measure_almost_everywhere theta [set g|forall j:'I_n,(depth (ideal alpha)<=j)%N ->
    @analytic_reduction_actual_B R X B hB n e he omega
      (@AnalyticInitialIdeal.value R X NX hNX (ideal alpha)) j g].
Proof.
move=>hAnalytic hNonempty hTheta.
pose I:set [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]:=ideal alpha.
pose K:=@AnalyticInitialIdeal.value R X NX hNX I.
have hI:=@analytic_set_ideal_ring_laws R X NX hNX 0 alpha.
have hK:=@analytic_initial_ideal_is_ideal R X NX hNX I.
have hProper:~I 1 by move=>hOne;apply:hNonempty;exact:(analytic_set_ideal_contains_one alpha).1 hOne.
have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
have hON:=@euclidean_coordinate_orthonormal_family R n.
have hTail:=@analytic_variety_reduction_tail_almost R n mulO invO unitO hO alpha theta
  hAnalytic hNonempty hTheta.
have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
pose Bj:=fun j:'I_n=>@analytic_reduction_actual_B R X B hB n e he omega K j.
have hEach (j:'I_n) (hJ:(depth I<=j)%N):measure_almost_everywhere theta (Bj j).
  pose A:=@analytic_reduction_actual_A R X B hB n e he omega I
    (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)).
  have hAlmostA:measure_almost_everywhere theta A.
    apply:(@measure_almost_everywhere_mono R (Choice.clone O _) theta hMeasure _ A _ hTail).
    move=>g hG;exact:(@analytic_reduction_B_contained_A R X B hB n e he omega I j g (hG j hJ)).
  have hDefect:theta (A `\` Bj j)=0%E.
    apply:(@analytic_reduction_cross_ideal_haar_null R X B hB n e he omega hDual I hI K hK j
      mulO invO unitO hO _ theta hTheta).
    move=>mulH invH unitH hH mu g hMu hAg.
    exact:(@analytic_initial_ideal_haar_fibre R X B hB n e he hON omega hDual I hI hProper j
      mulO invO unitO hO mulH invH unitH hH mu g hMu hAg).
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
