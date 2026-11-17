(** Federer (1969), 3.4.8(14), pp. 328, 336:
    a finite original irreducible union has no greater
    dimension than a common bound for its components. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  HilbertFormCompactness InnerMetric HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology
  LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  AnalyticGermRing CommutativeIdealUP SetGermUP GermVanishingSealed AnalyticDepthSealed AnalyticReductionDepthUP
  AnalyticReductionActual AnalyticReductionIndexDimension AnalyticReductionAlmostCover
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  AnalyticDepthReductionAlmost AnalyticIrreducibleGermUP AnalyticIrreducibleProperPrime
  AnalyticVarietyGermUP SetGermFiniteUnion AnalyticReductionFiniteUnion AnalyticReductionEAllIndexTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteDepth.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation G:=(@set_germ_space T 0).
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).
(** Source for [analytic_finite_irreducible_union_depth_bound]: the upper
    inequality in original 3.4.8(14), pp. 328, 336.
    One common Haar-generic rotation supplies every original
    component witness; their actual product gives the union
    witness. No dimension conclusion is a hypothesis. *)
Theorem analytic_finite_irreducible_union_depth_bound (F:seq G) d:
  F<>[::] ->
  (forall beta,beta \in F ->@is_nonempty_irreducible_analytic_germ R X NX hNX 0 beta) ->
  (forall beta,beta \in F ->(depth (ideal beta)<=d)%N) ->
  (depth (ideal (@set_germ_finite_union T (0%R:X) F))<=d)%N.
Proof.
move=>hNonempty hIrreducible hD.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
have [theta hTheta]:=@orthogonal_normalised_haar_measure_exists R X B hB n e he mulO invO unitO hO.
have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
have hIndex beta:(depth (ideal beta)<n.+1)%N.
  exact:leq_ltn_trans (analytic_reduction_depth_bound (@AnalyticDepth.laws R X B hB n e he omega (ideal beta))) (ltnSn n).
pose index beta:'I_n.+1:=Ordinal (hIndex beta).
pose P beta:set O:=@analytic_reduction_actual_E R X B hB n e he omega (ideal beta) (index beta).
have hEach beta (hBeta:beta \in F):measure_almost_everywhere theta (P beta).
  have hBetaIrreducible:=hIrreducible beta hBeta.
  have hPrime:=(@analytic_irreducible_proper_prime_equivalence R X NX hNX 0 beta hBetaIrreducible.1.1).1 hBetaIrreducible.
  have hVanishing:exists sigma:@set_germ_space T 0,ideal beta=ideal sigma by exists beta.
  exact:(@analytic_depth_reduction_haar_almost R n (ideal beta) hPrime hVanishing
    mulO invO unitO hO (index beta) theta erefl hTheta).
have hAlmost:=@measure_almost_everywhere_countable R (Choice.clone O _) G theta hMeasure
  [set beta|beta \in F] P (finite_set_countable (finite_seq F)) hEach.
have hMass:theta setT<>0%E.
  rewrite hTheta.2;move=>hEqual.
  have hOne:(1:R)=0:=EFin_inj hEqual.
  have hDifferent:(1:R)!=0 by rewrite oner_eq0.
  apply:(negP hDifferent);apply/eqP;exact:hOne.
have [g [_ hAll]]:=measure_almost_positive_set_witness hMeasure hMass hAlmost.
apply:(analytic_reduction_depth_minimal
  (@AnalyticDepth.laws R X B hB n e he omega (ideal (@set_germ_finite_union T (0%R:X) F)))).
exists g=>j hDJ.
apply:(@analytic_reduction_finite_union R X B hB n e he omega F j g hNonempty).
- move=>beta hBeta;exact:(hIrreducible beta hBeta).2.
- move=>beta hBeta.
  apply:(@analytic_reduction_E_all_index_tail R X B hB n e he omega (ideal beta) (index beta) g (hAll beta hBeta) j).
  exact:leq_trans (hD beta hBeta) hDJ.
Qed.
End FiniteDepth.
