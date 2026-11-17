(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(14), pp. 328, 336:
    a finite original irreducible union has no greater
    dimension than a common bound for its components. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import UnitaryGroupHaar FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  HilbertFormCompactness InnerMetric HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology
  LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  HolomorphicGermRing CommutativeIdealUP SetGermUP HolomorphicGermVanishingSealed HolomorphicDepthSealed AnalyticReductionDepthUP
  HolomorphicReductionActual HolomorphicReductionIndexDimension HolomorphicReductionAlmostCover
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  HolomorphicDepthReductionAlmost HolomorphicIrreducibleGermUP HolomorphicIrreducibleProperPrime
  HolomorphicVarietyGermUP SetGermFiniteUnion HolomorphicReductionFiniteUnion HolomorphicReductionEAllIndexTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteDepth.
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
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
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

(** Source for [holomorphic_finite_irreducible_union_tail_almost]:
    simultaneous original directional witnesses, extending 3.4.11,
    p. 338, under 3.4.12, p. 339. This exposes the conull
    portion of the existing finite-union depth proof. *)
Theorem holomorphic_finite_irreducible_union_tail_almost (F:seq G) d (theta:set O->\bar R):
  is_normalised_haar_measure mulU theta ->F<>[::] ->
  (forall beta,beta \in F ->@is_nonempty_irreducible_holomorphic_germ R X NX hNX 0 beta) ->
  (forall beta,beta \in F ->(depth (ideal beta)<=d)%N) ->
  measure_almost_everywhere theta [set g|forall j:'I_n,(d<=j)%N ->
    @holomorphic_reduction_actual_B R X Herm hHerm n e he omega
      (ideal (@set_germ_finite_union T (0%R:X) F)) j g].
Proof.
move=>hTheta hNonempty hIrreducible hD.
have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
have hIndex beta:(depth (ideal beta)<n.+1)%N.
  exact:leq_ltn_trans (analytic_reduction_depth_bound (@HolomorphicDepth.laws R X Herm hHerm n e he omega (ideal beta))) (ltnSn n).
pose index beta:'I_n.+1:=Ordinal (hIndex beta).
pose P beta:set O:=@holomorphic_reduction_actual_E R X Herm hHerm n e he omega (ideal beta) (index beta).
have hEach beta (hBeta:beta \in F):measure_almost_everywhere theta (P beta).
  have hBetaIrreducible:=hIrreducible beta hBeta.
  have hPrime:=(@holomorphic_irreducible_proper_prime_equivalence R X NX hNX 0 beta hBetaIrreducible.1.1).1 hBetaIrreducible.
  have hVanishing:exists sigma:@set_germ_space T 0,ideal beta=ideal sigma by exists beta.
  exact:(@holomorphic_depth_reduction_haar_almost R n (ideal beta) hPrime hVanishing
    mulO invO unitO hO mulU invU unitU hU (index beta) theta erefl hTheta).
have hAlmost:=@measure_almost_everywhere_countable R (Choice.clone O _) G theta hMeasure
  [set beta|beta \in F] P (finite_set_countable (finite_seq F)) hEach.
apply:(@measure_almost_everywhere_mono R (Choice.clone O _) theta hMeasure
  [set g|forall beta,beta \in F ->P beta g]
  [set g|forall j:'I_n,(d<=j)%N ->
    @holomorphic_reduction_actual_B R X Herm hHerm n e he omega
      (ideal (@set_germ_finite_union T (0%R:X) F)) j g] _ hAlmost).
move=>g hAll j hDJ.
apply:(@holomorphic_reduction_finite_union R X Herm hHerm n e he omega F j g hNonempty).
- move=>beta hBeta;exact:(hIrreducible beta hBeta).2.
- move=>beta hBeta.
  apply:(@holomorphic_reduction_E_all_index_tail R X Herm hHerm n e he omega (ideal beta) (index beta) g (hAll beta hBeta) j).
  exact:leq_trans (hD beta hBeta) hDJ.
Qed.
End FiniteDepth.
