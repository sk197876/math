(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(13), pp. 335–336:
    a positive original E_m reduction of an irreducible
    variety has m equal to its actual ideal depth.
    Apply the proved model (10), upper-null representative
    from (11), and positive measure of every nonempty
    m-dimensional holomorphic manifold germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import UnitaryGroupClosed TopologicalGroupLaws HolomorphicReductionIndexDimension HolomorphicReductionAlmostCover HaarIntegralUP CompactGroupHaarNormalisation MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness IsotropyGroupTopology LinearGroupTopology LinearGroupSealed HolomorphicPrimeReductionDimension HolomorphicLastReductionDepth StandardHermitianBasisValues UnitaryGroupHaar UnitaryComplexMapSealed HolomorphicRotatedCompositionInverse FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm InnerMetric
  HilbertFormCompactness OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  HolomorphicGermRing CommutativeIdealUP SetGermUP SetGermSealed SetGermOrder SetGermBooleanOrder
  HolomorphicGermVanishingSealed HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermSealed HolomorphicIdealVarietyGermExistence
  HolomorphicReductionActual HolomorphicReductionLociUP AnalyticReductionDepthUP HolomorphicDepthSealed
  HolomorphicRotatedGermIdeal HolomorphicRotatedIdealDepth HolomorphicRotatedIdealRecovery
  HolomorphicPrimeLocalModelUP HolomorphicPrimeLocalModelLaws Federer3412PrimeReduction
  FunctionalHolomorphicManifold HolomorphicGermHigherDegreeNull HolomorphicSubmanifoldGermNonNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DepthAlmost.
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
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).


Variable I:set G.
Hypothesis hPrime:is_prime_commutative_ideal I.
Hypothesis hVanishing:exists sigma:@set_germ_space T 0,I=ideal sigma.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation Orth:=(@orthogonal_group R XR B hB (n+n) eR heR).
Variables (mulO:Orth->Orth->Orth) (invO:Orth->Orth) (unitO:Orth).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR)
  Orth mulO invO unitO.
Variables (mulU:O->O->O) (invU:O->O) (unitU:O).
Hypothesis hU:is_subgroup_restriction mulO invO unitO O mulU invU unitU.
Local Notation E:=(@holomorphic_reduction_actual_E R X Herm hHerm n e he omega I).
(** Source for [holomorphic_depth_reduction_haar_almost]: the
    original dimension-index E_m is Haar conull,
    3.4.12, p. 339, extending 3.4.8(13), p. 328, proved on pp. 335–336.
    The proof retains every original rotation and both
    dimension endpoints. *)
Theorem holomorphic_depth_reduction_haar_almost (m:'I_n.+1) (theta:set O->\bar R):
  depth I=(m:nat) ->is_normalised_haar_measure mulU theta ->
  measure_almost_everywhere theta (E m).
Proof.
move=>hDepth hTheta.
have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
have hCover:=@holomorphic_prime_reductions_almost_cover R X Herm hHerm n e he omega hDual I
  (@standard_hermitian_basis_orthonormal R n) mulO invO unitO hO mulU invU unitU hU theta hPrime hTheta.
have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
apply:(@measure_almost_everywhere_mono R (Choice.clone O _) theta hMeasure
  (\bigcup_j E j) (E m) _ hCover)=>g [j hj hEj].
have hIndexDepth:=@holomorphic_prime_reduction_index_dimension R n I j g hPrime hVanishing hEj.
have hIndex:j=m by apply:val_inj;exact:eq_trans (esym hIndexDepth) hDepth.
by rewrite -hIndex.
Qed.

(** Source for [holomorphic_reduction_nonempty_dimension_criterion]:
    E_m is nonempty exactly at the original dimension,
    the first assertion of 3.4.12, p. 339, extending 3.4.8(13), p. 328.
    A normalized Haar measure is selected only as a
    local existence witness in the reverse implication. *)
Theorem holomorphic_reduction_nonempty_dimension_criterion (m:'I_n.+1):
  (exists g,E m g) <->depth I=(m:nat).
Proof.
split.
- move=>[g hg];exact:(@holomorphic_prime_reduction_index_dimension R n I m g hPrime hVanishing hg).
- move=>hDepth.
  have hLocal:=@subgroup_restriction_locally_compact_hausdorff Orth mulO invO unitO
    O mulU invU unitU hU (@orthogonal_group_lch R XR B hB (n+n) eR heR mulO invO unitO hO)
    (@unitary_group_closed R X Herm hHerm (n+n) eR heR).
  have [theta hTheta]:=normalised_haar_measure_exists R hLocal
    (@unitary_group_compact R X Herm hHerm (n+n) eR heR).
  have hAlmost:=holomorphic_depth_reduction_haar_almost hDepth hTheta.
  have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
  have hMass:theta setT<>0%E.
    rewrite hTheta.2;move=>hEqual.
    have hOne:(1:R)=0:=EFin_inj hEqual.
    have hDifferent:(1:R)!=0 by rewrite oner_eq0.
    apply:(negP hDifferent);apply/eqP;exact:hOne.
  have [g [_ hg]]:=measure_almost_positive_set_witness hMeasure hMass hAlmost.
  by exists g.
Qed.
End DepthAlmost.
