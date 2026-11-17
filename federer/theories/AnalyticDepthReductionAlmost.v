(** Federer (1969), 3.4.8(13), pp. 335–336:
    the original reduction set at the actual dimension
    contains Haar almost every rotation. Every other
    reduction index is impossible. This combines the
    proved almost-cover with the actual dimension comparison;
    the original nonemptiness assertion follows from Haar mass one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  HilbertFormCompactness InnerMetric HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology
  LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  AnalyticGermRing CommutativeIdealUP SetGermUP GermVanishingSealed AnalyticDepthSealed
  AnalyticReductionActual AnalyticReductionIndexDimension AnalyticReductionAlmostCover
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DepthAlmost.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).
Variable I:set G.
Hypothesis hPrime:is_prime_commutative_ideal I.
Hypothesis hVanishing:exists sigma:@set_germ_space T 0,I=ideal sigma.
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he)
  O mulO invO unitO.
Local Notation E:=(@analytic_reduction_actual_E R X B hB n e he omega I).

(** Source for [analytic_depth_reduction_haar_almost]: the
    original dimension-index E_m is Haar conull,
    3.4.8(13), p. 328, proved on pp. 335–336.
    The proof retains every original rotation and both
    dimension endpoints. *)
Theorem analytic_depth_reduction_haar_almost (m:'I_n.+1) (theta:set O->\bar R):
  depth I=(m:nat) ->is_normalised_haar_measure mulO theta ->
  measure_almost_everywhere theta (E m).
Proof.
move=>hDepth hTheta.
have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
have hCover:=@analytic_prime_reductions_almost_cover R X B hB n e he
  (@euclidean_coordinate_orthonormal_family R n) omega hDual I mulO invO unitO hO theta hPrime hTheta.
have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
apply:(@measure_almost_everywhere_mono R (Choice.clone O _) theta hMeasure
  (\bigcup_j E j) (E m) _ hCover)=>g [j hj hEj].
have hIndexDepth:=@analytic_prime_reduction_index_dimension R n I j g hPrime hVanishing hEj.
have hIndex:j=m by apply:val_inj;exact:eq_trans (esym hIndexDepth) hDepth.
by rewrite -hIndex.
Qed.

(** Source for [analytic_reduction_nonempty_dimension_criterion]:
    E_m is nonempty exactly at the original dimension,
    the first assertion of 3.4.8(13), p. 328.
    A normalized Haar measure is selected only as a
    local existence witness in the reverse implication. *)
Theorem analytic_reduction_nonempty_dimension_criterion (m:'I_n.+1):
  (exists g,E m g) <->depth I=(m:nat).
Proof.
split.
- move=>[g hg];exact:(@analytic_prime_reduction_index_dimension R n I m g hPrime hVanishing hg).
- move=>hDepth.
  have [theta hTheta]:=@orthogonal_normalised_haar_measure_exists R X B hB n e he
    mulO invO unitO hO.
  have hAlmost:=analytic_depth_reduction_haar_almost hDepth hTheta.
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
