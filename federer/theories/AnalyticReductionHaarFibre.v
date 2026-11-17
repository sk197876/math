(** Federer (1969), 3.4.8(6), pp. 328–329:
    if g belongs to original A_p, then gh
    belongs to original B_p for Haar almost
    every h in original H_p. The positive
    derivative order, actual sphere comparison and
    arbitrary Haar normalization are all proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct HomInner
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology HaarIntegralUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermRing AnalyticGermJetsSealed
  CommutativeIdealUP AnalyticRotatedGermIdeal AnalyticReductionLociUP AnalyticReductionActual AnalyticReductionPrefixWitness
  AnalyticReductionDirectionalTransport AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilySealed
  AnalyticPrefixGermSubring AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap
  AnalyticPrefixGermMapLaws PointedAnalyticLinearPullbackDiagonal
  MetricSubsetBackground HausdorffMeasure EuclideanAnalyticDirections OrthogonalCoordinateFixing
  AnalyticPrefixSphereAction AnalyticPrefixSphereAxis AnalyticPrefixSphereHaarNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Fibre.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=(@analytic_germ_ring R X NX hNX 0).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Hypothesis hProper:~I 1.
Variable j:'I_n.
Local Notation p:=((j:nat).+1).
Local Notation hPN:=(ltn_ord j).
Local Notation aIndex:=(@Ordinal n.+1 p (ltn_ord j)).
Local Notation Y:=(R_n R p).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R p)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R p)).
Local Notation P:=(@AnalyticPrefixCoordinates.projection R X n omega p hPN).
Local Notation S:=(@AnalyticPrefixCoordinates.inclusion R X n e p hPN).
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega p hPN).
Local Notation H:=(@analytic_prefix_rotation_group R X B hB n e he p).
Local Notation sphere:=(@analytic_prefix_unit_sphere R X B hB n e p).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.
Variables (mulH:H->H->H) (invH:H->H) (unitH:H).
Hypothesis hH:is_subgroup_restriction mulO invO unitO H mulH invH unitH.

(** Source for [analytic_reduction_haar_fibre_almost_B]: the
    entire original assertion (6), 3.4.8, p. 326,
    proved on pp. 328–329. Array index j
    denotes the printed p=j+1, and the original
    Haar measure need not have total mass one. *)
Theorem analytic_reduction_haar_fibre_almost_B (mu:set H->\bar R) (g:O):
  is_left_haar_measure mulH mu ->
  @analytic_reduction_actual_A R X B hB n e he omega I aIndex g ->
  measure_almost_everywhere mu
    [set h:H|@analytic_reduction_actual_B R X B hB n e he omega I j (mulO g (set_val h))].
Proof.
move=>hMu hA.
have [beta [hRotated [hBeta [k [hPositive [hTop hLower]]]]]]:=
  @analytic_reduction_prefix_witness R X B hB n e he omega I aIndex g hI hProper hA.
pose diagonal:=fun y:Y=>@ContinuousMultilinear.evaluation R k Y R^o NY (fun z=>`|z|) hNY
  (@scalar_absolute_value_norm R) [ffun _:'I_k=>y] (@AnalyticGermJets.value R Y NY hNY 0 k beta).
have [_ hSphereNull]:=@euclidean_analytic_germ_exceptional_directions_null R p 0 k beta hTop.
have hNull:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R p)) (p-1)
    [set y|NY y = 1 /\diagonal y = 0] = 0%E.
  have hSame:[set y:Y|NY y = 1 /\diagonal y = 0] = [set y:Y|diagonal y = 0 /\NY y = 1].
    by apply/seteqP;split=>y [h1 h2];split.
  rewrite hSame;exact:hSphereNull.
pose u:metric_subset sphere:=exist _ (e j)
  (mem_set (@analytic_prefix_sphere_axis_member R X B hB n e hON j)).
have hOrbitNull:=@analytic_prefix_sphere_haar_coordinate_null R X B hB n e he hON omega hDual
  p hPN (ltn0Sn (j:nat)) P S
  (@AnalyticPrefixCoordinates.projection_laws R X n omega p hPN)
  (@AnalyticPrefixCoordinates.inclusion_laws R X n e p hPN)
  mulO invO unitO hO mulH invH unitH hH mu u [set y|diagonal y = 0] hMu hNull.
pose Good:set H:=[set h|diagonal (P (@orthogonal_element_map R X B hB n e he (set_val h) (e j)))<>0].
have hAlmostGood:measure_almost_everywhere mu Good.
  rewrite /measure_almost_everywhere.
  have hComplement:~` Good = [set h:H|diagonal (P (@orthogonal_element_map R X B hB n e he (set_val h) (e j))) = 0].
    apply/seteqP;split=>h.
    - move=>hNot;apply:contrapT=>hNonzero;exact:hNot hNonzero.
    - move=>hZero hGood;exact:hGood hZero.
  rewrite hComplement;exact:hOrbitNull.
have [lambda [hLambda hMeasure hRep hRegular]]:=hMu.
apply:(@measure_almost_everywhere_mono R (Choice.clone H _) mu hMeasure Good
  [set h:H|@analytic_reduction_actual_B R X B hB n e he omega I j (mulO g (set_val h))]
  _ hAlmostGood)=>h hGood.
have hQAlpha:@AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega p (E beta).
  have hQLaws:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
  rewrite (analytic_coordinate_subring_family_member hQLaws hPN).
  apply/analytic_prefix_germ_subring_membership;by exists beta.
have hDirection:has_nonzero_analytic_directional_jet (E beta)
    (@orthogonal_element_map R X B hB n e he (set_val h) (e j)).
  exists k;split;first exact:hPositive.
  rewrite (@pointed_analytic_linear_pullback_diagonal R X Y NX NY hNX hNY 0 0 P E
    (@analytic_prefix_germ_map_specification R X NX hNX n e he omega p hPN)
    (@analytic_prefix_projection_zero R X n omega p hPN) k beta
    (@orthogonal_element_map R X B hB n e he (set_val h) (e j))).
  exact:hGood.
refine (@analytic_reduction_directional_transport R X B hB n e he omega hDual I
  mulO invO unitO hO j g (set_val h) (E beta) _ _ _ _).
- exact:set_valP h.
- have hBounds:(ltn_ord aIndex:is_true (p<=n)%N) = hPN.
    exact:(@bool_irrelevance (p<=n)%N (ltn_ord aIndex) hPN).
  rewrite hBounds in hRotated;exact:hRotated.
- exact:hQAlpha.
- exact:hDirection.
Qed.
End Fibre.
