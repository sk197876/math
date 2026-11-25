(** Federer (1969), 3.4.8(13), pp. 328, 336:
    assemble the actual prime variety representative and
    its uniform Hausdorff growth in one common orthogonal
    coordinate system. All selected objects remain local witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  HilbertFormCompactness InnerMetric HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology
  LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  AnalyticGermRing CommutativeIdealUP SetGermUP GermVanishingSealed AnalyticDepthSealed
  AnalyticDepthReductionAlmost MappingMultiplicity EuclideanLebesgueDimensions CoordinateProjection
  AnalyticReductionActual AnalyticReductionIndexDimension AnalyticReductionAlmostCover
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  AnalyticPrefixCoordinatesSealed AnalyticPrimeModelCompactRepresentative AnalyticPrimeLocalModelUP
  Federer348PrimeReduction AnalyticReductionLociUP HaarConullRightSelection CoordinateProjectionRotation
  AnalyticRotatedVarietyRepresentative OrthogonalCoordinateModelTransport SetGermCoordinateImage
  CommonCoordinateGrowthRepresentative UniformHausdorffGrowthUP RectifiableSetUP HausdorffMeasure
  ExteriorIndices FiniteAnalyticVarietyUP NormFiniteLinearBound NormBoundedLinearTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RotatedGrowth.
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
Variables U H:set X.
Variable m:'I_n.
Local Notation hMN:=(ltnW (ltn_ord m)).
Local Notation P:=(@AnalyticPrefixCoordinates.projection R X n omega m hMN).
Local Notation om:=(@orthogonal_element_map R X B hB n e he).

(** Source for [analytic_prime_rotated_growth_representative]:
    the original common g and compact representative in
    its coordinates, 3.4.8(13), p. 336. All
    prime models, coordinate rotations, exceptional sets and
    counting bounds are obtained internally. *)
Theorem analytic_prime_rotated_growth_representative:
  U 0 ->@is_finite_analytic_variety R X NX hNX U H ->
  I=ideal (@set_germ T 0 H) ->is_prime_commutative_ideal I ->
  (0<m)%N ->depth I=(m:nat) ->
  exists (g:O) (S:set X) (b:R),
    @compact (inner_metric_space hB) S /\
    @set_germ T 0 S=@set_germ T 0 (om g @^-1` H) /\
    @is_measure_m_rectifiable R (inner_metric_space hB)
      (@hausdorff_measure R (inner_metric_space hB) m) m S /\
    @is_uniform_hausdorff_growth R (inner_metric_space hB) m S b.
Proof.
move=>hU0 hH hIEquation hPrime hPositive hDepth.
have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
have hON:=@euclidean_coordinate_orthonormal_family R n.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
have [theta hTheta]:=@orthogonal_normalised_haar_measure_exists R X B hB n e he mulO invO unitO hO.
have hVanishing:exists sigma:@set_germ_space T 0,I=ideal sigma by exists (@set_germ T 0 H).
have hAlmost:=@analytic_depth_reduction_haar_almost R n I hPrime hVanishing
  mulO invO unitO hO (widen_ord (leqnSn n) m) theta hDepth hTheta.
have [psi hPsi]:=choice (fun lambda:Lambda n m=>
  @coordinate_projection_rotation R n m hMN mulO invO unitO hO lambda).
have [g hAll]:=@haar_conull_right_selection R O mulO invO unitO
  (@orthogonal_group_lch R X B hB n e he mulO invO unitO hO)
  (@orthogonal_group_compact_space R X B hB n e he) theta
  (Choice.clone (Lambda n m) _) setT psi
  (@analytic_reduction_actual_E R X B hB n e he omega I (widen_ord (leqnSn n) m))
  hTheta (countableP setT) hAlmost.
have hEach (lambda:Lambda n m):exists pair:(set X*nat),
    @compact (inner_metric_space hB) pair.1 /\
    @set_germ T 0 pair.1=@set_germ T 0 (om g @^-1` H) /\
    @is_countably_measure_m_rectifiable R (inner_metric_space hB)
      (@hausdorff_measure R (inner_metric_space hB) m) m pair.1 /\
    measure_almost_everywhere (@euclidean_lebesgue_measure R m)
      [set y|(@mapping_multiplicity R (inner_metric_space hB) (R_n R m)
        (@coordinate_projection R n m lambda) pair.1 y<=pair.2%:R%:E)%E].
  pose q:=mulO g (psi lambda).
  have hEm:=hAll lambda Logic.I.
  have [k [first [V [delta [coeff [f [Z [K [hI [hIq [hK [hModel hNonempty]]]]]]]]]]]]:=
    @federer_3_4_8_10 R n e he hON omega hDual I q m hMN hPrime hPositive hEm.
  have hTail:=((analytic_reduction_E_membership
    (@analytic_reduction_actual_laws R X B hB n e he omega I) m q).1 hEm).2.1.
  have [S [hCompact [hSGerm [hNull [hRect hCounts]]]]]:=
    @analytic_prime_model_compact_representative R n m hMN hDual I q hIq k first V delta coeff f Z K hK
      hPositive hModel hTail.
  have hOriginal:=@analytic_rotated_variety_representative R X B hB n e he I hI q hIq U H hU0 hH hIEquation.
  have hActualGerm:@set_germ T 0 S=@set_germ T 0 (om q @^-1` H):=eq_trans hSGerm hOriginal.
  have [hInverseLeft hInverseRight]:=@orthogonal_element_inv R X B hB n e he mulO invO unitO hO (psi lambda).
  pose v:=om (invO (psi lambda)).
  have hVBound:=@norm_finite_linear_bounded R X X NX NX hNX hNX n e he v.
  have hV:=@norm_bounded_linear_continuous R X X NX NX hNX hNX v hVBound.
  have hVGerm:=@set_germ_coordinate_image T 0 (om (psi lambda)) v (om g) (om q) S H
    hV (linear0 v) hInverseLeft hInverseRight
    (@orthogonal_element_mulE R X B hB n e he mulO invO unitO hO g (psi lambda)) hActualGerm.
  have [hTransportCompact [hTransportRect hTransportCaps]]:=
    @orthogonal_coordinate_model_transport R n m lambda (psi lambda) P S Z k%:R%:E
      (hPsi lambda) hCompact hNull hRect hCounts.
  exists (om (psi lambda) @` S,k);split;first exact:hTransportCompact.
  split;first exact:hVGerm.
  by split.
have [F hF]:=choice hEach.
have [S [b [hCompact [hGerm [hRect hGrowth]]]]]:=
  @common_coordinate_growth_representative R n m hMN (om g @^-1` H)
    (fun lambda=>(F lambda).1) (fun lambda=>(F lambda).2%:R)
    hPositive (fun lambda=>(hF lambda).1) (fun lambda=>(hF lambda).2.1)
    (fun lambda=>(hF lambda).2.2.1) (fun lambda=>ler0n R (F lambda).2)
    (fun lambda=>(hF lambda).2.2.2).
exists g,S,b;split;first exact:hCompact.
split;first exact:hGerm.
by split.
Qed.
End RotatedGrowth.
