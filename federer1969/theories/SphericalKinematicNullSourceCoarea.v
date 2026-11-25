(** Federer (1969), 3.2.48, pp. 284–286: signed coarea
    on the entire original source, using the proved countable manifold
    profile. All source, target and actual Jacobian premises are discharged. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  EuclideanHomInnerCharts ProductInner OrthogonalMaps EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  FiniteInnerChartUP FiniteInnerChartCompact FiniteInnerWeightedCoareaProfile EuclideanSubmanifoldUP
  UnitSphereSpace SphericalProductPreimageImage SphericalKinematicSource
  OrthogonalKinematicMap OrthogonalKinematicLipschitz OrthogonalKinematicDimensions OrthogonalKinematicCoareaFibres
  SphericalKinematicTangentProfile SphericalKinematicApproximateProfile SphericalKinematicSourceWeights
  SphericalRectifiablePartition DisjointFamilySelector SphericalKinematicPartitionProfile SphericalKinematicPartitionApproximate NullMeasureIntegral MeasureConullZeroIntegral
  EuclideanStiefelVolumeDimensions LipschitzUP LipschitzBasic RectifiableSetUP HausdorffMeasure
  PartialFunctionBasic PartialFunctionSourceRestriction MeasureApproximateJacobian MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUniqueness MeasureUP MeasureRestriction MeasureIntegralUP MeasureSubsetIntegral
  ParameterizedIntegral PartialFunctionUP PartialZeroExtension SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_null_source_coarea]: the coarea
    equality in 3.2.48, p. 284, with the actual tangent Jacobian
    computed on pp. 285–286. The original null source
    retains completed measurable sets and signed
    summable weights. No differential, Jacobian, fibre-integrability,
    finite-fibre or independent product-measurability premise is added. *)
Theorem spherical_kinematic_null_source_coarea (R:realType) d k m n v
    (c:R_n R (1+d)) (A B:set (R_n R (1+d)))
    (e:Hom (R_n R n) [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type])
    (p:Hom [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type] (R_n R n))
    (a:Hom (R_n R v) (Hom (R_n R (1+d)) (R_n R (1+d))))
    (t:Hom (Hom (R_n R (1+d)) (R_n R (1+d))) (R_n R v))
    (alpha beta:R_n R (1+d)->R) av bv:
  (d<=k+m)%N ->inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R (1+d) ->B `<=` @euclidean_unit_sphere_set R (1+d) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (1+d))) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) m) B ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) A) (real_total_integrand alpha) av%:E ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) m) B) (real_total_integrand beta) bv%:E ->
  is_finite_inner_chart (product_inner (@euclidean_hom_inner_productP R (1+d) (1+d))
    (@euclidean_hom_inner_productP R (1+d) (1+d))) e p ->
  is_finite_inner_chart (@euclidean_hom_inner_product R (1+d) (1+d)) a t ->
  let H:=inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d)) in
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))) in
  let S:=[set z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
    spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2] in
  let w:=fun z:P=>alpha (z.1 c)*beta (z.2 c) in
  (@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) S=0%E ->
    is_measure_subset_integral (@hausdorff_measure R H ((d*(d-1)%/2)+d))
      [set g|is_orthogonal_map (@euclidean_inner_product R (1+d))
        (@euclidean_inner_product R (1+d)) (hom_as_linear g)]
      (parameterized_integral (@hausdorff_measure R P ((k+m-d)+d*(d-1)%/2))
        (fun g=>partial_function_zero_extension (0:extended_real_line R)
          [set z|S z /\orthogonal_kinematic_map z=g] (real_total_integrand w))) 0%E.
Proof.
move=>hDim hc hA hB hRA hMA hRB hMB hAlpha hBeta hChart hTargetChart H P S w hNull.
pose V:=Hom (R_n R (1+d)) (R_n R (1+d)).
pose hH:=@euclidean_hom_inner_productP R (1+d) (1+d).
pose hP:=product_inner_productP hH hH.
pose O:=[set g:V|is_orthogonal_map (@euclidean_inner_product R (1+d))
  (@euclidean_inner_product R (1+d)) (hom_as_linear g)].
have hSource:=@spherical_kinematic_source R d k m c A B hc hA hB hRA hMA hRB hMB.
have hTarget:=@orthogonal_group_measure_rectifiable R (1+d)%N.
have hNu:=euclidean_skew_dimension_successor d.
change ((1+d)*((1+d)-1)%/2=(d*(d-1)%/2)+d)%N in hNu.
rewrite hNu in hTarget.
have hLip:@is_metric_lipschitz R P H S (@orthogonal_kinematic_map R (1+d)).
  have [L [hPositive hBound]]:=@orthogonal_kinematic_lipschitz R (1+d)%N.
  exists L; split; first exact hPositive.
  apply:(metric_lipschitz_bound_restrict _ hBound).
  move=>z [hx hy]; exact (conj hx.1 hy.1).
have hRange z:S z ->O (orthogonal_kinematic_map z).
  move=>[hx hy] u v0.
  change (euclidean_inner_product (z.1 (euclidean_rectangular_adjoint z.2 u))
    (z.1 (euclidean_rectangular_adjoint z.2 v0))=euclidean_inner_product u v0).
  by rewrite hx.1 (euclidean_orthogonal_adjoint_orthogonal hy.1).
have ht:is_orthogonal_map (@euclidean_hom_inner_product R (1+d) (1+d))
    (@euclidean_inner_product R v) (hom_as_linear t).
  exact (finite_inner_chart_inverse_product hTargetChart).
pose H0:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n))
  ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)).
have hNullC:H0 (p @` S)=0%E.
  have hEq:=@finite_inner_chart_inverse_hausdorff R [the lmodType R of (V*V)%type]
    _ hP n e p hChart ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N S.
  exact (eq_trans hEq hNull).
have hJac:measure_almost_everywhere_on H0 (p @` S) [set x|partial_function_graph
    (MeasureApproximateJacobian.measure_approximate_jacobian (measure_restrict H0 (p @` S))
      ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N ((d*(d-1)%/2)+d)%N
      (partial_function_source_restrict (p @` S)
        (partial_function_total (fun u=>t (orthogonal_kinematic_map (e u)))))) x 0%R].
  apply:(@measure_null_subset R (inner_metric_space (@euclidean_inner_productP R n)) H0
    (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n))
      ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) _ (p @` S) _ hNullC).
  by move=>x [hx _].
have hWeight:=@spherical_kinematic_source_weight_integral R d k m c A B alpha beta av bv
  hc hA hB hRA hMA hRB hMB hAlpha hBeta.
have hTargetDim:(((d*(d-1)%/2)+d)<=((k+d*(d-1)%/2)+(m+d*(d-1)%/2)))%N.
  rewrite -hNu; exact (orthogonal_kinematic_target_dimension_bound hDim).
have hResult:=@finite_inner_weighted_coarea_profile R [the lmodType R of (V*V)%type] V
  _ _ hP hH n v ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N ((d*(d-1)%/2)+d)%N
  e p a t S O (@orthogonal_kinematic_map R (1+d)) w
  (fun _=>0%R) hChart hTargetChart hTargetDim
  hSource.1 hSource.2 hTarget.1 hTarget.2 hLip hRange (ex_intro _ _ hWeight) hJac.
have hFibre:(((k+d*(d-1)%/2)+(m+d*(d-1)%/2))-((d*(d-1)%/2)+d)=
    (k+m-d)+d*(d-1)%/2)%N.
  rewrite -hNu; exact (orthogonal_kinematic_fibre_dimension hDim).
rewrite hFibre in hResult.
have [q [hSourceIntegral hTargetIntegral]]:=hResult.
pose rho:=measure_restrict (@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) S.
have hr:=measure_restrict_is_measure (@hausdorff_measure_is_measure R P
  ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) S.
have hWholeNull:rho setT=0%E by rewrite /rho /measure_restrict setIT.
have hZero:=@null_whole_measure_integral R P rho hr (real_total_integrand (fun z=>w z*0%R)) hWholeNull.
have hValue:=measure_integral_unique hSourceIntegral hZero.
by rewrite hValue in hTargetIntegral.
Qed.
