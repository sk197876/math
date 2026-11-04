(** Federer (1969), 3.2.48, pp. 284–286: signed coarea
    on the entire original source, using the proved countable manifold
    profile. All source, target and actual Jacobian premises are discharged. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  EuclideanHomInnerCharts ProductInner OrthogonalMaps EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  FiniteInnerChartUP FiniteInnerWeightedCoareaProfile EuclideanSubmanifoldUP
  UnitSphereSpace SphericalProductPreimageImage SphericalKinematicSource
  OrthogonalKinematicMap OrthogonalKinematicLipschitz OrthogonalKinematicDimensions OrthogonalKinematicCoareaFibres
  SphericalKinematicTangentProfile SphericalKinematicApproximateProfile SphericalKinematicSourceWeights
  SphericalRectifiablePartition DisjointFamilySelector SphericalKinematicPartitionProfile SphericalKinematicPartitionApproximate
  EuclideanStiefelVolumeDimensions LipschitzUP LipschitzBasic RectifiableSetUP HausdorffMeasure
  MeasureUP MeasureRestriction MeasureIntegralUP MeasureSubsetIntegral
  ParameterizedIntegral PartialFunctionUP PartialZeroExtension SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_partition_coarea]: the coarea
    equality in 3.2.48, p. 284, with the actual tangent Jacobian
    computed on pp. 285–286. The proved partition laws
    retain the entire original completed measurable source and signed
    summable weights. No differential, Jacobian, fibre-integrability,
    finite-fibre or independent product-measurability premise is added. *)
Theorem spherical_kinematic_partition_coarea (R:realType) d k m n v
    (c:R_n R (1+d)) (A B:set (R_n R (1+d)))
    (C D:set (set (R_n R (1+d)))) (M N:set (R_n R (1+d))->set (R_n R (1+d)))
    (sA sB:R_n R (1+d)->set (R_n R (1+d)))
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
  is_spherical_rectifiable_partition k A C M ->is_spherical_rectifiable_partition m B D N ->
  is_disjoint_family_selector C sA ->is_disjoint_family_selector D sB ->
  is_finite_inner_chart (product_inner (@euclidean_hom_inner_productP R (1+d) (1+d))
    (@euclidean_hom_inner_productP R (1+d) (1+d))) e p ->
  is_finite_inner_chart (@euclidean_hom_inner_product R (1+d) (1+d)) a t ->
  let H:=inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d)) in
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))) in
  let S:=[set z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
    spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2] in
  let w:=fun z:P=>alpha (z.1 c)*beta (z.2 c) in
  exists q,is_measure_integral (measure_restrict (@hausdorff_measure R P
      ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) S)
      (real_total_integrand (fun z=>w z*spherical_kinematic_partition_profile c M N sA sB e p t z)) q /\
    is_measure_subset_integral (@hausdorff_measure R H ((d*(d-1)%/2)+d))
      [set g|is_orthogonal_map (@euclidean_inner_product R (1+d))
        (@euclidean_inner_product R (1+d)) (hom_as_linear g)]
      (parameterized_integral (@hausdorff_measure R P ((k+m-d)+d*(d-1)%/2))
        (fun g=>partial_function_zero_extension (0:extended_real_line R)
          [set z|S z /\orthogonal_kinematic_map z=g] (real_total_integrand w))) q.
Proof.
move=>hDim hc hA hB hRA hMA hRB hMB hAlpha hBeta hC hD hSelectA hSelectB hChart hTargetChart H P S w.
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
have hJac:=@spherical_kinematic_partition_approximate R d k m n v c A B C D M N sA sB e p t
  hc hA hB hRA hMA hRB hMB hC hD hSelectA hSelectB hChart ht.
have hWeight:=@spherical_kinematic_source_weight_integral R d k m c A B alpha beta av bv
  hc hA hB hRA hMA hRB hMB hAlpha hBeta.
have hTargetDim:(((d*(d-1)%/2)+d)<=((k+d*(d-1)%/2)+(m+d*(d-1)%/2)))%N.
  rewrite -hNu; exact (orthogonal_kinematic_target_dimension_bound hDim).
have hResult:=@finite_inner_weighted_coarea_profile R [the lmodType R of (V*V)%type] V
  _ _ hP hH n v ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N ((d*(d-1)%/2)+d)%N
  e p a t S O (@orthogonal_kinematic_map R (1+d)) w
  (spherical_kinematic_partition_profile c M N sA sB e p t) hChart hTargetChart hTargetDim
  hSource.1 hSource.2 hTarget.1 hTarget.2 hLip hRange (ex_intro _ _ hWeight) hJac.
have hFibre:(((k+d*(d-1)%/2)+(m+d*(d-1)%/2))-((d*(d-1)%/2)+d)=
    (k+m-d)+d*(d-1)%/2)%N.
  rewrite -hNu; exact (orthogonal_kinematic_fibre_dimension hDim).
by rewrite hFibre in hResult.
Qed.
