(** Federer (1969), 3.2.48, p. 284: both signed
    fibre-integral changes. The actual graph similarity contributes
    sqrt(2)^(lambda+mu), and Phi contributes its proved
    sqrt(2)^lambda isotropy-volume factor. Original intersections,
    signed weights and exact integral definedness are preserved. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts OrthogonalMaps EuclideanRectangularAdjoint ProductInner UnitSphereSpace
  SphericalProductPreimageImage OrthogonalKinematicMap OrthogonalKinematicFibreScale
  OrthogonalKinematicFibreProjection OrthogonalKinematicFibreMeasurability
  SphericalOrthogonalConverseRectifiability SphericalWeightedPreimageTransport
  SphericalPullbackPushforward HausdorffSimilarityRestriction RectifiableSetUP
  HausdorffMeasure MeasureUP MeasureRestriction MeasureIntegralUP MeasureSubsetIntegral
  RestrictedIntegralIdentity PartialFunctionUP PartialFunctionPrecomposition
  SummableRealFunctionUP MeasureIntegralGraphEquivalence ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_fibre_integral]: the two
    displayed fibre-integral equalities in 3.2.48, p. 284.
    Whole-fibre rectifiability and completed measurability are
    the conclusions discharged almost everywhere by coarea.
    Every signed partial-integral value, including infinity,
    retains its exact definedness in both directions. *)
Theorem spherical_kinematic_fibre_integral (R:realType) d r
    (c:R_n R d.+1) (A B:set (R_n R d.+1))
    (g:Hom (R_n R d.+1) (R_n R d.+1)) (alpha beta:R_n R d.+1->R) a:
  inner_norm (@euclidean_inner_productP R d.+1) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R d.+1 ->
  is_orthogonal_map (@euclidean_inner_product R d.+1)
    (@euclidean_inner_product R d.+1) (hom_as_linear g) ->
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R d.+1 d.+1) (@euclidean_hom_inner_productP R d.+1 d.+1)) in
  let fibre:=[set z:Hom (R_n R d.+1) (R_n R d.+1)*Hom (R_n R d.+1) (R_n R d.+1)|
    (spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2) /\
    orthogonal_kinematic_map z=g] in
  is_measure_m_rectifiable (@hausdorff_measure R P (r+d*(d-1)%/2)) (r+d*(d-1)%/2)%N fibre ->
  measure_measurable (@hausdorff_measure R P (r+d*(d-1)%/2)) fibre ->
  (is_measure_subset_integral (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) r)
    (A `&` (g @` B)) (real_total_integrand (fun x=>alpha x*beta (euclidean_rectangular_adjoint g x))) a <->
  is_measure_subset_integral (@hausdorff_measure R P (r+d*(d-1)%/2)) fibre
    (real_total_integrand (fun z:P=>alpha (z.1 c)*beta (z.2 c)))
    ((((Num.sqrt (2:R))^+(r+d*(d-1)%/2)*spherical_preimage_mass_scale R d r)%:E)*a)%E).
Proof.
move=>hc hA hg P fibre hFRect hFMeas.
pose X:=inner_metric_space (@euclidean_inner_productP R d.+1).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R d.+1 d.+1).
pose E:=A `&` (g @` B).
pose S:=spherical_orthogonal_preimage c E.
pose F:=fun x:Y=>((x,hom_comp (euclidean_rectangular_adjoint g) x):P).
pose Phi:=fun x:Y=>x c.
pose u:=real_total_integrand (fun x=>alpha x*beta (euclidean_rectangular_adjoint g x)).
pose w:=real_total_integrand (fun z:P=>alpha (z.1 c)*beta (z.2 c)).
pose C:=spherical_preimage_mass_scale R d r.
pose D:=(Num.sqrt (2:R))^+(r+d*(d-1)%/2).
pose H:=@hausdorff_measure R Y (r+d*(d-1)%/2)%N.
pose K:=@hausdorff_measure R P (r+d*(d-1)%/2)%N.
pose betaE:=@hausdorff_measure R X r.
have hPreRect:=@orthogonal_kinematic_fibre_projection_rectifiable R d.+1
  (r+d*(d-1)%/2)%N c A B g hg hFRect.
have hSphere:E `<=` @euclidean_unit_sphere_set R d.+1 by move=>x hx; exact (hA x hx.1).
have hERect:=@spherical_orthogonal_converse_rectifiability R d c E r hc hSphere hPreRect.
have hEMeas:=@orthogonal_kinematic_intersection_measurable R d r c A B g hc hA hg hFRect hFMeas.
have hPreMeas:=@orthogonal_kinematic_preimage_measurable R d.+1 (r+d*(d-1)%/2)%N c A B g hg hFMeas.
have hLeft:cancel F fst by move=>x.
have hRoot:0<Num.sqrt (2:R) by rewrite sqrtr_gt0 ltr0n.
have hDistance x y:@mdist R P (F x) (F y)=Num.sqrt (2:R)*@mdist R Y x y.
  rewrite !inner_metric_distanceE; exact (@orthogonal_kinematic_fibre_distance R d.+1 g x y hg).
have hGraph:fibre=F @` S:=@orthogonal_kinematic_fibre_graph_normalized R d.+1 c A B g hg.
have hWeight x z:partial_function_graph (partial_function_precompose Phi u) x z <->
    partial_function_graph (partial_function_precompose F w) x z.
  rewrite /partial_function_precompose !real_total_integrand_graph.
  by [].
have hScale:(D%:E*(C%:E*a)=(D*C)%:E*a)%E by rewrite muleA -EFinM.
have hSourceIff:=@restricted_integral_zero_extension_iff R X betaE
  (@hausdorff_measure_is_measure R X r) E u a hEMeas.
have hTargetIff:=@restricted_integral_zero_extension_iff R P K
  (@hausdorff_measure_is_measure R P (r+d*(d-1)%/2)%N) fibre w ((D*C)%:E*a)%E hFMeas.
split.
- move=>hI.
  have hRestricted:=hSourceIff.2 hI.
  have hLifted:=(@spherical_weighted_pullback_from_preimage_iff R d r c E u a
    hc hSphere hERect hPreMeas).1 hRestricted.
  have hWeightLifted:=measure_integral_graph_equivalent hWeight hLifted.
  have hSimilar:=(@hausdorff_similarity_subset_integral_iff R Y P F fst (Num.sqrt (2:R))
    hRoot hLeft hDistance (r+d*(d-1)%/2)%N S w (C%:E*a)%E).1 hWeightLifted.
  rewrite -hGraph hScale in hSimilar; exact (hTargetIff.1 hSimilar).
- move=>hI.
  have hRestricted:=hTargetIff.2 hI.
  rewrite hGraph -hScale in hRestricted.
  have hSimilar:=(@hausdorff_similarity_subset_integral_iff R Y P F fst (Num.sqrt (2:R))
    hRoot hLeft hDistance (r+d*(d-1)%/2)%N S w (C%:E*a)%E).2 hRestricted.
  have hWeightRestored:=measure_integral_graph_equivalent (fun x z=>iff_sym (hWeight x z)) hSimilar.
  have hRestored:=(@spherical_weighted_pullback_from_preimage_iff R d r c E u a
    hc hSphere hERect hPreMeas).2 hWeightRestored.
  exact (hSourceIff.1 hRestored).
Qed.
