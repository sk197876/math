(** Federer (1969), 3.2.48, pp. 285–286: restore the actual
    approximate Jacobian on completed measurable source subsets of the
    original manifold product. Local coordinate existence and the actual
    differential discharge every manifold and Jacobian obligation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerMetric EuclideanHomInnerCharts HilbertFormCompactness ProductInner OrthogonalMaps
  FiniteInnerChartUP FiniteInnerSubmanifoldCoordinates FiniteInnerCoordinatesSubmanifold
  FiniteInnerCartesianSubmanifold FiniteInnerRectifiableCoordinates FiniteInnerChartMeasureTransport
  EuclideanSubmanifoldUP UnitSphereSpace SphericalProductPreimageImage
  SphericalOrthogonalPreimageSubmanifold OrthogonalKinematicMap
  OrthogonalKinematicCoordinateDifferential SphericalKinematicTangentProfile
  SubmanifoldSubsetIntrinsicJacobian EuclideanTangentExteriorNorm
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction MeasureApproximateJacobian
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure RectifiableSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_approximate_profile]: the
    replacement of approximate tangents by actual manifold tangents in
    3.2.48, p. 285. The exact approximate Jacobian on the original
    completed measurable source is restored almost everywhere. No
    independent Jacobian or derivative-field measurability is assumed. *)
Theorem spherical_kinematic_approximate_profile (R:realType) d k m n v
    (c:R_n R (1+d)) (M N:set (R_n R (1+d)))
    (e:Hom (R_n R n) [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type])
    (p:Hom [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type] (R_n R n))
    (t:Hom (Hom (R_n R (1+d)) (R_n R (1+d))) (R_n R v))
    (W:set (Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d)))):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  @is_euclidean_submanifold R (1+d)%N k 1%N M ->@is_euclidean_submanifold R (1+d)%N m 1%N N ->
  M `<=` @euclidean_unit_sphere_set R (1+d) ->N `<=` @euclidean_unit_sphere_set R (1+d) ->
  is_finite_inner_chart (product_inner (@euclidean_hom_inner_productP R (1+d) (1+d))
    (@euclidean_hom_inner_productP R (1+d) (1+d))) e p ->
  is_orthogonal_map (@euclidean_hom_inner_product R (1+d) (1+d))
    (@euclidean_inner_product R v) (hom_as_linear t) ->
  W `<=` [set z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
    spherical_orthogonal_preimage c M z.1 /\spherical_orthogonal_preimage c N z.2] ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (product_inner_productP
      (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))))
    ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (product_inner_productP
      (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))))
    ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) W ->
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n))
    ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)) in
  measure_almost_everywhere_on H (p @` W) [set z|partial_function_graph
    (measure_approximate_jacobian (measure_restrict H (p @` W))
      ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N ((d*(d-1)%/2)+d)%N
      (partial_function_source_restrict (p @` W)
        (partial_function_total (fun u=>t (orthogonal_kinematic_map (e u)))))) z
    (spherical_kinematic_tangent_profile c M N e p t (e z))].
Proof.
move=>hc hM hN hMS hNS hChart ht hWSubset hRW hMW H.
pose X:=Hom (R_n R (1+d)) (R_n R (1+d)).
pose hX:=@euclidean_hom_inner_productP R (1+d) (1+d).
pose hP:=product_inner_productP hX hX.
pose source:=[set z:X*X|spherical_orthogonal_preimage c M z.1 /\spherical_orthogonal_preimage c N z.2].
have hPM:=@spherical_orthogonal_preimage_submanifold R d k 1%N c M hc (leqnn 1) hM hMS.
have hPN:=@spherical_orthogonal_preimage_submanifold R d m 1%N c N hc (leqnn 1) hN hNS.
have hProduct:=@finite_inner_cartesian_submanifold R X X _ _ hX hX
  (k+d*(d-1)%/2)%N (m+d*(d-1)%/2)%N 1%N (spherical_orthogonal_preimage c M)
  (spherical_orthogonal_preimage c N) (leqnn 1) hPM hPN.
have hCoordMan:=@finite_inner_coordinates_euclidean_submanifold R [the lmodType R of (X*X)%type]
  _ hP n e p ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N 1%N source (leqnn 1) hChart
  (fun a ha=>@finite_inner_submanifold_coordinates R [the lmodType R of (X*X)%type]
    _ hP ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N 1%N source a hProduct ha).
have hSub:p @` W `<=` p @` source.
  move=>z [a ha <-]; exists a; first exact (hWSubset a ha); reflexivity.
have hRC:=@finite_inner_chart_measure_rectifiable_coordinates R [the lmodType R of (X*X)%type]
  _ hP n e p ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N W hChart hRW.
have hMC:=@finite_inner_chart_coordinates_measurable R [the lmodType R of (X*X)%type]
  _ hP n e p ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N W hChart hMW.
have hAlmost:=@submanifold_subset_intrinsic_jacobian_almost R n v
  ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N ((d*(d-1)%/2)+d)%N (p @` source) (p @` W)
  (fun u=>t (orthogonal_kinematic_map (e u))) (orthogonal_kinematic_coordinate_differential e t)
  hCoordMan hSub hRC hMC (fun a _=>orthogonal_kinematic_coordinate_differential_actual hChart ht a).
apply:(measure_null_subset (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) _ hAlmost).
move=>z [hz hNot]; split; first exact hz.
move=>hGraph; apply:hNot.
change (partial_function_graph
  (measure_approximate_jacobian (measure_restrict H (p @` W))
    ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N ((d*(d-1)%/2)+d)%N
    (partial_function_source_restrict (p @` W)
      (partial_function_total (fun u=>t (orthogonal_kinematic_map (e u)))))) z
  (spherical_kinematic_tangent_profile c M N e p t (e z))).
rewrite /spherical_kinematic_tangent_profile (finite_inner_chart_left_inverse hChart).
exact hGraph.
Qed.
