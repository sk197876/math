(** Federer (1969), 3.2.48, pp. 285–286: restore the actual
    approximate Jacobian on completed measurable source subsets of the
    original manifold product. Local coordinate existence and the actual
    differential discharge every manifold and Jacobian obligation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerMetric EuclideanHomInnerCharts HilbertFormCompactness ProductInner OrthogonalMaps
  FiniteInnerChartUP FiniteInnerSubmanifoldCoordinates FiniteInnerCoordinatesSubmanifold
  FiniteInnerCartesianSubmanifold FiniteInnerRectifiableCoordinates FiniteInnerChartMeasureTransport
  EuclideanSubmanifoldUP UnitSphereSpace SphericalProductPreimageImage
  SphericalOrthogonalPreimageSubmanifold OrthogonalKinematicMap
  OrthogonalKinematicCoordinateDifferential SphericalKinematicTangentProfile
  SubmanifoldSubsetIntrinsicJacobian EuclideanTangentExteriorNorm
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction MeasureApproximateJacobian
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure RectifiableSetUP
  SphericalKinematicSource SphericalKinematicMeasurablePiece SphericalKinematicCoverAlmost
  SphericalRectifiablePartition DisjointFamilySelector SphericalKinematicPartitionProfile
  SphericalKinematicApproximateProfile CountableDifferentiableJacobianProfile
  FiniteInnerChartMeasureTransport FiniteInnerChartCompact MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_partition_approximate]: the
    original approximate Jacobian in 3.2.48, p. 284, equals the
    countably assembled actual manifold profile of pp. 285–286
    almost everywhere. The manifold cover, original completed source,
    genuine second factor and actual polynomial differential discharge
    every local-to-global obligation. No orientation field is selected. *)
Theorem spherical_kinematic_partition_approximate (R:realType) d k m n v
    (c:R_n R (1+d)) (A B:set (R_n R (1+d)))
    (C D:set (set (R_n R (1+d)))) (M N:set (R_n R (1+d))->set (R_n R (1+d)))
    (sA sB:R_n R (1+d)->set (R_n R (1+d)))
    (e:Hom (R_n R n) [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type])
    (p:Hom [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type] (R_n R n))
    (t:Hom (Hom (R_n R (1+d)) (R_n R (1+d))) (R_n R v)):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R (1+d) ->B `<=` @euclidean_unit_sphere_set R (1+d) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (1+d))) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) m) B ->
  is_spherical_rectifiable_partition k A C M ->is_spherical_rectifiable_partition m B D N ->
  is_disjoint_family_selector C sA ->is_disjoint_family_selector D sB ->
  is_finite_inner_chart (product_inner (@euclidean_hom_inner_productP R (1+d) (1+d))
    (@euclidean_hom_inner_productP R (1+d) (1+d))) e p ->
  is_orthogonal_map (@euclidean_hom_inner_product R (1+d) (1+d))
    (@euclidean_inner_product R v) (hom_as_linear t) ->
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))) in
  let W:=[set z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
    spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2] in
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n))
    ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)) in
  measure_almost_everywhere_on H (p @` W) [set z|partial_function_graph
    (measure_approximate_jacobian (measure_restrict H (p @` W))
      ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N ((d*(d-1)%/2)+d)%N
      (partial_function_source_restrict (p @` W)
        (partial_function_total (fun u=>t (orthogonal_kinematic_map (e u)))))) z
    (spherical_kinematic_partition_profile c M N sA sB e p t (e z))].
Proof.
move=>hc hA hB hRA hMA hRB hMB hC hD hSelectA hSelectB hChart ht P W H.
pose V:=Hom (R_n R (1+d)) (R_n R (1+d)).
pose hP:=product_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d))
  (@euclidean_hom_inner_productP R (1+d) (1+d)).
pose degree:=((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N.
pose HP:=@hausdorff_measure R P degree.
pose I:=[the choiceType of (set (R_n R (1+d))*set (R_n R (1+d)))%type].
pose S0:=fun i:I=>[set z:V*V|spherical_orthogonal_preimage c (A `&` i.1) z.1 /\
  spherical_orthogonal_preimage c (B `&` i.2) z.2].
pose S:=fun i:I=>p @` (S0 i).
pose WC:=p @` W.
have hSource:=@spherical_kinematic_source R d k m c A B hc hA hB hRA hMA hRB hMB.
have hWC:=@finite_inner_chart_coordinates_measurable R [the lmodType R of (V*V)%type]
  _ hP n e p degree W hChart hSource.2.
have hFinite:(H WC< +oo)%E.
  have hEqual:=@finite_inner_chart_inverse_hausdorff R [the lmodType R of (V*V)%type]
    _ hP n e p hChart degree W.
  change (H WC=HP W) in hEqual.
  rewrite hEqual; exact hSource.1.2.
have hPieces i:(C `*` D) i ->is_measure_m_rectifiable HP degree (S0 i) /\measure_measurable HP (S0 i).
  move=>[hi hj].
  exact (@spherical_kinematic_measurable_piece R d k m c A B i.1 i.2 hc hA hB hRA hMA hRB hMB
    (spherical_partition_borel hC hi) (spherical_partition_borel hD hj)).
have hSM i:(C `*` D) i ->measure_measurable H (S i).
  move=>hi; exact (@finite_inner_chart_coordinates_measurable R [the lmodType R of (V*V)%type]
    _ hP n e p degree (S0 i) hChart (hPieces i hi).2).
have hSW i:S0 i `<=` W.
  move=>z [hx hy]; split; [split; first exact hx.1|split; first exact hy.1];
    [exact hx.2.1|exact hy.2.1].
have hSWC i:(C `*` D) i ->S i `<=` WC.
  move=>hi z [x hx <-]; exists x; first exact (hSW i x hx); reflexivity.
have hLoss:=@spherical_kinematic_cover_almost R d k m c A B C D hc hA hB hRA hMA hRB hMB
  (spherical_partition_almost hC) (spherical_partition_almost hD).
have hLossC:H (WC `\` \bigcup_(i in C `*` D) S i)=0%E.
  change (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) degree
    (WC `\` \bigcup_(i in C `*` D) S i)=0)%E.
  rewrite -(@finite_inner_chart_hausdorff_pushforward R [the lmodType R of (V*V)%type]
    _ hP n e p degree hChart).
  apply:(measure_null_subset (@hausdorff_measure_is_measure R P degree) _ hLoss).
  move=>x [[y hy hSame] hNot].
  have hEqual:y=x:=(can_inj (finite_inner_chart_right_inverse hChart)) _ _ hSame.
  split; first by rewrite -hEqual.
  move=>[i hi hx]; apply hNot; exists i; first exact hi.
  exists x; first exact hx; reflexivity.
have hJac i:(C `*` D) i ->measure_almost_everywhere_on H (S i) [set x|partial_function_graph
    (measure_approximate_jacobian (measure_restrict H (S i)) degree ((d*(d-1)%/2)+d)%N
      (partial_function_source_restrict (S i)
        (partial_function_total (fun u=>t (orthogonal_kinematic_map (e u)))))) x
    (spherical_kinematic_tangent_profile c (M i.1) (N i.2) e p t (e x))].
  move=>[hi hj].
  have hSubset:S0 i `<=` [set z:V*V|spherical_orthogonal_preimage c (M i.1) z.1 /\
      spherical_orthogonal_preimage c (N i.2) z.2].
    move=>z [hx hy]; split.
    - split; first exact hx.1; exact (spherical_partition_subordinate hC hi hx.2.2).
    - split; first exact hy.1; exact (spherical_partition_subordinate hD hj hy.2.2).
  exact (@spherical_kinematic_approximate_profile R d k m n v c (M i.1) (N i.2) e p t (S0 i)
    hc (spherical_partition_manifold hC hi) (spherical_partition_manifold hD hj)
    (spherical_partition_inside hC hi) (spherical_partition_inside hD hj) hChart ht hSubset
    (hPieces i (conj hi hj)).1 (hPieces i (conj hi hj)).2).
apply:(@countable_differentiable_jacobian_profile R degree n v ((d*(d-1)%/2)+d)%N I
  (C `*` D) WC S (fun u=>t (orthogonal_kinematic_map (e u)))
  (fun i x=>spherical_kinematic_tangent_profile c (M i.1) (N i.2) e p t (e x))
  (fun x=>spherical_kinematic_partition_profile c M N sA sB e p t (e x))
  (countableX (spherical_partition_countable hC) (spherical_partition_countable hD))
  hWC hFinite hSM hSWC hLossC _ _ hJac).
- move=>x hx; exists (orthogonal_kinematic_coordinate_differential e t x).
  exact (orthogonal_kinematic_coordinate_differential_actual hChart ht x).
- move=>i [hi hj] x [z hz <-].
  rewrite (finite_inner_chart_right_inverse hChart).
  exact (@spherical_kinematic_partition_profile_on R d n v c M N C D sA sB e p t z i.1 i.2
    hSelectA hSelectB hi hj hz.1.2.2 hz.2.2.2).
Qed.
