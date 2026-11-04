(** Federer (1969), 3.2.48, p. 284: the complete
    almost-everywhere finite rectifiability assertion for the original
    intersections A intersect g(B). Coarea, the actual whole-fibre
    graph and 3.2.47(3) discharge all intermediate hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates CoordinateProjection
  EuclideanInnerProduct InnerNorm InnerMetric EuclideanHomInnerCharts OrthogonalMaps
  OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures LinearGroupTopology
  LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  OrthogonalHausdorffHaarAlmost OrthogonalKinematicCoareaFibres
  OrthogonalKinematicFibreProjection OrthogonalKinematicFibreMeasurability SphericalOrthogonalConverseRectifiability
  SphericalKinematicIntegral UnitSphereSpace SphericalProductPreimageImage
  RectifiableSetUP HausdorffMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_intersection_rectifiable]: the
    first conclusion of 3.2.48, p. 284: A intersect
    g(B) is finitely H^lambda rectifiable for theta_(d+1)
    almost every original g. The printed source hypotheses,
    all natural k,m with d<=k+m and positive ambient
    dimensions remain. No k,m<=d, source Borelness,
    transversality or finite individual fibre premise is added. *)
Theorem spherical_kinematic_intersection_rectifiable (R:realType) d k m
    (c:R_n R d.+1) (A B:set (R_n R d.+1))
    (mulS:euclidean_orthogonal_group R d.+1->euclidean_orthogonal_group R d.+1->euclidean_orthogonal_group R d.+1)
    (invS:euclidean_orthogonal_group R d.+1->euclidean_orthogonal_group R d.+1)
    (eS:euclidean_orthogonal_group R d.+1)
    (theta:set (euclidean_orthogonal_group R d.+1)->\bar R):
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R d.+1) (@coordinate_basisP R d.+1))
    (linear_group_inv (@euclidean_inner_productP R d.+1) (@coordinate_basisP R d.+1))
    (linear_group_unit (@euclidean_inner_productP R d.+1) (@coordinate_basisP R d.+1))
    (euclidean_orthogonal_group R d.+1) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  (d<=k+m)%N ->inner_norm (@euclidean_inner_productP R d.+1) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R d.+1 ->B `<=` @euclidean_unit_sphere_set R d.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R d.+1)) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) m) B ->
  measure_almost_everywhere theta [set g|
    is_measure_m_rectifiable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R d.+1)) (k+m-d)) (k+m-d)%N
        (spherical_kinematic_intersection A B g)].
Proof.
move=>hS hTheta hDim hc hA hB hRA hMA hRB hMB.
pose H:=inner_metric_space (@euclidean_hom_inner_productP R d.+1 d.+1).
pose P:set (Hom (R_n R d.+1) (R_n R d.+1)):=
  [set g|is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) (k+m-d)) (k+m-d)%N
      (A `&` (g @` B))].
apply:(@orthogonal_hausdorff_to_haar_almost R d.+1 mulS invS eS theta P hS hTheta).
have hCore:=@orthogonal_kinematic_coarea_fibres R d k m c A B hDim hc hA hB hRA hMA hRB hMB.
apply:(@measure_null_subset R H (@hausdorff_measure R H (d.+1*(d.+1-1)%/2)%N)
  (@hausdorff_measure_is_measure R H (d.+1*(d.+1-1)%/2)%N) _ _ _ hCore).
move=>g [hg hBad]; split; first exact hg.
move=>hGood; apply:hBad.
have hPre:=@orthogonal_kinematic_fibre_projection_rectifiable R d.+1
  ((k+m-d)+d*(d-1)%/2)%N c A B g hg hGood.1.
apply:(@spherical_orthogonal_converse_rectifiability R d c (A `&` (g @` B)) (k+m-d)%N
  hc _ hPre).
move=>x hx; exact (hA x hx.1).
Qed.


(** Source for [spherical_kinematic_intersection_measurable]: supporting
    completed measurability of the original intersections in
    the signed formula of 3.2.48, p. 284. This
    conclusion is derived almost everywhere from the actual
    coarea fibre, rather than assumed for the inner integral. *)
Theorem spherical_kinematic_intersection_measurable (R:realType) d k m
    (c:R_n R d.+1) (A B:set (R_n R d.+1))
    (mulS:euclidean_orthogonal_group R d.+1->euclidean_orthogonal_group R d.+1->euclidean_orthogonal_group R d.+1)
    (invS:euclidean_orthogonal_group R d.+1->euclidean_orthogonal_group R d.+1)
    (eS:euclidean_orthogonal_group R d.+1)
    (theta:set (euclidean_orthogonal_group R d.+1)->\bar R):
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R d.+1) (@coordinate_basisP R d.+1))
    (linear_group_inv (@euclidean_inner_productP R d.+1) (@coordinate_basisP R d.+1))
    (linear_group_unit (@euclidean_inner_productP R d.+1) (@coordinate_basisP R d.+1))
    (euclidean_orthogonal_group R d.+1) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  (d<=k+m)%N ->inner_norm (@euclidean_inner_productP R d.+1) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R d.+1 ->B `<=` @euclidean_unit_sphere_set R d.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R d.+1)) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) m) B ->
  measure_almost_everywhere theta [set g|
    measure_measurable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R d.+1)) (k+m-d))
        (spherical_kinematic_intersection A B g)].
Proof.
move=>hS hTheta hDim hc hA hB hRA hMA hRB hMB.
pose H:=inner_metric_space (@euclidean_hom_inner_productP R d.+1 d.+1).
pose P:set (Hom (R_n R d.+1) (R_n R d.+1)):=
  [set g|measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) (k+m-d)) (A `&` (g @` B))].
apply:(@orthogonal_hausdorff_to_haar_almost R d.+1 mulS invS eS theta P hS hTheta).
have hCore:=@orthogonal_kinematic_coarea_fibres R d k m c A B hDim hc hA hB hRA hMA hRB hMB.
apply:(@measure_null_subset R H (@hausdorff_measure R H (d.+1*(d.+1-1)%/2)%N)
  (@hausdorff_measure_is_measure R H (d.+1*(d.+1-1)%/2)%N) _ _ _ hCore).
move=>g [hg hBad]; split; first exact hg.
move=>hGood; apply:hBad.
exact (@orthogonal_kinematic_intersection_measurable R d (k+m-d)%N c A B g
  hc hA hg hGood.1 hGood.2).
Qed.
