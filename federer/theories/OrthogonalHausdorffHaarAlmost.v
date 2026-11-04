(** Federer (1969), 3.2.48, p. 284: almost-everywhere
    assertions for ambient Hausdorff measure on O(N) are
    assertions for its normalized Haar measure. The proved
    all-set identity includes arbitrary exceptional subsets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates CoordinateProjection EuclideanInnerProduct
  InnerMetric EuclideanHomInnerCharts OrthogonalMaps OrthogonalGroupHaarMeasure
  EuclideanOrthogonalInvariantMeasures LinearGroupTopology LinearGroupSealed
  IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  OrthogonalHausdorffHaarTransport StiefelGammaVolumeScalar HausdorffMeasure
  MeasureUP MeasureRestriction MeasurePushforward MeasureScaleIntegral MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_hausdorff_to_haar_almost]: supporting
    the change from H^nu almost every g to theta_N
    almost every g in 3.2.48, p. 284. The actual
    positive finite group volume is cancelled through inverse
    measure scaling; no measurability premise is added to P. *)
Lemma orthogonal_hausdorff_to_haar_almost (R:realType) N
    (mulS:euclidean_orthogonal_group R N->euclidean_orthogonal_group R N->euclidean_orthogonal_group R N)
    (invS:euclidean_orthogonal_group R N->euclidean_orthogonal_group R N)
    (eS:euclidean_orthogonal_group R N)
    (theta:set (euclidean_orthogonal_group R N)->\bar R)
    (P:set (Hom (R_n R N) (R_n R N))):
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (linear_group_inv (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (linear_group_unit (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (euclidean_orthogonal_group R N) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R N N)) (N*(N-1)%/2))
    [set g|is_orthogonal_map (@euclidean_inner_product R N)
      (@euclidean_inner_product R N) (hom_as_linear g)] P ->
  measure_almost_everywhere theta [set g|P (orthogonal_element_map g)].
Proof.
move=>hS hTheta hAlmost.
pose H:=inner_metric_space (@euclidean_hom_inner_productP R N N).
pose O:=[set g:Hom (R_n R N) (R_n R N)|is_orthogonal_map
  (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear g)].
pose rho:=measure_restrict (@hausdorff_measure R H (N*(N-1)%/2)%N) O.
pose gamma:=stiefel_gamma_volume_scalar R (leqnn N).
have hGamma:0<gamma:=stiefel_gamma_volume_scalar_positive R (leqnn N).
pose om:=@orthogonal_element_map R (R_n R N) (@euclidean_inner_product R N)
  (@euclidean_inner_productP R N) N (@coordinate_basis R N) (@coordinate_basisP R N).
have hMeasure:=@orthogonal_ambient_hausdorff_haar R N mulS invS eS theta hS hTheta.
have hInverse:measure_scale gamma^-1 rho=measure_pushforward om theta.
  rewrite /rho hMeasure; exact (measure_scale_inverse _ hGamma).
have hNull:rho (~` P)=0%E.
  rewrite /rho /measure_restrict -setDE; exact hAlmost.
have hZero:measure_scale gamma^-1 rho (~` P)=0%E.
  by rewrite /measure_scale hNull mule0.
rewrite hInverse /measure_pushforward preimage_setC in hZero.
exact hZero.
Qed.
