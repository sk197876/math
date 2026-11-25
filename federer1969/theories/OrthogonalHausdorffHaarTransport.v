(** Federer (1969), 3.2.48, p. 284: transport between
    the actual ambient group restriction and normalized Haar
    measure. The identities hold on all sets and for actual
    signed partial integrals, including defined infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets functions constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanHomInnerCharts OrthogonalMaps OrthogonalGroupHaarMeasure
  EuclideanOrthogonalInvariantMeasures LinearGroupTopology LinearGroupSealed IsotropyGroupTopology
  HaarIntegralUP CompactGroupHaarNormalisation OrthogonalGroupHausdorffCarrier
  OrthogonalGroupHausdorffVolume OrthogonalGroupHaarBridge StiefelGammaVolumeScalar
  HausdorffMeasure MeasureUP MeasureRestriction MeasurePushforward MeasureScaleIntegral
  PartialFunctionUP PartialFunctionPrecomposition MeasurableFunctionUP
  MeasureIntegralUP PushforwardMeasurabilityTransfer PushforwardIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_group_hausdorff_pushforward]: the
    actual carrier inclusion pushes group Hausdorff measure
    onto its ambient restriction, supporting 3.2.48, p. 284.
    The identity retains arbitrary group subsets and every degree. *)
Lemma orthogonal_group_hausdorff_pushforward (R:realType) N q:
  measure_pushforward (@orthogonal_element_map R (R_n R N) (@euclidean_inner_product R N)
    (@euclidean_inner_productP R N) N (@coordinate_basis R N) (@coordinate_basisP R N))
    (@orthogonal_group_hausdorff_measure R N q)=
  measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R N N)) q)
    [set g:Hom (R_n R N) (R_n R N)|is_orthogonal_map (@euclidean_inner_product R N)
      (@euclidean_inner_product R N) (hom_as_linear g)].
Proof.
apply:funext=>A; rewrite /measure_pushforward /orthogonal_group_hausdorff_measure /measure_restrict.
congr (@hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R N N)) q).
apply/seteqP; split=>g.
- move=>[h hA <-]; exact (conj (orthogonal_element_orthogonal h) hA).
- move=>[hg hA].
  pose h:=orthogonal_element_of (@euclidean_inner_productP R N) (@coordinate_basisP R N) hg.
  have hValue:orthogonal_element_map h=g.
    by apply:hom_ext=>x; rewrite orthogonal_element_ofE.
  exists h; last exact hValue.
  by change (A (orthogonal_element_map h)); rewrite hValue.
Qed.

(** Source for [orthogonal_ambient_hausdorff_haar]: the
    exact all-set normalization of ambient H^nu restricted
    to O(N), 3.2.48, p. 284. Its scalar is
    the already proved positive finite original group volume. *)
Theorem orthogonal_ambient_hausdorff_haar (R:realType) N
    (mulS:euclidean_orthogonal_group R N->euclidean_orthogonal_group R N->euclidean_orthogonal_group R N)
    (invS:euclidean_orthogonal_group R N->euclidean_orthogonal_group R N)
    (eS:euclidean_orthogonal_group R N)
    (theta:set (euclidean_orthogonal_group R N)->\bar R):
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (linear_group_inv (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (linear_group_unit (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (euclidean_orthogonal_group R N) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R N N)) (N*(N-1)%/2)%N)
    [set g:Hom (R_n R N) (R_n R N)|is_orthogonal_map (@euclidean_inner_product R N)
      (@euclidean_inner_product R N) (hom_as_linear g)]=
  measure_scale (stiefel_gamma_volume_scalar R (leqnn N))
    (measure_pushforward (@orthogonal_element_map R (R_n R N) (@euclidean_inner_product R N)
      (@euclidean_inner_productP R N) N (@coordinate_basis R N) (@coordinate_basisP R N)) theta).
Proof.
move=>hS hTheta.
have h:=congr1 (fun mu=>measure_pushforward
  (@orthogonal_element_map R (R_n R N) (@euclidean_inner_product R N)
    (@euclidean_inner_productP R N) N (@coordinate_basis R N) (@coordinate_basisP R N)) mu)
  (@orthogonal_group_hausdorff_haar R N mulS invS eS theta hS hTheta).
rewrite orthogonal_group_hausdorff_pushforward in h; exact h.
Qed.

(** Source for [orthogonal_hausdorff_to_haar_integral]: the
    actual signed outer-integral change in 3.2.48, p. 284.
    Injectivity of the original carrier inclusion proves composition
    measurability; no independent measurability or integrability hypothesis
    is imposed on the composition. *)
Theorem orthogonal_hausdorff_to_haar_integral (R:realType) N
    (mulS:euclidean_orthogonal_group R N->euclidean_orthogonal_group R N->euclidean_orthogonal_group R N)
    (invS:euclidean_orthogonal_group R N->euclidean_orthogonal_group R N)
    (eS:euclidean_orthogonal_group R N)
    (theta:set (euclidean_orthogonal_group R N)->\bar R)
    (f:partial_function (Hom (R_n R N) (R_n R N)) (extended_real_line R)) a:
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (linear_group_inv (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (linear_group_unit (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (euclidean_orthogonal_group R N) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R N N)) (N*(N-1)%/2)%N)
    [set g:Hom (R_n R N) (R_n R N)|is_orthogonal_map (@euclidean_inner_product R N)
      (@euclidean_inner_product R N) (hom_as_linear g)]) f a ->
  is_measure_integral theta (partial_function_precompose
    (@orthogonal_element_map R (R_n R N) (@euclidean_inner_product R N)
      (@euclidean_inner_productP R N) N (@coordinate_basis R N) (@coordinate_basisP R N)) f)
    (((stiefel_gamma_volume_scalar R (leqnn N))^-1)%:E*a)%E.
Proof.
move=>hS hTheta hI.
pose H:=inner_metric_space (@euclidean_hom_inner_productP R N N).
pose O:=euclidean_orthogonal_group R N.
pose om:=@orthogonal_element_map R (R_n R N) (@euclidean_inner_product R N)
  (@euclidean_inner_productP R N) N (@coordinate_basis R N) (@coordinate_basisP R N).
pose rho:=measure_restrict (@hausdorff_measure R H (N*(N-1)%/2)%N)
  [set g|is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g)].
pose gamma:=stiefel_gamma_volume_scalar R (leqnn N).
have hGamma:0<gamma:=stiefel_gamma_volume_scalar_positive R (leqnn N).
have hGammaInv:0<gamma^-1 by rewrite invr_gt0.
have hRho:=measure_restrict_is_measure (@hausdorff_measure_is_measure R H (N*(N-1)%/2)%N)
  [set g|is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g)].
have hMeasure:=@orthogonal_ambient_hausdorff_haar R N mulS invS eS theta hS hTheta.
have hInverse:measure_scale gamma^-1 rho=measure_pushforward om theta.
  rewrite /rho hMeasure; exact (measure_scale_inverse _ hGamma).
have hScaled:=@measure_scale_integral R H rho hRho gamma^-1 hGammaInv f a hI.
rewrite hInverse in hScaled.
have hInjective:injective om.
  move=>g h hEqual; apply:orthogonal_element_ext=>x.
  exact (congr1 (fun L:Hom (R_n R N) (R_n R N)=>L x) hEqual).
have hComposition:=measurable_function_pushforward_precompose hInjective hScaled.1.
have [[lambda [hLambda hThetaMeasure hRepresent hRegular]] hTotal]:=hTheta.
exact ((@measure_pushforward_integral_iff R O H theta hThetaMeasure om f hComposition _).2 hScaled).
Qed.
