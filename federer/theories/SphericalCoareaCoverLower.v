(** Federer (1969), 3.2.47(3), p. 283: a
    finite rectifiable Borel cover of the WHOLE original
    preimage supplies the lower mass comparison. Actual
    coarea, whole-fibre containment, the tangent Jacobian bound
    and characteristic upper integrals retain arbitrary original E. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts OrthogonalMaps FiniteInnerChartUP FiniteInnerChartCompact
  SphericalOrthogonalProductAlgebra SphericalProductPreimageImage SphericalCoordinateOrbitCalculus
  SphericalGroupSubsetJacobianBound SphericalOrthogonalFibreIsometry SphericalIsotropyMeasure
  EuclideanStiefelHalfNormalization StiefelGammaVolumeScalar UnitSphereSpace
  LipschitzUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  PartialMappingMultiplicity MeasureRestriction MeasureApproximateJacobian
  RectifiableSetUP RectifiableCoarea RectifiableCoareaFibreMassIntegralBound
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureBasic MeasureIntegralUP MeasureSubsetIntegral
  BorelRegularMeasureUP TopologicalBorel SubsetIntegralArbitraryConstantLower ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_coarea_cover_lower]: the lower
    comparison for the original arbitrary set in 3.2.47(3),
    p. 283. Borel rectifiable source and target covers
    are genuine obligations here, discharged by true hulls
    in the final theorem. No measurability of original E
    or null difference from either hull is assumed. *)
Theorem spherical_coarea_cover_lower (R:realType) n d r
    (e:Hom (R_n R d) (Hom (R_n R n.+1) (R_n R n.+1)))
    (p:Hom (Hom (R_n R n.+1) (R_n R n.+1)) (R_n R d))
    (c:R_n R n.+1) (E Z:set (R_n R n.+1)) (W:set (R_n R d)):
  is_finite_inner_chart (@euclidean_hom_inner_product R n.+1 n.+1) e p ->
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->E `<=` Z ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r Z ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n.+1)) Z ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d)) (r+n*(n-1)%/2)%N) (r+n*(n-1)%/2)%N W ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R d)) W ->
  p @` (spherical_orthogonal_preimage c E) `<=` W ->
  W `<=` p @` (spherical_orthogonal_preimage c Z) ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
    (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c)*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) r E<=
    (((Num.sqrt (2:R))^-1)^+r)%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R d)) (r+n*(n-1)%/2)%N W)%E.
Proof.
move=>hChart hc hES hEZ hRectZ hZB hRectW hWB hEW hWZ.
pose X:=inner_metric_space (@euclidean_inner_productP R d).
pose Y:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose H:=inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1).
pose mu:=(n*(n-1)%/2)%N.
pose m:=(r+mu)%N.
pose rho:=@hausdorff_measure R X m.
pose beta:=@hausdorff_measure R Y r.
pose alpha:=@hausdorff_measure R X mu.
have hRho:=@hausdorff_measure_is_measure R X m.
have hBeta:=@hausdorff_measure_is_measure R Y r.
have hAlpha:=@hausdorff_measure_is_measure R X mu.
have hWMeas:=borel_regular_borel_measurable hRho (@hausdorff_measure_borel_regular R X m) hWB.
have hZMeas:=borel_regular_borel_measurable hBeta (@hausdorff_measure_borel_regular R Y r) hZB.
pose F:=fun x:R_n R d=>e x c.
pose f:=partial_function_source_restrict W (partial_function_total F).
have hDom:partial_function_domain f=W.
  by rewrite /f partial_function_source_restrict_domain partial_function_total_domain setIT.
have hLip:exists L,@is_partial_metric_lipschitz_bound R X Y f L.
  have [L [_ hBound]]:=@spherical_coordinate_orbit_lipschitz R n.+1 d e c.
  exists L; split; first exact hBound.1.
  move=>x y u v [hx hFu] [hy hFv].
  change (F x=u) in hFu; change (F y=v) in hFv.
  rewrite -hFu -hFv; exact (hBound.2 x y I I).
have hRange:partial_function_range f `<=` Z.
  move=>z [x [hx hFx]].
  have [g [hg hZg] hpg]:=hWZ x hx.
  change (F x=z) in hFx.
  change (e x c=z) in hFx.
  rewrite -hpg (finite_inner_chart_right_inverse hChart) in hFx.
  by rewrite -hFx.
have hCoarea:=@federer_3_2_22 R m d r n.+1 W Z f (leq_addr mu r)
  hRectW hWMeas hRectZ hZMeas hDom hLip hRange.
have hWO:W `<=` p @` [set g|is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear g)].
  move=>x hx; have [g [hg _] hpg]:=hWZ x hx; by exists g.
pose C:=(((Num.sqrt (2:R))^-1)^+r).
have hC:(0<C)%R.
  exact (exprn_gt0 r (euclidean_stiefel_half_normalization R).1).
have hJac x j (hx:W x):partial_function_graph (measure_approximate_jacobian
    (measure_restrict rho W) m r f) x j ->(j<=C)%R.
  exact (@spherical_group_subset_jacobian_bound R n d m r e p c W x j hChart hc hWO hx).
have hFibreMeas z:measure_measurable (@hausdorff_measure R X (m-r)) (partial_mapping_fibre f z).
  exact (borel_regular_borel_measurable (@hausdorff_measure_is_measure R X (m-r))
    (@hausdorff_measure_borel_regular R X (m-r))
    (@spherical_coordinate_fibre_borel R n.+1 d e c W z hWB)).
have [a [hIntegral hUpper]]:=@rectifiable_coarea_fibre_mass_integral_bound R m d r n.+1 W Z f C
  hCoarea hWMeas hDom hC hJac hFibreMeas.
change (is_measure_subset_integral beta Z (partial_function_total
  (fun z=>(@hausdorff_measure R X (r+mu-r)%N (partial_mapping_fibre f z):extended_real_line R))) a) in hIntegral.
rewrite addKn in hIntegral.
pose profile:=fun z:R_n R n.+1=>(alpha (partial_mapping_fibre f z):extended_real_line R).
pose lambda:=stiefel_gamma_volume_scalar R (leqnn n).
have hLambda:(0<lambda)%R:=stiefel_gamma_volume_scalar_positive R (leqnn n).
have hProfileLower z (hz:E z):(lambda%:E<=profile z)%E.
  have hContain:p @` (spherical_orthogonal_preimage c [set z]) `<=` partial_mapping_fibre f z.
    move=>x [g [hg hValue] <-].
    split.
    - apply:hEW; exists g; last reflexivity.
      split; first exact hg.
      change (E (g c)); by rewrite hValue.
    - change (e (p g) c=z).
      by rewrite (finite_inner_chart_right_inverse hChart).
  have hFibreMass:alpha (p @` (spherical_orthogonal_preimage c [set z]))=lambda%:E.
    rewrite /alpha (@finite_inner_chart_inverse_hausdorff R _ _
      (@euclidean_hom_inner_productP R n.+1 n.+1) d e p hChart).
    rewrite (@spherical_orthogonal_fibre_measure R n c z hc (hES z hz) mu).
    exact (@spherical_isotropy_gamma_mass R n c hc).
  have hEstimate:=@measure_mono R X alpha hAlpha _ _ hContain.
  by rewrite hFibreMass in hEstimate.
have hLower:(lambda%:E*beta E<=a)%E.
  apply:(@subset_integral_arbitrary_positive_constant_lower R [the choiceType of Y] beta hBeta E Z
    (partial_function_total profile) a lambda hEZ hLambda _ _ hIntegral).
  - move=>z _; exists (profile z); split; first reflexivity.
    exact (@measure_nonnegative R X alpha hAlpha _).
  - move=>z y hz hValue.
    change (profile z=y) in hValue; rewrite -hValue; exact (@hProfileLower z hz).
have hIota:@hausdorff_measure R H mu (spherical_orthogonal_isotropy c)=lambda%:E.
  exact (@spherical_isotropy_gamma_mass R n c hc).
rewrite hIota; exact (le_trans hLower hUpper).
Qed.
