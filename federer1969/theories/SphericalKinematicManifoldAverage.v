(** Federer (1969), 3.2.48, p. 286: averaging the exact original
    source measure over the actual right isotropy action preserves it.
    Every regularity, finiteness, continuity and invariance requirement
    is proved from the printed rectifiability/measurability hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets functions constructive_ereal topology subtype_topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates CoordinateProjection
  LinearBasis HomCompositionDeterminant EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  EuclideanHomInnerCharts HomInner HomSpaceTopology ProductInner ProductFiniteBasis InnerSpaceCountableBase
  LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  EuclideanOrthogonalInvariantMeasures IsotropyGroupTopology TopologicalGroupUP
  HaarIntegralUP CompactGroupHaarNormalisation OrthogonalHaarRegularity
  SphericalIsotropyTransverseAction SphericalCoordinateIsotropy SphericalOrthogonalProductAlgebra
  SphericalProductPreimageImage SphericalKinematicSource OrthogonalCartesianRightInvariance
  EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse UnitSphereSpace OrthogonalMaps
  RectifiableSetUP HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureRestriction
  MeasurePushforward ProductMeasure BorelRegularMeasureUP BorelRegularFiniteRestriction InvariantProbabilityAverage
  SphericalKinematicSourceAverage SphericalKinematicProfileHaarAverage SphericalKinematicTangentProfile
  SphericalKinematicSourceWeights InvariantProbabilityOrbitIntegral SphericalTangentCoordinates
  EuclideanLinearMaps FiniteInnerChartUP SphericalPullbackPushforward ExteriorGrading ExteriorNorm HilbertFormCompactness EuclideanSubmanifoldUP GammaHalfSequences
  MeasureIntegralUP MeasureAlmostUP MeasureAlmostBasic MeasureBasic RestrictedAlmostEverywhere
  SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_manifold_average]: the last
    averaging display in 3.2.48, p. 286, on original measurable
    subsets of spherical manifolds. The actual pointwise tangent profile,
    right isotropy action, signed source integral and Haar average are
    used. Joint measurability follows from full invariant image measures;
    source finiteness proves countable measurability before signed Fubini. *)
Theorem spherical_kinematic_manifold_average (R:realType) d k m
    (hk:(k<=d)%N) (hm:(m<=d)%N) (hkm:(d<=k+m)%N)
    (c:R_n R (1+d)) (Q:Hom (R_n R (1+d)) (R_n R (1+d)))
    (A B M N:set (R_n R (1+d))) (E:exterior_power (R_n R d) d) n v
    (e:Hom (R_n R n) [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type])
    (p:Hom [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type] (R_n R n))
    (t:Hom (Hom (R_n R (1+d)) (R_n R (1+d))) (R_n R v))
    (alpha beta:R_n R (1+d)->R) av bv
    (mulS:euclidean_orthogonal_group R d->euclidean_orthogonal_group R d->euclidean_orthogonal_group R d)
    (invS:euclidean_orthogonal_group R d->euclidean_orthogonal_group R d)
    (eS:euclidean_orthogonal_group R d) (theta:set (euclidean_orthogonal_group R d)->\bar R):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->Q (spherical_coordinate_pole R d)=c ->
  A `<=` M ->B `<=` N ->
  @is_euclidean_submanifold R (1+d)%N k 1%N M ->@is_euclidean_submanifold R (1+d)%N m 1%N N ->
  M `<=` @euclidean_unit_sphere_set R (1+d) ->N `<=` @euclidean_unit_sphere_set R (1+d) ->
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
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E= 1 ->
  is_finite_inner_chart (product_inner (@euclidean_hom_inner_productP R (1+d) (1+d))
    (@euclidean_hom_inner_productP R (1+d) (1+d))) e p ->
  is_orthogonal_map (@euclidean_hom_inner_product R (1+d) (1+d))
    (@euclidean_inner_product R v) (hom_as_linear t) ->
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R d) (@coordinate_basisP R d))
    (linear_group_inv (@euclidean_inner_productP R d) (@coordinate_basisP R d))
    (linear_group_unit (@euclidean_inner_productP R d) (@coordinate_basisP R d))
    (euclidean_orthogonal_group R d) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))) in
  let S:=[set z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
    spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2] in
  let rho:=measure_restrict (@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) S in
  let w:=fun z:P=>alpha (z.1 c)*beta (z.2 c) in
  forall q,is_measure_integral rho
    (real_total_integrand (fun z=>w z*spherical_kinematic_tangent_profile c M N e p t z)) q ->
  q=(((Num.sqrt (2:R))^+((d*(d-1)%/2)+(k+m-d)))*
    (gamma_half_sequence R k*gamma_half_sequence R m/
      (gamma_half_sequence R d*gamma_half_sequence R (k+m-d)))*
    ((spherical_preimage_mass_scale R d k*av)*(spherical_preimage_mass_scale R d m*bv)))%:E.
Proof.
move=>hc hQ hQc hAM hBN hM hN hMS hNS hRA hMA hRB hMB hAlpha hBeta hE hChart ht hGroup hTheta P S rho w q hIntegral.
have hA:A `<=` @euclidean_unit_sphere_set R (1+d) by move=>x hx; exact (hMS x (hAM x hx)).
have hB:B `<=` @euclidean_unit_sphere_set R (1+d) by move=>x hx; exact (hNS x (hBN x hx)).
pose H:=Hom (R_n R (1+d)) (R_n R (1+d)).
pose hH:=@euclidean_hom_inner_productP R (1+d) (1+d).
pose hP:=product_inner_productP hH hH.
pose G:=euclidean_orthogonal_group R d.
have hSource:=@spherical_kinematic_source R d k m c A B hc hA hB hRA hMA hRB hMB.
pose hRho:=measure_restrict_is_measure (@hausdorff_measure_is_measure R P
  ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) S.
have hRhoRegular:is_borel_regular_measure rho.
  exact (@borel_regular_finite_measurable_restriction R P
    (@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)))
    (@hausdorff_measure_is_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)))
    (@hausdorff_measure_borel_regular R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)))
    S hSource.2 hSource.1.2).
have hRhoFinite:(rho setT< +oo)%E.
  rewrite /rho /measure_restrict setIT; exact hSource.1.2.
have [U hU]:=@orthogonal_group_countable_open_base R d.
pose b:=@hom_rank_one_base R (R_n R (1+d)) (R_n R (1+d)) (1+d) (1+d)
  (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d)) (@coordinate_basis R (1+d)).
have hb:=@hom_rank_one_baseP R (R_n R (1+d)) (R_n R (1+d)) (1+d) (1+d)
  (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d)) (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d)).
have [V hV]:=@inner_space_countable_open_base R [the lmodType R of (H*H)%type] _ hP _
  (cartesian_basis b b) (cartesian_basisP hb hb).
pose F:=fun z:G*P=>orthogonal_cartesian_right_translation
  (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q (orthogonal_element_map z.1))) z.2.
pose C:=(Num.sqrt (2:R))^+((d*(d-1)%/2)+(k+m-d))*
  (gamma_half_sequence R k*gamma_half_sequence R m/
    (gamma_half_sequence R d*gamma_half_sequence R (k+m-d))).
pose J:=spherical_kinematic_tangent_profile c M N e p t.
pose f:=fun z:P=>w z*J z.
have hPush:=@spherical_kinematic_source_average R d k m c Q A B mulS invS eS theta
  hc hQ hQc hA hB hRA hMA hRB hMB hGroup hTheta.
have hOrbits:measure_almost_everywhere rho [set z|is_measure_integral theta
    (real_total_integrand (fun g=>f (F (g,z)))) (C*w z)%:E].
  apply/(restricted_almost_everywhere_iff _ S _).
  apply:(measure_almost_everywhere_mono
    (@hausdorff_measure_is_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) _
    (measure_almost_everywhere_true (@hausdorff_measure_is_measure R P
      ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)))))=>z _ hz.
  have hzM:spherical_orthogonal_preimage c M z.1 by split; [exact hz.1.1|exact (hAM _ hz.1.2)].
  have hzN:spherical_orthogonal_preimage c N z.2 by split; [exact hz.2.1|exact (hBN _ hz.2.2)].
  have hJ:=@spherical_kinematic_profile_haar_average R d k m hk hm hkm c M N z.1 z.2 Q E n v e p t
    mulS invS eS theta hc hQ hQc hM hN hMS hNS hzM hzN hE hChart ht hGroup hTheta.
  have hScaled:=@real_total_integral_scale R G theta (normalised_haar_measure_law hTheta)
    _ C (w z) hJ.
  have hWeight g:w (F (g,z))=w z.
    have hMember:=@spherical_isotropy_transverse_operator_member R d Q (orthogonal_element_map g)
      hQ (orthogonal_element_orthogonal g).
    rewrite hQc in hMember.
    have hFixed:euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q (orthogonal_element_map g)) c=c.
      have h:=congr1 (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q (orthogonal_element_map g))) hMember.2.
      rewrite (euclidean_orthogonal_adjoint_cancel hMember.1) in h; exact (esym h).
    change (alpha (z.1 c)*beta (z.2 (euclidean_rectangular_adjoint
      (spherical_isotropy_transverse_operator Q (orthogonal_element_map g)) c))=
      alpha (z.1 c)*beta (z.2 c)).
    by rewrite hFixed.
  have hFunction:(fun g:G=>f (F (g,z)))=
      (fun g:G=>w z*spherical_kinematic_tangent_profile c M N e p t
        (z.1,hom_comp z.2 (euclidean_rectangular_adjoint
          (spherical_isotropy_transverse_operator Q (orthogonal_element_map g))))).
    apply:funext=>g; by rewrite /f hWeight.
  change (is_measure_integral theta (real_total_integrand (fun g:G=>f (F (g,z)))) (C*w z)%:E).
  rewrite hFunction [C*w z]mulrC; exact hScaled.
have hWeight:=@spherical_kinematic_source_weight_integral R d k m c A B alpha beta av bv
  hc hA hB hRA hMA hRB hMB hAlpha hBeta.
have hMean:=@real_total_integral_scale R P rho hRho w
  ((spherical_preimage_mass_scale R d k*av)*(spherical_preimage_mass_scale R d m*bv)) C hWeight.
exact (@invariant_probability_orbit_integral R G P theta rho
  (normalised_haar_measure_law hTheta) hRho U V F f (fun z=>C*w z) q
  (C*((spherical_preimage_mass_scale R d k*av)*(spherical_preimage_mass_scale R d m*bv)))
  hU hV (orthogonal_normalised_haar_borel_regular hGroup hTheta) hRhoRegular
  hTheta.2 hRhoFinite hPush hIntegral hOrbits hMean).
Qed.
