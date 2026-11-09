(** Federer (1969), 3.3.4, p. 290: the
    finite invariant reference measure equals its
    total mass times the actual normalized Haar
    orbit image. Derive the all-set identity from
    2.7.11(2), p. 128, through the already proved
    continuous-test theorem and Radon uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasurePushforward MeasureScaleIntegral
  MeasureScaleBorelRegular BorelRegularMeasureUP RadonBorelRegularity
  CompactMetricFiniteRadon CompactMetricSeparability CompactSupportCountableRadon
  SubtypeCompactHausdorff TopologicalGroupUP HomogeneousSpaceUP HomogeneousSpaceLaws
  CompactGroupHaarNormalisation CompactGroupHomogeneousMeasures CompactInvariantOrbitIntegral
  CovariantIntegralUP HaarIntegralUP CompactSupportFunctionUP DaniellSpacePushforward
  RealIntegralFunctionalUP MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_metric_finite_invariant_orbit_measure]:
    the all-subset invariant-measure identity used in
    Federer 3.3.4, p. 290, with actual finite
    Borel regular reference, original homogeneous action
    and actual normalized Haar measure. No orbit
    measure identification is an input assumption. *)
Theorem compact_metric_finite_invariant_orbit_measure (R:realType)
    (G:topologicalType) (X:metricType R)
    (mul:G->G->G) (inv:G->G) (e:G) (A:G->X->X)
    (hG:is_locally_compact_hausdorff_group mul inv e)
    (hA:is_homogeneous_space mul A)
    (mu:set X->\bar R) (theta:set G->\bar R) (C:R) (x:X):
  compact (@setT G) ->is_measure mu ->is_borel_regular_measure mu ->
  0<C ->mu setT=C%:E ->
  (forall g,measure_pushforward (A g) mu=mu) ->
  is_normalised_haar_measure mul theta ->
  mu=measure_scale C (measure_pushforward (orbit_map A x) theta).
Proof.
move=>hGc hMu hB hC hMass hInvariant hTheta.
have hCompact:=compact_homogeneous_space_compact hGc hA.
have hHaus:=@metric_hausdorff R X.
have hMuFinite:(mu setT< +oo)%E by rewrite hMass ltry.
have hMuRadon:=compact_metric_finite_borel_radon x hMu hB hCompact hMuFinite.
pose nu:=measure_pushforward (orbit_map A x) theta.
have hNorm:=@compact_orbit_pushforward_invariant R G X mul inv e A
  hG hGc hA hHaus theta x hTheta.
have [[L [hLD hLC hNu hLRep hLRegular]] hNuOne]:=hNorm.
change (nu setT= 1%E) in hNuOne.
have [Base hBase]:=compact_metric_countable_open_base hCompact.
have hNuRadon:=@compact_support_regular_countable_base_radon R X nu L
  hNu hLRep hLRegular Base hHaus (compact_space_locally_compact hCompact) hBase.
have hNuBorel:=radon_borel_regular hNu hNuRadon.
have hScaleMeasure:=measure_scale_is_measure hNu hC.
have hScaleBorel:=measure_scale_borel_regular hNu hC hNuBorel.
have hScaleFinite:(measure_scale C nu setT< +oo)%E.
  by rewrite /measure_scale hNuOne mule1 ltry.
have hScaleRadon:=compact_metric_finite_borel_radon x hScaleMeasure hScaleBorel
  hCompact hScaleFinite.
have [[lambda [hHaar hThetaMeasure hThetaRep hThetaRegular]] hThetaOne]:=hTheta.
have hF:=orbit_map_continuous hA x.
have hProper:=compact_homogeneous_orbit_proper hGc hA (x:=x) hHaus.
pose N:=(fun u:X->R=>lambda (u\o orbit_map A x)).
have hNuRep:is_real_integral_functional nu (@compactly_supported_continuous_functions R X) N.
  exact:(daniell_pushforward_integral hF hProper hThetaMeasure hThetaRep).
have hScaleRep:=measure_scale_represents hNu hC hNuRep.
have hMuRep:is_real_integral_functional mu (@compactly_supported_continuous_functions R X)
    (fun u=>C*N u).
  move=>u hu.
  have hPull:=compactly_supported_compose hF hProper hu.
  exact:(@compact_finite_invariant_orbit_integral R G X mul inv e A hG hA hHaus
    mu theta C x hGc hMu hB hC hMass hInvariant hTheta u (N u) hu (hThetaRep _ hPull)).
exact:(radon_representations_coincide hMu hScaleMeasure hMuRadon hScaleRadon hMuRep hScaleRep).
Qed.
