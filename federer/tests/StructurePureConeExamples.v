(** Federer (1969), 3.3.6, pp. 293–294: actual endpoint
    and positive-mass regressions for the complete numbered theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra ring.
From Federer Require Import TensorUP GrassmannAbbreviations FiniteCoordinates CoordinateProjection
  EuclideanInnerProduct InnerMetric AdjointUP Adjoint OrthogonalMaps OrthogonalInjectionSpaces
  EuclideanOrthogonalInvariantMeasures EuclideanProjectionSpace StructureConeUP StructureCone
  StructureProjectionKernel StructureConeMetric StructureConeMassUP StructurePureConeBound
  StructureConeDensityValues RectifiableSetUP PureUnrectifiableLaws
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureRestriction BorelRegularMeasureUP TopologicalBorel
  EuclideanLebesgueDimensions EuclideanBallVolume EuclideanClosedBallVolume
  ApproximateDifferentialAffine PositiveClosedSubsets DaniellEmptyBoundary
  MetricClosedBalls MetricDensities PointMassMeasure PointMassRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_mass_zero_projection_exists]: local actual
    zero-target projections for regressions of Federer 3.3.6, p. 293.
    Their existence is the original O star definition, 1.7.4, p. 30. *)
Lemma structure_mass_zero_projection_exists (R:realType) n:
  exists p:euclidean_projection_space R n 0,forall x,euclidean_projection_linear p x= 0.
Proof.
have [f hf]:=@euclidean_orthogonal_injection_exists R n 0 (leq0n n).
have hp:is_orthogonal_projection (@euclidean_inner_product R n)
    (@euclidean_inner_product R 0)
    (inner_adjoint (@euclidean_inner_productP R 0)
      (@euclidean_inner_productP R n) (@coordinate_basisP R 0) f).
  by exists f; split; [exact:hf|exact:inner_adjointP].
pose p:=orthogonal_projection_of (@euclidean_inner_productP R 0)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n) hp.
exists p=>x; apply/ffunP=>i; have hi:=ltn_ord i; by rewrite ltn0 in hi.
Qed.

(** Source for [structure_mass_zero_ambient_infinite_cutoff_example]:
    nonempty R^0, degree zero and infinite cutoff in Federer 3.3.6,
    p. 293. The actual zero measure satisfies the complete theorem;
    its original nonempty source and upper-density bound are retained. *)
Example structure_mass_zero_ambient_infinite_cutoff_example (R:realType):
  exists p:euclidean_projection_space R 0 0,
    is_structure_uniform_cone_mass_bound (leqnn 0)
      (fun _=>0%E) setT p (1/2) 1 +oo%E /\
    (upper_metric_density 0
      (measure_restrict (fun _=>0%E) (@setT (inner_metric_space (@euclidean_inner_productP R 0))))
      (0%R:inner_metric_space (@euclidean_inner_productP R 0))<= 2%:E)%E.
Proof.
have [p hP]:=structure_mass_zero_projection_exists R 0.
have hm:=@daniell_zero_measure R (inner_metric_space (@euclidean_inner_productP R 0)).
have hStructure:is_structure_measure (fun _:set (inner_metric_space (@euclidean_inner_productP R 0))=>0%E).
  split; first exact:hm.
  by move=>S _ T; rewrite add0e.
have hPure:@is_purely_measure_m_unrectifiable R
    (inner_metric_space (@euclidean_inner_productP R 0)) (fun _=>0%E) 0 setT.
  split; first exact:hm.
  by move=>[F [_ [_ hPos]]]; rewrite ltxx in hPos.
have hs:=@structure_density_positive_half_bounds R 1 ltr01.
have hMass:is_structure_uniform_cone_mass_bound (leqnn 0) (fun _=>0%E) setT p (1/2) 1 +oo%E.
  move=>x _ r hr hCutoff.
  by rewrite euclidean_unit_ball_volume0 expe0 expr0 !mule1 lee_fin ler01.
have hFinite:=@structure_uniform_cone_finite_radius R 0 0 (leqnn 0) (fun _=>0%E) setT p (1/2) 1 +oo%E hMass.
have hResult:=(@federer_3_3_6 R 0 0 (leqnn 0) (fun _=>0%E) setT p (1/2) 1 +oo%E
  hStructure hPure hs ltr01 (@ltry R 0) hFinite 0).2.
exists p; split; first exact:hMass.
by rewrite expr0 !mulr1 in hResult.
Qed.

(** Source for [structure_mass_empty_positive_atom_example]: empty
    original A under the positive actual R^0 unit atom, a boundary
    regression of Federer 3.3.6, p. 293. The complete theorem gives
    every original cylinder bound although the ambient measure is nonzero. *)
Example structure_mass_empty_positive_atom_example (R:realType):
  exists p:euclidean_projection_space R 0 0,
    @point_mass R (inner_metric_space (@euclidean_inner_productP R 0)) 0 setT= 1%E /\
    forall rho:R,0<rho ->rho<= 1/48 ->
      (point_mass R 0%R (set0 `&` metric_closed_ball (0%R:inner_metric_space (@euclidean_inner_productP R 0)) (4*rho/(1/2)) `&`
        ((euclidean_projection_linear p) @^-1`
          metric_closed_ball (euclidean_projection_linear p 0%R:inner_metric_space (@euclidean_inner_productP R 0)) rho))<= 2%:E)%E.
Proof.
have [p hP]:=structure_mass_zero_projection_exists R 0.
pose phi:=@point_mass R (inner_metric_space (@euclidean_inner_productP R 0)) 0.
have hm:is_measure phi:=point_mass_is_measure R _.
have hStructure:is_structure_measure phi.
  split; first exact:hm.
  move=>S hS; exact:point_mass_every_set_measurable.
have hPure:@is_purely_measure_m_unrectifiable R
    (inner_metric_space (@euclidean_inner_productP R 0)) phi 0 set0.
  apply/(pure_unrectifiable_iff_rectifiable_subsets_null); split; first exact:hm.
  move=>F hF _; apply:(measure_null_subset hm hF); exact:measure_empty hm.
have hs:=@structure_density_positive_half_bounds R 1 ltr01.
have hMass:is_structure_uniform_cone_mass_bound (leqnn 0) phi set0 p (1/2) 1 1%E.
  by move=>x [].
have hFinite:=@structure_uniform_cone_finite_radius R 0 0 (leqnn 0) phi set0 p (1/2) 1 1%E hMass.
have hResult:=(@federer_3_3_6 R 0 0 (leqnn 0) phi set0 p (1/2) 1 1%E
  hStructure hPure hs ltr01 (ltac:(by rewrite lte_fin)) hFinite 0).1.
exists p; split; first exact:point_mass_in.
move=>rho hRho hSmall.
have hTwentyFour:(0:R)<24 by rewrite ltr0n.
have hCutoff:(rho%:E<=(1/2:R)%:E*1%E/(24:R)%:E)%E.
  rewrite mule1 inver (gt_eqF hTwentyFour) -EFinM lee_fin; lra.
have hBound:=hResult rho hRho hCutoff.
by rewrite expr0 euclidean_unit_ball_volume0 !mulr1 in hBound.
Qed.

(** Source for [structure_mass_positive_line_example]: an actual positive
    cylinder mass under the nonzero line Lebesgue measure, testing the
    degree-zero case and the extreme finite radius of Federer 3.3.6,
    p. 293. The whole line is purely (L^1,0) unrectifiable because
    zero-rectifiable sets are finite and its actual singletons are null. *)
Example structure_mass_positive_line_example (R:realType):
  exists p:euclidean_projection_space R 1 0,
    let B:=(@setT (inner_metric_space (@euclidean_inner_productP R 1))) `&`
      metric_closed_ball (0%R:inner_metric_space (@euclidean_inner_productP R 1)) (4*(1/48)/(1/2)) `&`
      ((euclidean_projection_linear p) @^-1`
        metric_closed_ball (euclidean_projection_linear p 0%R:inner_metric_space (@euclidean_inner_productP R 0)) (1/48)) in
    euclidean_lebesgue_measure 1 B=(1/3:R)%:E /\
    (euclidean_lebesgue_measure 1 B<= 4%:E)%E /\
    (upper_metric_density 0 (measure_restrict (@euclidean_lebesgue_measure R 1) setT)
      (0%R:inner_metric_space (@euclidean_inner_productP R 1))<= 4%:E)%E.
Proof.
have [p hP]:=structure_mass_zero_projection_exists R 1.
pose phi:=@euclidean_lebesgue_measure R 1.
have hm:is_measure phi:=euclidean_lebesgue_is_measure R 1.
have hStructure:is_structure_measure phi.
  split; first exact:hm.
  move=>S hS; apply:(borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R 1)).
  exact:closed_borel_set hS.
have hPure:is_purely_measure_m_unrectifiable phi 0 setT.
  apply/(pure_unrectifiable_iff_rectifiable_subsets_null); split; first exact:hm.
  move=>F _ hFinite.
  apply:(countable_null_singletons_null hm (finite_set_countable hFinite))=>x _.
  exact:positive_euclidean_singleton_null.
have hs:=@structure_density_positive_half_bounds R 1 ltr01.
have hMass:is_structure_uniform_cone_mass_bound (leq0n 1) phi setT p (1/2) 2 1%E.
  move=>x _; case=>[r| |] hr hCutoff; last 2 first.
  - by rewrite leye_eq in hCutoff.
  - by rewrite ltNge leNye in hr.
  have hr0:0<r by move:hr; rewrite lte_fin.
  have hr1:r<= 1 by move:hCutoff; rewrite lee_fin.
  have hSub:(setT `&` structure_cone (structure_projection_kernel (leq0n 1) p) x r%:E (1/2)) `<=`
      metric_closed_ball x r.
    move=>z [_ hCone].
    have hNear:=(structure_projection_cone_metricE (leq0n 1) p x z r%:E (andP hs).1).1 hCone.
    have hDistance:mdist x z<r by move:hNear.1; rewrite lte_fin.
    exact:ltW hDistance.
  have hBound:=@measure_mono R _ phi hm _ _ hSub.
  rewrite /phi (@euclidean_closed_ball_normalized_volume R 1 x r (ltW hr0))
    euclidean_unit_ball_volume1 expr1 in hBound.
  rewrite euclidean_unit_ball_volume0 expe0 expr0 !mule1.
  apply:le_trans hBound _; rewrite lee_fin; lra.
have hTwo:(0:R)<2 by rewrite ltr0n.
have hOne:(0<(1:R)%:E)%E by rewrite lte_fin.
have hFinite:=@structure_uniform_cone_finite_radius R 1 0 (leq0n 1) phi setT p (1/2) 2 1%E hMass.
have [hCylinders hDensity]:=@federer_3_3_6 R 1 0 (leq0n 1) phi setT p (1/2) 2 1%E
  hStructure hPure hs hTwo hOne hFinite 0.
have hRho:(0:R)<1/48 by lra.
have hTwentyFour:(0:R)<24 by rewrite ltr0n.
have hCutoff:((1/48:R)%:E<=(1/2:R)%:E*1%E/(24:R)%:E)%E.
  rewrite mule1 inver (gt_eqF hTwentyFour) -EFinM lee_fin; lra.
have hBound:=hCylinders (1/48) hRho hCutoff.
have hCoefficient:2*84^+0*2*euclidean_unit_ball_volume R 0*(1/48)^+0=(4:R).
  rewrite euclidean_unit_ball_volume0 !expr0; ring.
have hDensityCoefficient:2*84^+0*2=(4:R) by rewrite expr0; ring.
rewrite hCoefficient in hBound; rewrite hDensityCoefficient in hDensity.
exists p; split; last by split.
have hRadius:4*(1/48:R)/(1/2)= 1/6 by lra.
rewrite hRadius.
have hRegion:(setT `&` metric_closed_ball (0%R:inner_metric_space (@euclidean_inner_productP R 1)) (1/6) `&`
    ((euclidean_projection_linear p) @^-1`
      metric_closed_ball (euclidean_projection_linear p 0%R:inner_metric_space (@euclidean_inner_productP R 0)) (1/48)))=
    metric_closed_ball (0%R:inner_metric_space (@euclidean_inner_productP R 1)) (1/6).
  apply/seteqP; split; first by move=>x [[_ hx] _].
  move=>x hx; split; first by split.
  change (is_true (mdist (euclidean_projection_linear p 0%R:inner_metric_space (@euclidean_inner_productP R 0))
    (euclidean_projection_linear p x)<= 1/48)).
  rewrite !hP mdistxx; lra.
rewrite hRegion (@euclidean_closed_ball_normalized_volume R 1 0 (1/6) (ltac:(lra)))
  euclidean_unit_ball_volume1 expr1.
congr (EFin _); lra.
Qed.
