(** Federer (1969), 3.3.9, pp. 295–296: actual finite positive
    kernel-line mass and empty-source dimension endpoint regressions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  EuclideanProjectionSpace StructureCoordinateProjection EuclideanBlockLinearMaps
  EuclideanBlockMetricIsometries MetricIsometricImageGeometry StructureCone StructureConeUP
  StructureConeMetric StructureProjectionKernel StructurePlaneGrowth StructureConeDensityUP
  StructureInfiniteProjectionNull StructureReciprocalUpperGrowth StructureConeDensityValues
  ExtendedRealBounds PositiveRadiusLimits MetricClosedBalls EuclideanBallVolume
  EuclideanClosedBallVolume EuclideanLebesgueDimensions ApproximateDifferentialAffine
  MeasureUP MeasureBasic MeasureRestriction MeasurePushforward PushforwardMeasurableSets
  MeasureNullModification BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages
  DaniellEmptyBoundary PointMassMeasure PointMassRegularity.
From FedererTests Require Import StructurePureConeExamples StructureProjectionMassExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_vertical_line_cone_mass_lower]: concrete
    regression support for Federer 3.3.9, pp. 295–296. Push actual
    unit-interval Lebesgue length to the actual last-coordinate line
    in the plane. Every original positive-aperture cone based at the
    original line origin has mass at least r for 0<r<1. A genuine
    closed source ball of radius r/2, with its null centre removed,
    proves the bound; no cone-mass conclusion is assumed. *)
Lemma structure_vertical_line_cone_mass_lower (R:realType)
    (p:euclidean_projection_space R 2 1) (r s:R):
  (forall z,euclidean_projection_linear p z=@euclidean_first_block R 1 1 z) ->
  0<r<1 ->0<s ->
  let X:=inner_metric_space (@euclidean_inner_productP R 1) in
  let Y:=inner_metric_space (@euclidean_inner_productP R 2) in
  let f:X->Y:=@euclidean_last_injection R 1 1 in
  let phi:=measure_pushforward f
    (measure_restrict (@euclidean_lebesgue_measure R 1) (metric_closed_ball (0:X) 1)) in
  (r%:E<=phi (structure_cone (structure_projection_kernel (leqnSn 1) p) (f 0%R) r%:E s))%E.
Proof.
move=>hP /andP [hr hr1] hs; cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose Y:=inner_metric_space (@euclidean_inner_productP R 2).
pose f:X->Y:=@euclidean_last_injection R 1 1.
pose K:=metric_closed_ball (0:X) (r/2).
pose V:=K `\` [set (0:X)].
pose U:=metric_closed_ball (0:X) 1.
have hLeb:=euclidean_lebesgue_is_measure R 1.
have hHalf:=structure_density_positive_half_bounds hr.
have hMassV:@euclidean_lebesgue_measure R 1 V=r%:E.
  have hSame:=@measure_null_modification_value R [the choiceType of X]
    (@euclidean_lebesgue_measure R 1) hLeb V K [set (0:X)]
    (@positive_euclidean_singleton_null R 0 0).
  have hOutside:forall u:X,~[set (0:X)] u ->(V u<->K u).
    move=>u hNot; split; first by move=>[hu _].
    move=>hu; by split.
  rewrite (hSame hOutside) /K
    (@euclidean_closed_ball_normalized_volume R 1 0 (r/2) (ltW (andP hHalf).1))
    euclidean_unit_ball_volume1 expr1.
  congr (EFin _); nra.
have hDist u:mdist (0:X) u=inner_norm (@euclidean_inner_productP R 1) u.
  by rewrite inner_metric_distanceE sub0r inner_normN.
have hSubset:V `<=` (U `&` f @^-1`
    structure_cone (structure_projection_kernel (leqnSn 1) p) (f 0%R) r%:E s).
  move=>u [hu hNot].
  have hNorm:inner_norm (@euclidean_inner_productP R 1) u<=r/2 by rewrite -hDist.
  have hNormNe:inner_norm (@euclidean_inner_productP R 1) u!=0.
    apply/eqP=>hZero; apply:hNot; apply/eqP.
    by rewrite -(inner_norm_eq0 (@euclidean_inner_productP R 1)) hZero eqxx.
  have hNorm0:0<inner_norm (@euclidean_inner_productP R 1) u.
    by rewrite lt_neqAle inner_norm_nonnegative andbT eq_sym hNormNe.
  split.
  - apply:le_trans hu _; exact:le_trans (ltW (andP hHalf).2) (ltW hr1).
  - have hMetric:=@euclidean_last_injection_metric R 1 1 (0:X) u.
    rewrite hDist in hMetric.
    have hProjected:mdist
        (euclidean_projection_linear p (f 0%R):inner_metric_space (@euclidean_inner_productP R 1))
        (euclidean_projection_linear p (f u))=0.
      by rewrite !hP /f !euclidean_first_block_last_injection mdistxx.
    apply/(structure_projection_cone_metricE (leqnSn 1) p (f 0%R) (f u) r%:E hs).
    split.
    + rewrite hMetric lte_fin; exact:le_lt_trans hNorm (andP hHalf).2.
    + rewrite hProjected hMetric; exact:mulr_gt0 hs hNorm0.
have hBound:=@measure_mono R [the choiceType of X] (@euclidean_lebesgue_measure R 1)
  hLeb _ _ hSubset.
by rewrite hMassV in hBound.
Qed.

(** Source for [structure_vertical_line_infinite_cone_growth]: actual
    infinite upper growth for the finite positive line measure in the
    regression of Federer 3.3.9, pp. 295–296. Every positive radial
    cutoff contains a positive fixed source radius; its original cost
    is at least the inverse aperture. All real apertures are retained. *)
Lemma structure_vertical_line_infinite_cone_growth (R:realType)
    (p:euclidean_projection_space R 2 1):
  (forall z,euclidean_projection_linear p z=@euclidean_first_block R 1 1 z) ->
  let X:=inner_metric_space (@euclidean_inner_productP R 1) in
  let Y:=inner_metric_space (@euclidean_inner_productP R 2) in
  let f:X->Y:=@euclidean_last_injection R 1 1 in
  let phi:=measure_pushforward f
    (measure_restrict (@euclidean_lebesgue_measure R 1) (metric_closed_ball (0:X) 1)) in
  structure_plane_infinite_growth 1 phi setT (f 0%R) (structure_projection_kernel (leqnSn 1) p).
Proof.
move=>hP; cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose Y:=inner_metric_space (@euclidean_inner_productP R 2).
pose f:X->Y:=@euclidean_last_injection R 1 1.
pose phi:=measure_pushforward f
  (measure_restrict (@euclidean_lebesgue_measure R 1) (metric_closed_ball (0:X) 1)).
move=>delta hDelta.
pose r:=Num.min (delta/2) (1/2).
have hHalf:=structure_density_positive_half_bounds hDelta.
have hHalfOne:=@structure_density_positive_half_bounds R 1 ltr01.
have hr:0<r by rewrite /r lt_min; apply/andP; split; [exact:(andP hHalf).1|exact:(andP hHalfOne).1].
have hrDelta:r<delta.
  apply:le_lt_trans _ (andP hHalf).2; by rewrite /r ge_min lexx.
have hr1:r<1.
  apply:le_lt_trans _ (andP hHalfOne).2; by rewrite /r ge_min lexx orbT.
apply:(@structure_reciprocal_upper_growth R _ 1 ltr01)=>s /andP [hs _].
have hrBoth:0<r<1 by apply/andP; split.
have hMass:=@structure_vertical_line_cone_mass_lower R p r s hP hrBoth hs.
have hWeight:(0<=((r^-1)*(s^-1))%:E)%E by rewrite lee_fin mulr_ge0 // invr_ge0 ltW.
have hWeighted:=@lee_wpmul2r R _ hWeight _ _ hMass.
have hCancel:(r*(r^-1*s^-1))=s^-1 by rewrite mulrA mulfV ?gt_eqF // mul1r.
rewrite -EFinM hCancel in hWeighted.
apply:le_trans hWeighted _; apply:extended_real_sup_upper.
exists r; split; first by apply/andP; split.
by rewrite /phi /structure_cone_cost setTI !expr1 -muleA -EFinM.
Qed.

(** Source for [structure_infinite_projection_positive_vertical_line]:
    actual nonempty finite-positive-mass regression for COMPLETE Federer
    3.3.9, pp. 295–296. The original A is the whole plane, its
    actual restricted-pushforward measure has mass two, and B is the
    original vertical origin. The actual horizontal projection has
    zero projected outer length by the complete theorem. *)
Example structure_infinite_projection_positive_vertical_line (R:realType):
  exists p:euclidean_projection_space R 2 1,
    let X:=inner_metric_space (@euclidean_inner_productP R 1) in
    let Y:=inner_metric_space (@euclidean_inner_productP R 2) in
    let f:X->Y:=@euclidean_last_injection R 1 1 in
    let phi:=measure_pushforward f
      (measure_restrict (@euclidean_lebesgue_measure R 1) (metric_closed_ball (0:X) 1)) in
    phi setT= 2%E /\
    structure_plane_infinite_growth 1 phi setT (f 0%R) (structure_projection_kernel (leqnSn 1) p) /\
    euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` [set f 0%R])=0%E.
Proof.
have [p hP]:=@euclidean_projection_linear_complete R 2 1
  (@structure_first_block_projection R 1 1) (@structure_first_block_projection_orthogonal R 1 1).
exists p; cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose Y:=inner_metric_space (@euclidean_inner_productP R 2).
pose f:X->Y:=@euclidean_last_injection R 1 1.
pose U:=metric_closed_ball (0:X) 1.
pose mu:=measure_restrict (@euclidean_lebesgue_measure R 1) U.
pose phi:=measure_pushforward f mu.
have hPBlock z:euclidean_projection_linear p z=@euclidean_first_block R 1 1 z:=hP z.
have hLeb:=euclidean_lebesgue_is_measure R 1.
have hMu:is_measure mu:=measure_restrict_is_measure hLeb U.
have hPhi:is_measure phi:=measure_pushforward_is_measure f hMu.
have hCont:continuous f.
  apply:(@metric_isometric_map_continuous R
    [the metricType R of X] [the metricType R of Y] f).
  move=>x y; exact:(@euclidean_last_injection_metric R 1 1 x y).
have hStructure:is_structure_measure phi.
  split; first exact:hPhi.
  move=>S hS; apply:pushforward_measurable_from_preimage.
  apply:(measure_restrict_measurable U).
  exact:(borel_regular_borel_measurable hLeb (euclidean_lebesgue_borel_regular R 1)
    (continuous_borel_preimage hCont (closed_borel_set hS))).
have hTotal:phi setT= 2%E.
  rewrite /phi /measure_pushforward /mu /measure_restrict preimage_setT setIT /U
    (@euclidean_closed_ball_normalized_volume R 1 0 1 (ler01))
    euclidean_unit_ball_volume1 expr1 mulr1.
  reflexivity.
have hGrowth:=@structure_vertical_line_infinite_cone_growth R p hPBlock.
split; first exact:hTotal.
split; first exact:hGrowth.
have hFinite:(phi setT< +oo)%E by rewrite hTotal ltry.
apply:(@federer_3_3_9 R 2 1 (leqnSn 1) phi setT [set f 0%R] p hStructure hFinite).
by move=>x ->.
Qed.

(** Source for [structure_infinite_projection_zero_dimensional_empty]:
    actual degree-zero positive unit atom and original empty B in
    COMPLETE Federer 3.3.9, pp. 295–296. Both dimensions zero remain. *)
Example structure_infinite_projection_zero_dimensional_empty (R:realType):
  exists p:euclidean_projection_space R 0 0,
    let X:=inner_metric_space (@euclidean_inner_productP R 0) in
    let phi:=point_mass R (0:X) in
    phi setT= 1%E /\
    euclidean_lebesgue_measure 0 (euclidean_projection_linear p @` set0)=0%E.
Proof.
have [p _]:=structure_mass_zero_projection_exists R 0; exists p; cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R 0).
pose phi:=point_mass R (0:X).
have hStructure:is_structure_measure phi.
  split; first exact:point_mass_is_measure.
  move=>S _; exact:point_mass_every_set_measurable.
have hTotal:phi setT= 1%E:=point_mass_in R Logic.I.
split; first exact:hTotal.
apply:(@federer_3_3_9 R 0 0 (leqnn 0) phi setT set0 p hStructure).
- by rewrite hTotal ltry.
- by move=>x.
Qed.

(** Source for [structure_infinite_projection_nonmeasurable_original]:
    actual nonmeasurable positive finite-mass original A and empty
    B in COMPLETE Federer 3.3.9, pp. 295–296. The proved 2.2.4
    example supplies the original A; no measurable hull replaces it. *)
Example structure_infinite_projection_nonmeasurable_original (R:realType):
  exists (A:set (inner_metric_space (@euclidean_inner_productP R 1)))
    (p:euclidean_projection_space R 1 0),
    ~measure_measurable (@euclidean_lebesgue_measure R 1) A /\
    (0<@euclidean_lebesgue_measure R 1 A< +oo)%E /\
    euclidean_lebesgue_measure 0 (euclidean_projection_linear p @` set0)=0%E.
Proof.
have [A [p [hNot [/andP [hPos hFinite] _]]]]:=structure_projection_nonmeasurable_source_example R.
exists A,p; split; first exact:hNot.
split; first by apply/andP; split.
pose phi:=@euclidean_lebesgue_measure R 1.
have hm:=euclidean_lebesgue_is_measure R 1.
have hStructure:is_structure_measure phi.
  split; first exact:hm.
  move=>S hS; exact:(borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R 1) (closed_borel_set hS)).
apply:(@federer_3_3_9 R 1 0 (leq0n 1) phi A set0 p hStructure hFinite).
by move=>x.
Qed.
