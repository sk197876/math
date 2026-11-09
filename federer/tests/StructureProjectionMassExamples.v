(** Federer (1969), 3.3.7, p. 294: actual positive,
    nonmeasurable and unbounded original sources. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace CoordinateProjection EuclideanBallVolume EuclideanClosedBallVolume
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes DenseMinkowskiInfinite PointMassMeasure
  StructureConeUP StructureCone StructureProjectionKernel StructureApertureMassUP StructurePureProjectionMass
  StructureProjectionBorelMeasure StructureConeDensityValues RectifiableSetUP PureUnrectifiableLaws
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure PositiveClosedSubsets
  ApproximateDifferentialAffine BernsteinNonmeasurableSubset EuclideanMetricCompleteness
  EuclideanMetricSeparability BorelRegularMeasureUP TopologicalBorel FiniteOpenBoxUnionBounds
  DaniellEmptyBoundary MetricClosedBalls.
From FedererTests Require Import StructurePureConeExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projection_line_zero_degree_bound]: regression
    setup for Federer 3.3.7, p. 294. Actual line Lebesgue measure
    makes every finite set null, so every original A is purely
    (L^1,0) unrectifiable. An actual total mass at most one gives the
    printed cone hypothesis with lambda one, at every positive radius
    and small aperture. Apply the COMPLETE original theorem. *)
Lemma structure_projection_line_zero_degree_bound (R:realType)
    (A:set (inner_metric_space (@euclidean_inner_productP R 1))):
  (@euclidean_lebesgue_measure R 1 A<=1)%E ->
  exists p:euclidean_projection_space R 1 0,
    (forall x,euclidean_projection_linear p x=0) /\
    (@euclidean_lebesgue_measure R 1 A<=
      (2*84^+0*1:R)%:E*euclidean_lebesgue_measure 0 (euclidean_projection_linear p @` A))%E.
Proof.
move=>hMass.
have [p hP]:=structure_mass_zero_projection_exists R 1.
pose phi:=@euclidean_lebesgue_measure R 1.
have hm:is_measure phi:=euclidean_lebesgue_is_measure R 1.
have hStructure:is_structure_measure phi.
  split; first exact:hm.
  move=>S hS; exact:(borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R 1) (closed_borel_set hS)).
have hPure:is_purely_measure_m_unrectifiable phi 0 A.
  apply/(pure_unrectifiable_iff_rectifiable_subsets_null); split; first exact:hm.
  move=>F _ hFinite.
  apply:(countable_null_singletons_null hm (finite_set_countable hFinite))=>x _.
  exact:positive_euclidean_singleton_null.
have hAperture:is_structure_aperture_mass_bound (leq0n 1) phi A p (1/2) 1.
  move=>x hx r hr s hs hsSigma.
  have hSub:(A `&` structure_cone (structure_projection_kernel (leq0n 1) p) x r%:E s) `<=` A.
    by move=>y [hy _].
  have hBound:=le_trans (@measure_mono R _ phi hm _ _ hSub) hMass.
  by rewrite euclidean_unit_ball_volume0 !expr0 !mulr1.
have hSigma:=@structure_density_positive_half_bounds R 1 ltr01.
have hFull:=@federer_3_3_7 R 1 0 (leq0n 1) phi A p (1/2) 1
  hStructure hPure hSigma ltr01 hAperture.
exists p; by split.
Qed.

(** Source for [structure_projection_positive_interval_example]: an
    actual interval of Lebesgue mass one and its actual zero-dimensional
    projection of mass one, testing Federer 3.3.7, p. 294. Both
    positive masses are computed, and the full numbered theorem supplies
    the bound on the original interval. *)
Example structure_projection_positive_interval_example (R:realType):
  let A:=metric_closed_ball (0:inner_metric_space (@euclidean_inner_productP R 1)) (1/2) in
  exists p:euclidean_projection_space R 1 0,
    @euclidean_lebesgue_measure R 1 A= 1%E /\
    euclidean_lebesgue_measure 0 (euclidean_projection_linear p @` A)= 1%E /\
    (@euclidean_lebesgue_measure R 1 A<=
      (2*84^+0*1:R)%:E*euclidean_lebesgue_measure 0 (euclidean_projection_linear p @` A))%E.
Proof.
move=>A.
have hHalf:(0:R)<1/2 by lra.
have hMass:@euclidean_lebesgue_measure R 1 A= 1%E.
  rewrite /A (@euclidean_closed_ball_normalized_volume R 1 0 (1/2) (ltW hHalf))
    euclidean_unit_ball_volume1 expr1.
  congr (EFin _); lra.
have hAtMost:(@euclidean_lebesgue_measure R 1 A<=1)%E by rewrite hMass.
have [p [hP hFull]]:=structure_projection_line_zero_degree_bound hAtMost.
have hImage:(euclidean_projection_linear p @` A)=
    [set (0:inner_metric_space (@euclidean_inner_productP R 0))].
  apply/seteqP; split.
  - move=>z [a ha <-]; exact:hP a.
  - move=>z ->; exists (0:inner_metric_space (@euclidean_inner_productP R 1)).
    + rewrite /A /metric_closed_ball /= mdistxx; exact:ltW hHalf.
    + by rewrite hP.
have hImageMass:euclidean_lebesgue_measure 0 (euclidean_projection_linear p @` A)= 1%E.
  rewrite hImage /euclidean_lebesgue_measure; exact:point_mass_in.
exists p; by split; last split.
Qed.

(** Source for [structure_projection_nonmeasurable_source_example]:
    an ACTUAL nonmeasurable positive finite-volume subset of the unit
    interval, testing the arbitrary-source assertion of Federer 3.3.7,
    p. 294. Existence follows from the already proved 2.2.4, p. 62;
    the original W is retained in the full numbered conclusion. *)
Example structure_projection_nonmeasurable_source_example (R:realType):
  exists (W:set (inner_metric_space (@euclidean_inner_productP R 1)))
    (p:euclidean_projection_space R 1 0),
    ~measure_measurable (@euclidean_lebesgue_measure R 1) W /\
    (0<@euclidean_lebesgue_measure R 1 W< +oo)%E /\
    (@euclidean_lebesgue_measure R 1 W<=
      (2*84^+0*1:R)%:E*euclidean_lebesgue_measure 0 (euclidean_projection_linear p @` W))%E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose mu:=@euclidean_lebesgue_measure R 1.
pose A:set X:=[set x|forall i,0<x i<1]%R.
have hm:=euclidean_lebesgue_is_measure R 1.
have hMass:mu A= 1%E:=euclidean_unit_cube R 1.
have hPositive:(0<mu A)%E by rewrite hMass lte_fin ltr01.
have hFinite:(mu A< +oo)%E by rewrite hMass ltry.
have [W [hWA hNot]]:=@borel_regular_nonmeasurable_subset R X mu hm
  (euclidean_lebesgue_borel_regular R 1) A (@euclidean_metric_complete R 1)
  (@euclidean_metric_separable R 1) hPositive hFinite
  (fun x _=>@positive_euclidean_singleton_null R 0 x).
have hWPositive:(0<mu W)%E.
  rewrite lt_neqAle (measure_nonnegative hm W) andbT; apply/negP=>/eqP hZero.
  apply:hNot; exact:(@measure_null_measurable R X mu hm W (esym hZero)).
have hAtMost:(mu W<=1)%E by rewrite -hMass; exact:(@measure_mono R X mu hm _ _ hWA).
have hWFinite:(mu W< +oo)%E:=le_lt_trans hAtMost (ltry _).
have [p [hP hFull]]:=structure_projection_line_zero_degree_bound hAtMost.
exists W,p; split; first exact:hNot.
split; first by apply/andP; split.
exact:hFull.
Qed.

(** Source for [structure_projection_unbounded_infinite_image_example]:
    actual whole-line source and infinite projected Lebesgue measure,
    testing the unbounded-source conclusion of Federer 3.3.7,
    p. 294. The actual zero outer measure is purely unrectifiable
    in degree one. The original identity projection and its whole
    original image remain; no finite-source premise is available. *)
Example structure_projection_unbounded_infinite_image_example (R:realType):
  exists p:euclidean_projection_space R 1 1,
    (forall x,euclidean_projection_linear p x=x) /\
    euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` setT)= +oo%E /\
    ((0: \bar R)<=(2*84^+1*1:R)%:E*
      euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` setT))%E.
Proof.
have hp:O_star (linear_id (R_n R 1)).
  exists (linear_id (R_n R 1)); split; by move=>x y.
have [p hP]:=euclidean_projection_linear_complete hp.
pose phi:set (inner_metric_space (@euclidean_inner_productP R 1))-> \bar R:=fun _=>0%E.
have hm:is_measure phi:=@daniell_zero_measure R (inner_metric_space (@euclidean_inner_productP R 1)).
have hStructure:is_structure_measure phi.
  split; first exact:hm.
  by move=>S _ T; rewrite /phi add0e.
have hPure:is_purely_measure_m_unrectifiable phi 1 setT.
  split; first exact:hm.
  by move=>[F [_ [_ hPositive]]]; rewrite /phi ltxx in hPositive.
have hAperture:is_structure_aperture_mass_bound (leqnn 1) phi setT p (1/2) 1.
  move=>x _ r hr s hs hsSigma.
  rewrite /phi euclidean_unit_ball_volume1 !expr1 lee_fin; nra.
have hSigma:=@structure_density_positive_half_bounds R 1 ltr01.
have hFull:=@federer_3_3_7 R 1 1 (leqnn 1) phi setT p (1/2) 1
  hStructure hPure hSigma ltr01 hAperture.
have hImage:(euclidean_projection_linear p @` setT)=setT.
  apply/seteqP; split; first by move=>x _.
  move=>x _; exists x; first exact:I; by rewrite hP.
have hImageMass:euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` setT)= +oo%E.
  rewrite hImage; exact:(@positive_euclidean_whole_volume_infinite R 1 (erefl true)).
exists p; split; first exact:hP.
split; first exact:hImageMass.
exact:hFull.
Qed.
