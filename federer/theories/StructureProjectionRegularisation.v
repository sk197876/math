(** Federer (1969), 3.3.7, p. 294: construct and justify
    the actual local Borel regularisation of the original image measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeUP StructureApertureMassUP StructureBoundedProjectionBalls
  StructureProjectionBorelMeasure StructureImageRegularisationMass StructureFiniteBallMass
  RectifiableSetUP MetricClosedBalls EuclideanClosedBallCompact EuclideanBallVolume
  EuclideanClosedBallVolume EuclideanLebesgueDimensions TopologicalBorel MeasureUP MeasureBasic
  MeasureRestriction MeasurePushforward MeasureDerivationContext BorelRegularisationUP
  BorelRegularisation BorelRegularMeasureUP RadonMeasureUP StructureEuclideanFiniteRadon.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_bounded_projection_regularisation]: the
    actual psi and every regularity premise in Federer 3.3.7,
    p. 294. Original A lies in a genuine closed source ball, but
    need not be measurable. The local 3.3.6 estimates and an actual
    finite net of original image points prove finite total mass;
    Borel regularity follows from the already sealed Borel-infimum
    operator. The exact original-image mass is retained. No chosen
    regularisation becomes a new global auxiliary object. *)
Theorem structure_bounded_projection_regularisation (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (sigma lam L:R):
  is_structure_measure phi ->is_purely_measure_m_unrectifiable phi m A ->
  0<sigma<1 ->0<lam ->0<=L ->
  A `<=` metric_closed_ball (0:inner_metric_space (@euclidean_inner_productP R n)) L ->
  is_structure_aperture_mass_bound hmn phi A p sigma lam ->
  exists psi:set (inner_metric_space (@euclidean_inner_productP R m))-> \bar R,
    @is_borel_regularisation R
      [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
      (measure_pushforward (euclidean_projection_linear p) (measure_restrict phi A)) psi /\
    is_derivation_measure psi /\
    @is_radon_measure R [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] psi /\
    phi A=psi (euclidean_projection_linear p @` A) /\
    exists delta:R,0<delta /\forall z:inner_metric_space (@euclidean_inner_productP R m), (euclidean_projection_linear p @` A) z ->
      forall rho:R,0<rho ->rho<delta ->
      (psi (metric_closed_ball z rho)<=(2*84^+m*lam)%:E*
        euclidean_lebesgue_measure m (metric_closed_ball z rho))%E.
Proof.
move=>hStructure hPure hSigma hLam hL hSource hAperture.
pose f:inner_metric_space (@euclidean_inner_productP R n)->
  inner_metric_space (@euclidean_inner_productP R m):=euclidean_projection_linear p.
pose mu:set (inner_metric_space (@euclidean_inner_productP R m))-> \bar R:=
  measure_pushforward f (measure_restrict phi A).
have hMu:is_measure mu:=measure_pushforward_is_measure f (measure_restrict_is_measure hStructure.1 A).
pose psi:=@borel_regularisation R
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] mu.
have hRegularisation:@is_borel_regularisation R
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] mu psi:=borel_regularisation_laws mu.
have hPsi:is_measure psi:=borel_regularised_measure_is_measure hMu.
have hBorel B:borel_set B ->measure_measurable mu B.
  exact:(@structure_projection_pushforward_borel_measurable R n m phi A p hStructure B).
have hPsiRegular:@is_borel_regular_measure R
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] psi:=borel_regularised_measure_borel_regular hMu hBorel.
have hImageMass:phi A=psi (f @` A).
  exact:(@structure_image_regularisation_mass R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] phi A f psi
    hStructure.1 hRegularisation).
have hTotal:psi setT=phi A.
  rewrite /psi (@borel_regularised_measure_borel_value R
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] mu hMu setT
    (open_borel_set (@openT [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]))).
  by rewrite /mu /measure_pushforward /measure_restrict preimage_setT setIT.
pose M:=2*L+1.
have hM:0<M by rewrite /M; nra.
have hDiameter x y:A x ->A y ->mdist x y<=M.
  move=>hx hy.
  have hBound:=metric_closed_ball_diameter_bound (hSource x hx) (hSource y hy).
  rewrite /M; lra.
pose delta:=sigma*M/4.
have hNumerator:0<sigma*M:=mulr_gt0 (andP hSigma).1 hM.
have hDelta:0<delta by rewrite /delta divr_gt0 // ltr0n.
have hLocal (z:inner_metric_space (@euclidean_inner_productP R m)):(f @` A) z ->forall rho:R,0<rho ->rho<delta ->
    (psi (metric_closed_ball z rho)<=(2*84^+m*lam)%:E*
      euclidean_lebesgue_measure m (metric_closed_ball z rho))%E.
  move=>[a ha <-] rho hRho hSmall.
  rewrite /psi (@borel_regularised_measure_borel_value R
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] mu hMu
    (metric_closed_ball (f a) rho) (closed_borel_set (@metric_closed_ball_closed R (inner_metric_space (@euclidean_inner_productP R m)) (f a) rho))).
  exact:(@structure_bounded_projection_ball_mass R n m hmn phi A p sigma lam M
    hPure hSigma hLam hM hDiameter hAperture a ha rho hRho hSmall).
pose K:=metric_closed_ball (f 0) L.
have hCompact:compact K:=@euclidean_closed_metric_ball_compact R m (f 0) L.
have hImageInside:(f @` A) `<=` K.
  move=>z [a ha <-]; apply:le_trans (euclidean_projection_nonexpanding p 0 a) (hSource a ha).
pose r:=delta/2.
have hr:0<r by rewrite /r divr_gt0 // ltr0n.
have hrDelta:r<delta by rewrite /r; lra.
pose b:=(2*84^+m*lam)*euclidean_unit_ball_volume R m*r^+m.
have hTwo:(0:R)<2 by rewrite ltr0n.
have hPower:0<(84:R)^+m by apply:exprn_gt0; rewrite ltr0n.
have hCoefficient:0<2*84^+m*lam:=mulr_gt0 (mulr_gt0 hTwo hPower) hLam.
have hb:0<=b.
  rewrite /b; apply:mulr_ge0; last by apply:exprn_ge0; exact:ltW hr.
  exact:mulr_ge0 (ltW hCoefficient) (ltW (euclidean_unit_ball_volumeE R m).2).
have hBall (z:inner_metric_space (@euclidean_inner_productP R m)):(f @` A) z ->(psi (metric_closed_ball z r)<=b%:E)%E.
  move=>hz; have hBound:=hLocal z hz r hr hrDelta.
  by rewrite (@euclidean_closed_ball_normalized_volume R m z r (ltW hr)) -EFinM /b mulrA in hBound.
have hFiniteImage:=@structure_compact_subset_ball_mass_finite R
  (inner_metric_space (@euclidean_inner_productP R m)) (f 0) (f @` A) K psi b r
  hCompact hImageInside hPsi hr hb hBall.
have hFiniteTotal:(psi setT< +oo)%E by rewrite hTotal hImageMass.
have hClass:is_derivation_measure psi.
  constructor; [exact:hPsi|exact:hPsiRegular|].
  move=>B _; apply:le_lt_trans _ hFiniteTotal.
  exact:(@measure_mono R _ psi hPsi B setT (subsetT B)).
have hRadon:=@structure_euclidean_finite_borel_radon R m psi hPsi hPsiRegular hFiniteTotal.
exists psi; split; first exact:hRegularisation.
split; first exact:hClass.
split; first exact:hRadon.
split; first exact:hImageMass.
exists delta; by split.
Qed.
