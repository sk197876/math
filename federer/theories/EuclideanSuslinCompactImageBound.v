(** Federer (1969), 3.2.37, p. 274: projected volumes are
    approximated on compact subsets of the original Borel pieces.
    The supporting form allows any continuous Euclidean-valued map
    on a Suslin subset of a complete separable metric source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanClosedBallCompact CompleteMetricUP SuslinSetUP
  SuslinCompactImageApproximation MeasureUP MeasureBasic MeasureRestriction
  BorelRegularMeasureUP BorelRegularRestriction MetricClosedBalls TopologicalBorel
  MeasurableBallRadialContinuity RadialMassSupremum ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_suslin_compact_image_mass_bound]: the
    compact source approximation required for the supremum in
    Federer 3.2.37, p. 274. Compact target balls make the pruning
    measure finite. Their independent radial exhaustion restores
    infinite original image masses; no finite source mass, Borel
    source or selected measurable inverse is required. *)
Theorem euclidean_suslin_compact_image_mass_bound (R:realType)
    (X:metricType R) k
    (f:X->inner_metric_space (@euclidean_inner_productP R k))
    (S:set X) (b:R):
  is_complete_metric_space X ->(exists D:set X,countable D /\ dense D) ->
  continuous f ->is_suslin_set R S ->
  (forall K,compact K ->K `<=` S ->@euclidean_lebesgue_measure R k (f @` K)<=b%:E) ->
  @euclidean_lebesgue_measure R k (f @` S)<=b%:E.
Proof.
move=>hX hSep hf hS hBound.
pose Y:=[the metricType R of inner_metric_space (@euclidean_inner_productP R k)].
pose mu:=@euclidean_lebesgue_measure R k.
have hm:=euclidean_lebesgue_is_measure R k.
have hr:=euclidean_lebesgue_borel_regular R k.
have hBall r:borel_set (@metric_closed_ball R Y (0%R:Y) r).
  exact:(@closed_borel_set Y _ (@metric_closed_ball_closed R Y (0%R:Y) r)).
have hTruncated (r:R):mu ((f @` S) `&` @metric_closed_ball R Y (0%R:Y) r)<=b%:E.
  pose B:=@metric_closed_ball R Y (0%R:Y) r.
  pose nu:=measure_restrict mu B.
  have hn:is_measure nu:=measure_restrict_is_measure hm B.
  have hRegular:is_borel_regular_measure nu:=borel_regular_restrict_borel hm hr (hBall r).
  have hFinite:nu setT< +oo.
    rewrite /nu /measure_restrict setIT.
    exact:(@euclidean_compact_finite R k B
      (@euclidean_closed_metric_ball_compact R k (0%R:Y) r)).
  have hApprox:nu (f @` S)<=b%:E.
    apply:(@extended_upper_bound_from_scaled_errors R _ b 1%R ler01)=>e he.
    have [K [hK [hKS hLoss]]]:=@finite_measure_suslin_compact_image_approximation R X Y f nu S e
      hX hSep (@metric_hausdorff R Y) hf hn hRegular hFinite hS he.
    have hImage:nu (f @` K)<=mu (f @` K).
      apply:(@measure_mono R Y mu hm)=>y [_ hy]; exact:hy.
    have hCost:=le_trans hLoss (le_trans hImage (hBound K hK hKS)).
    have hError:nu (f @` S)<=b%:E+(e/2)%:E by rewrite -leeBlDr.
    apply:le_trans hError _; rewrite -EFinD lee_fin mul1r lerD2l.
    have h2:(0<(2:R))%R by rewrite ltr0n.
    rewrite ler_pdivrMr //; nra.
  by rewrite /nu /measure_restrict setIC in hApprox.
have hRadial:=@measurable_ball_radial_continuity R Y mu 0%R (f @` S) hm
  (fun r=>borel_regular_borel_measurable hm hr (hBall r)).
rewrite leNgt; apply/negP=>hLarge.
have [r hR]:=hRadial.1 b%:E hLarge.
have hr1:(r<r+1)%R by rewrite ltrDl ltr01.
have hBad:=lt_le_trans (hR ((r+1)%R) hr1) (hTruncated ((r+1)%R)).
by rewrite ltxx in hBad.
Qed.
