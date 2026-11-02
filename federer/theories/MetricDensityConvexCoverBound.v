(** Federer (1969), 3.2.26(2), p. 261: unit
    upper density and the local thin-cover estimates produce
    a fine ball family. Vitali selection then bounds each
    cutoff cost by (1+delta)^2 times the source mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MetricClosedBalls MetricDiameterUP MetricDiameter
  MetricDensities MetricDensityNumericalBounds PositiveRadiusLimits PositiveRadiusLimitBounds
  EuclideanBallVolume MeasureUP BorelRegularMeasureUP CoveringRelationUP CoveringRelationFineness
  CenteredBallRelations MetricScaleEnvelopeUP VitaliMetricCoverCostBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_density_convex_cover_cutoff_bound]: the
    ball selection and summed-cost estimate in 3.2.26(2),
    p. 261. Only arbitrarily small balls above the
    density threshold are needed. The local generator hypotheses
    are proved from actual differentiable charts separately;
    neither a rectifiable-measure equality nor a prescribed
    measurable tangent field is assumed by this covering argument. *)
Theorem metric_density_convex_cover_cutoff_bound (R:realType) (X:metricType R) m
    (J:choiceType) (j0:J) (S:J->set X) (c:J->\bar R)
    (delta: \bar R) (cutoff d:R) (mu nu:set X->\bar R) (W Z:set X):
  is_measure mu ->is_borel_regular_measure mu ->
  is_vitali_relation mu (@centered_closed_ball_relation R X) ->
  is_metric_scale_envelope S c delta nu ->(forall j,0<=c j) ->
  (0<cutoff)%R ->cutoff%:E<=delta ->(0<d)%R ->
  mu (W `\` Z)=0 ->(forall A,A `<=` W ->mu A=0 ->nu A=0) ->
  (forall w,Z w ->upper_metric_density m mu w= 1) ->
  (forall w,Z w ->exists s:R,(0<s)%R /\forall r:R,(0<r<s)%R ->exists j,
    W `&` metric_closed_ball w r `<=` S j /\
    extended_metric_diameter (S j)<=(r*3)%R%:E /\
    c j<=((1+d)*euclidean_unit_ball_volume R m*r^+m)%R%:E) ->
  nu W<=((1+d)^+2)%R%:E*mu setT.
Proof.
move=>hMu hRegular hVitali hNu hc hCutoff hCutoffDelta hd hOutside hNull hDensity hLocal.
pose a:R:=((1+d)^+2)%R.
pose C0:R:=(1+d)%R.
pose q:R:=(C0^-1)%R.
have hC0:(0<C0)%R by rewrite /C0; lra.
have hC0Ne:C0!=0%R by rewrite gt_eqF.
have hA:(0<a)%R by rewrite /a exprn_gt0.
have hQ:(q<1)%R by rewrite /q invf_lt1 // /C0; lra.
pose C (w:X) (B:set X):=exists r:R,(0<r)%R /\B=metric_closed_ball w r /\
  exists j,W `&` B `<=` S j /\extended_metric_diameter (S j)<=delta /\c j<=a%:E*mu B.
have hCV w B:C w B ->centered_closed_ball_relation w B.
  move=>[r [hr [hB _]]]; by exists r.
have hFine w:Z w ->covering_relation_fine_at C w.
  move=>hw; apply:(covering_relation_fine_iff_small_diameter C w).2=>e he.
  have [s [hs hCover]]:=hLocal w hw.
  pose small:R:=Num.min s (Num.min (cutoff/4)%R (e/4)%R).
  have hSmall:(0<small)%R by rewrite /small !lt_min hs !divr_gt0 // ltr0n.
  have hThreshold:q%:E<positive_radius_upper_limit (metric_ball_density m mu w).
    change (is_true (q%:E<upper_metric_density m mu w)).
    by rewrite (hDensity w hw) lte_fin.
  have [r [hRadius hLarge]]:=@positive_radius_upper_large_value R
    (metric_ball_density m mu w) q%:E small hThreshold hSmall.
  have hr:(0<r)%R:=(andP hRadius).1.
  have hRs:(r<s)%R.
    apply:lt_le_trans (andP hRadius).2 _; by rewrite /small ge_min lexx.
  have hRcut:(r<cutoff/4)%R.
    apply:lt_le_trans (andP hRadius).2 _.
    have hMin:(Num.min (cutoff/4)%R (e/4)%R<=cutoff/4)%R by rewrite ge_min lexx.
    apply:le_trans _ hMin.
    by rewrite /small ge_min lexx orbT.
  have hRe:(r<e/4)%R.
    apply:lt_le_trans (andP hRadius).2 _.
    have hMin:(Num.min (cutoff/4)%R (e/4)%R<=e/4)%R by rewrite ge_min lexx orbT.
    apply:le_trans _ hMin.
    by rewrite /small ge_min lexx orbT.
  have hRsPositive:(0<r<s)%R by apply/andP; split.
  have [j [hCovered [hDiameter hCost]]]:=hCover r hRsPositive.
  have hSize:extended_metric_diameter (S j)<=delta.
    apply:le_trans hDiameter _; apply:le_trans _ hCutoffDelta.
    rewrite lee_fin; lra.
  have hMass:=@metric_ball_density_value_large R X m mu w r q hr hLarge.
  have hIdentity:a%:E*((q*(euclidean_unit_ball_volume R m*r^+m))%R%:E)=
      ((1+d)*euclidean_unit_ball_volume R m*r^+m)%R%:E.
    rewrite -EFinM; congr (_%:E).
    have hCancel:((C0*C0)*C0^-1=C0)%R.
      by rewrite -mulrA (mulfV hC0Ne) mulr1.
    change (a*(q*(euclidean_unit_ball_volume R m*r^+m))=
      C0*euclidean_unit_ball_volume R m*r^+m)%R.
    by rewrite /a -/C0 expr2 /q mulrA hCancel mulrA.
  have hBudget:c j<=a%:E*mu (metric_closed_ball w r).
    apply:le_trans hCost _; rewrite -hIdentity.
    exact:(lee_wpmul2l (lee_tofin (ltW hA)) (ltW hMass)).
  exists (metric_closed_ball w r); split.
  - exists r; split; first exact hr; split; first reflexivity.
    exists j; by split; last split.
  - have hBallDiam:extended_metric_diameter (metric_closed_ball w r)<=(r+r)%R%:E.
      apply:(metric_diameter_least (extended_metric_diameter_specification _)).
      + rewrite lee_fin; exact:addr_ge0 (ltW hr) (ltW hr).
      + move=>x y hx hy; rewrite lee_fin; exact:metric_closed_ball_diameter_bound hx hy.
    apply:le_lt_trans hBallDiam _; rewrite lte_fin; lra.
apply:(@vitali_metric_cover_cost_bound R X J j0 S c delta mu nu W Z
  (@centered_closed_ball_relation R X) C a hMu hRegular hVitali hNu hc hA hOutside hNull hCV hFine).
move=>w B [r [hr [hB hJ]]]; exact hJ.
Qed.
