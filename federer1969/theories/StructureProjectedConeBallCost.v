(** Federer (1969), 3.3.9, pp. 295–296: compare the original
    cone cost with an actual projected closed-ball measure quotient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureCone StructureProjectionKernel StructureConeMetric StructureConeDensityUP
  StructureWeightedQuotient MetricClosedBalls EuclideanClosedBallVolume EuclideanBallVolume
  EuclideanLebesgueDimensions TopologicalBorel MeasureUP MeasureBasic MeasureRestriction MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projected_cone_ball_cost]: the original
    inclusion X(x,r,ker p,s) subset p inverse U[p(x),rs] in Federer
    3.3.9, p. 295, and its normalized ball quotient on p. 296.
    Both centres and projection are original. Actual positive ball
    normalization supplies the exact alpha(m) factor, including
    degree zero; no separate cone-inclusion or quotient premise. *)
Theorem structure_projected_cone_ball_cost (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m)
    (psi:set (inner_metric_space (@euclidean_inner_productP R m))->\bar R)
    (x:inner_metric_space (@euclidean_inner_productP R n)) (r s:R):
  is_measure phi ->is_measure psi ->
  (forall S,borel_set S ->psi S=measure_pushforward (euclidean_projection_linear p) (measure_restrict phi A) S) ->
  0<r ->0<s ->
  (structure_cone_cost hmn phi A (x,p) r s<=
    (euclidean_unit_ball_volume R m)%:E*
    (psi (metric_closed_ball (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m)) (r*s))/
      euclidean_lebesgue_measure m (metric_closed_ball (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m)) (r*s))))%E.
Proof.
move=>hPhi hPsi hValue hr hs.
pose f:inner_metric_space (@euclidean_inner_productP R n)->
  inner_metric_space (@euclidean_inner_productP R m):=euclidean_projection_linear p.
pose B:=metric_closed_ball (f x) (r*s).
have hSub:(A `&` structure_cone (structure_projection_kernel hmn p) x r%:E s) `<=`
    (A `&` f @^-1` B).
  move=>y [hy hCone]; split=>//.
  have [hRadius hAngle]:=(structure_projection_cone_metricE hmn p x y r%:E hs).1 hCone.
  have hNear:mdist x y<r by move:hRadius; rewrite lte_fin.
  rewrite /B /metric_closed_ball /=.
  apply:ltW; apply:lt_trans hAngle _.
  by rewrite [r*s]mulrC ltr_pM2l.
have hMass:(phi (A `&` structure_cone (structure_projection_kernel hmn p) x r%:E s)<=psi B)%E.
  rewrite (hValue B (closed_borel_set (@metric_closed_ball_closed R
    (inner_metric_space (@euclidean_inner_productP R m)) (f x) (r*s)))).
  exact:(@measure_mono R _ phi hPhi _ _ hSub).
pose d:=euclidean_unit_ball_volume R m*(r*s)^+m.
pose w:=(r^-1)^+m*(s^-1)^+m.
have hAlpha:0<euclidean_unit_ball_volume R m:=(euclidean_unit_ball_volumeE R m).2.
have hDen:0<d by rewrite /d mulr_gt0 // exprn_gt0 // mulr_gt0.
have hW:0<w by rewrite /w mulr_gt0 // exprn_gt0 // invr_gt0.
have hCancel:d*w=euclidean_unit_ball_volume R m.
  rewrite /d /w exprMn !exprVn.
  field; by rewrite ?expf_neq0 ?gt_eqF.
have hCoefficient:d*w<=euclidean_unit_ball_volume R m by rewrite hCancel.
have hBound:=@structure_weighted_quotient_upper R
  (phi (A `&` structure_cone (structure_projection_kernel hmn p) x r%:E s))
  (psi B) d w (euclidean_unit_ball_volume R m)
  (measure_nonnegative hPsi B) hMass hDen hW hCoefficient.
rewrite (@euclidean_closed_ball_normalized_volume R m (f x) (r*s) (ltW (mulr_gt0 hr hs))).
rewrite /structure_cone_cost -muleA -EFinM -/w -/d.
exact:hBound.
Qed.
