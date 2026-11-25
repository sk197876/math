(** Federer (1969), 3.3.19, p. 305: original
    finite-cone masses bound the actual ball densities
    of the restriction to the original infinite cone. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  EuclideanProjectionSpace StructureProjectionKernel StructureCone StructureConeBasic
  MeasureUP MeasureBasic MeasureRestriction MetricDensities EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Ball.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).

(** Source for [extended_positive_cone_rescale]: exact
    extended-real division by the positive factors 2r
    and 2s equals division by 4rs, including infinite
    masses. This supports 3.3.19, p. 305. *)
Lemma extended_positive_cone_rescale (q: \bar R) (r s:R):
  0<r ->0<s ->(q/(2* r)%:E/(2* s)%:E= q/(4* r* s)%:E)%E.
Proof.
move=>hr hs.
have hFirst:0<2* r by lra.
have hSecond:0<2* s by lra.
have hProduct:0<4* r* s by nra.
rewrite !inver (gt_eqF hFirst) (gt_eqF hSecond) (gt_eqF hProduct) -muleA -EFinM.
apply:(congr1 (fun t:R=>(q* t%:E)%E)).
have hrN:r!=0 by rewrite gt_eqF.
have hsN:s!=0 by rewrite gt_eqF.
field;by rewrite hrN hsN.
Qed.

(** Source for [structure_cone_original_ball_ratio_bound]:
    an original finite cone of radius 2rs lies in the
    original infinite cone intersected with the actual closed
    ball of radius 2rs. Thus its normalized mass yields
    the displayed actual metric-density bound in 3.3.19,
    p. 305, for every positive r and s. *)
Theorem structure_cone_original_ball_ratio_bound
    (mu:set E->\bar R) (A:set E) (p:euclidean_projection_space R 2 1)
    (a:E) (r s L:R):
  is_measure mu ->0<r ->0<s ->
  (L%:E<=mu (A `&` structure_cone (structure_projection_kernel (leqnSn 1) p)
    a (2* r* s)%:E s)/(2* r)%:E)%E ->
  ((L/(2* s))%:E<=metric_ball_density 1
    (measure_restrict mu (A `&` structure_cone (structure_projection_kernel (leqnSn 1) p) a +oo s))
    a (2* r* s))%E.
Proof.
move=>hMu hr hs hLower.
pose K:= structure_projection_kernel (leqnSn 1) p.
pose T:= A `&` structure_cone K a (2* r* s)%:E s.
pose D:=(A `&` structure_cone K a +oo s) `&` metric_closed_ball a (2* r* s).
have hSubset:T `<=` D.
  move=>x [hxA hxCone];split.
  - split=>//;exact:(structure_cone_radius_mono (leey _) hxCone).
  - have hRadius:= @structure_cone_norm_bound R 2 1 K a x (2* r* s)%:E s hxCone.
    rewrite lte_fin -inner_metric_distanceE (metric_sym x a) in hRadius.
    exact:ltW hRadius.
have hMass:= @measure_mono R E mu hMu T D hSubset.
have hSecond:0<2* s by lra.
have hSecondInverse:(0<=((2* s)%:E)^-1)%E by rewrite inve_ge0 lee_fin;exact:ltW hSecond.
have hScaled:= lee_wpmul2r hSecondInverse hLower.
rewrite (extended_positive_cone_rescale (mu T) hr hs) in hScaled.
have hReal:((L%:E/(2* s)%:E)=(L/(2* s))%:E)%E by rewrite inver (gt_eqF hSecond) -EFinM.
rewrite hReal in hScaled.
have hDenominator:0<4* r* s by nra.
have hInverse:(0<=((4* r* s)%:E)^-1)%E by rewrite inve_ge0 lee_fin;exact:ltW hDenominator.
have hCompared:= lee_wpmul2r hInverse hMass.
have hIdentity:2*(2* r* s)= 4* r* s by ring.
rewrite /metric_ball_density /measure_restrict euclidean_unit_ball_volume1 expr1 hIdentity.
exact:(le_trans hScaled hCompared).
Qed.
End Ball.
