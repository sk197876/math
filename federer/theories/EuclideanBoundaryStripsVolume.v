(** Federer (1969), 3.2.43, printed p. 278:
    disjoint measurable exterior and interior strips give
    the actual boundary tube-volume comparison. All original
    sets and possibly infinite strip volumes are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanBallVolume MinkowskiContents MetricOpenThickening
  EuclideanBoundaryStripsGeometry EuclideanExteriorStripBoundaryTube TopologicalBorel MeasureUP MeasureBasic
  MeasureFiniteClosure MeasureFiniteAdditivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_boundary_strip_volume_sum]: direct
    volume consequence of the first sentence in the proof
    of Federer 3.2.43, p. 278. Actual measurability and
    disjointness precede finite additivity. No finite mass,
    source measurability or rectifiability premise is imposed. *)
Lemma euclidean_boundary_strip_volume_sum (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  (@euclidean_lebesgue_measure R n (metric_open_thickening S r `\` closure S)+
    @euclidean_lebesgue_measure R n (interior S `\` (~`metric_open_thickening (~`S) r))<=
    @euclidean_lebesgue_measure R n (metric_open_thickening (closure S `\` interior S) r))%E.
Proof.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose A:=metric_open_thickening S r `\` closure S.
pose B:=interior S `\` (~`metric_open_thickening (~`S) r).
have hm:=euclidean_lebesgue_is_measure R n.
have hAMeas:measure_measurable mu A.
  apply:(@measure_measurable_difference R E mu hm).
  - apply:euclidean_borel_measurable; apply:open_borel_set; exact:metric_open_thickening_open.
  - apply:euclidean_borel_measurable; apply:closed_borel_set; exact:closed_closure.
have hDisjoint:forall x,A x ->B x ->False:=@euclidean_boundary_strips_disjoint R n S r.
have hUnion:A `|` B `<=` metric_open_thickening (closure S `\` interior S) r.
  move=>x [hx|hx].
  - exact:(@euclidean_exterior_strip_boundary_tube R n S r x hx).
  - exact:(@euclidean_interior_strip_boundary_tube R n S r x hx).
rewrite -(@measure_disjoint_union R E mu A B hAMeas hDisjoint).
exact:(@measure_mono R E mu hm _ _ hUnion).
Qed.

(** Source for [euclidean_boundary_two_strip_quotient_bound]:
    supporting codimension-one normalization of the preceding
    comparison in Federer 3.2.43, p. 278. The actual normal
    ball coefficient is alpha(1)=2. Both source strip lower
    constants are finite, while every actual volume may be
    infinite. Only the positive radius is cancelled. *)
Lemma euclidean_boundary_two_strip_quotient_bound (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) (r a b:R):
  0<r ->
  ((a*r)%:E<=@euclidean_lebesgue_measure R k.+1
    (metric_open_thickening S r `\` closure S))%E ->
  ((b*r)%:E<=@euclidean_lebesgue_measure R k.+1
    (interior S `\` (~`metric_open_thickening (~`S) r)))%E ->
  (((a+b)/2)%:E<=minkowski_tube_quotient k (closure S `\` interior S) r)%E.
Proof.
move=>hr hA hB.
have hSum:=leeD hA hB.
rewrite -EFinD -mulrDl in hSum.
have hVolume:=euclidean_boundary_strip_volume_sum S r.
have hBound:=le_trans hSum hVolume.
have hTwo:0<(2:R) by rewrite ltr0n.
have hDen:0<2*r:=mulr_gt0 hTwo hr.
rewrite /minkowski_tube_quotient subSnn euclidean_unit_ball_volume1 expr1
  inver (gt_eqF hDen) (lee_pdivlMr _ _ hDen) -EFinM.
have hCancel:((a+b)/2)*(2*r)=(a+b)*r by field.
by rewrite hCancel.
Qed.
