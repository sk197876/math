(** Federer (1969), 4.1.14, pp. 371–372: shrink
    the open time interval around [0,1] while retaining
    a compact larger closed band. This is the earlier
    compact-neighbourhood argument of 4.1.13, pp. 369–370.
    It supplies a uniform target margin for the smooth
    affine approximation on a fixed source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype normed_module lra.
From Federer Require Import RealMetricBackground RealOpenIntervals
  MetricOpenThickening MetricCompactNeighbourhood CurrentHomotopyUP
  CurrentHomotopyGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [homotopy_parameter_compact_band]: an original
    open parameter interval contains [-r,1+r] for some
    0<r<=1, supporting Federer 4.1.14, pp. 371–372.
    Its original ends may be unbounded. *)
Theorem homotopy_parameter_compact_band (R:realType) (A:set R)
    (hA:@is_homotopy_parameter_interval R A):
  exists r:R,0<r<=1 /\forall t:R,-r<=t<=1+r->A t.
Proof.
have hI:@compact (real_line_metric R) (`[0,1]:set (real_line_metric R)).
  exact:segment_compact.
have hIA:(`[0,1]:set (real_line_metric R)) `<=` A.
  move=>t ht.
  have hBand:0<=t<=1 by move:ht;rewrite /mkset in_itv /=.
  exact:(@current_homotopy_closed_time_band R A hA t hBand).
have[d [hd hTube]]:=@compact_metric_open_thickening R
  [the metricType R of real_line_metric R] (`[0,1]) A hI
  (homotopy_parameter_open hA) hIA.
pose r:=Num.min (d/2) 1.
have hHalf:0<d/2.
  apply:divr_gt0;first exact:hd.
  by rewrite ltr0n.
have hr:0<r by rewrite /r lt_min hHalf ltr01.
have hr1:r<=1 by rewrite /r ge_min lexx orbT.
have hrd:r<d.
  have h:r<=d/2 by rewrite /r ge_min lexx.
  lra.
exists r;split;first by apply/andP;split.
have hZero:(`[0,1]:set (real_line_metric R)) 0 by rewrite /mkset in_itv /= lexx ler01.
have hOne:(`[0,1]:set (real_line_metric R)) 1 by rewrite /mkset in_itv /= lexx ler01.
move=>t /andP[htLow htHigh];apply:hTube.
case:(leP 0 t)=>ht0.
- case:(leP t 1)=>ht1.
  + exists t;first by rewrite /mkset in_itv /= ht0 ht1.
    by rewrite /= mdistxx.
  + exists 1;first exact:hOne.
    rewrite /= real_line_metric_distanceE.
    have hNeg:1-t<=0 by lra.
    rewrite (ler0_norm hNeg);lra.
- exists 0;first exact:hZero.
  rewrite /= real_line_metric_distanceE sub0r normrN (ltr0_norm ht0);lra.
Qed.

(** Source for [homotopy_parameter_symmetric_enlargement]:
    (-r,1+r) is one original allowed open time interval,
    supporting Federer 4.1.14, pp. 371–372. *)
Theorem homotopy_parameter_symmetric_enlargement (R:realType) (r:R):
  0<r->@is_homotopy_parameter_interval R (@real_open_interval R (-r) (1+r)).
Proof.
move=>hr;constructor.
- exact:real_open_interval_open.
- move=>s t u [hs0 hs1] [ht0 ht1] /andP[hsu hut].
  split;lra.
- split;lra.
- split;lra.
Qed.
