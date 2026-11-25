(** Federer (1969), 4.1.13, pp. 369–370: an open
    neighbourhood of the closed time interval contains an
    open interval containing both endpoints. This supports
    the source-neighbourhood step without a uniform image
    assumption beyond the actual compact time cylinder. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology num_normedtype normed_module lra.
From Federer Require Import RealMetricBackground RealOpenIntervals
  MetricOpenThickening MetricCompactNeighbourhood CurrentHomotopyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [homotopy_parameter_neighbourhood]: the open
    time interval needed by the homotopy invoked in Federer
    4.1.13, pp. 369–370. The compact interval has
    a positive uniform radius inside any open neighbourhood. *)
Theorem homotopy_parameter_neighbourhood (R:realType)
    (W:set (real_line_metric R)):
  open W->(`[0,1]:set (real_line_metric R)) `<=` W->
  exists A:set R,@is_homotopy_parameter_interval R A /\A `<=` W.
Proof.
move=>hW hIW.
have hI:@compact (real_line_metric R) (`[0,1]:set (real_line_metric R)).
  exact:segment_compact.
have [r [hr hTube]]:=@compact_metric_open_thickening R
  [the metricType R of real_line_metric R] (`[0,1]) W hI hW hIW.
pose A:=@real_open_interval R (-r) (1+r).
have hA:@is_homotopy_parameter_interval R A.
  constructor.
  - exact:real_open_interval_open.
  - move=>s t u [hs0 hs1] [ht0 ht1] /andP [hsu hut].
    by split;lra.
  - by split;lra.
  - by split;lra.
exists A;split;first exact:hA.
have hZero:(`[0,1]:set (real_line_metric R)) 0 by rewrite /mkset in_itv /= lexx ler01.
have hOne:(`[0,1]:set (real_line_metric R)) 1 by rewrite /mkset in_itv /= lexx ler01.
move=>t [ht0 ht1];apply:hTube.
case:(leP 0 t)=>hNonnegative.
- case:(leP t 1)=>hBefore.
  + exists t;first by rewrite /mkset in_itv /= hNonnegative hBefore.
    by rewrite /= mdistxx.
  + exists 1;first exact:hOne.
    rewrite /= real_line_metric_distanceE.
    have hNegative:1-t<=0 by lra.
    rewrite (ler0_norm hNegative);lra.
- exists 0;first exact:hZero.
  rewrite /= real_line_metric_distanceE sub0r normrN (ltr0_norm hNonnegative);lra.
Qed.
