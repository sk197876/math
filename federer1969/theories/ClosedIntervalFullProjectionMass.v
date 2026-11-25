(** Federer (1969), 3.3.20, p. 307: a closed projection fills its root precisely at full length. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricClosedBalls MetricOpenShrinking
  LebesgueScalarMeasure EuclideanLebesgueBoxes MeasureUP MeasureBasic MeasureFiniteAdditivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_interval_subset_full_length]: supporting
    equivalence c_u=1 with the full root projection in 3.3.20,
    p. 307. Every proper closed subset of a nondegenerate original
    root interval misses a positive closed subinterval. Actual scalar
    length and disjoint finite addition exclude equal full length. *)
Theorem closed_interval_subset_full_length (R:realType) (a b:R)
    (C:set (real_line_metric R)):
  a<b ->closed C ->C `<=` `[a,b] ->
  (lebesgue_scalar_measure C=(b-a)%:E <->C=`[a,b]).
Proof.
move=>hab hClosed hSub;split;last by move=>->;exact:lebesgue_scalar_segment (ltW hab).
move=>hMass;apply/seteqP;split;first exact:hSub.
move=>x hx;case:(pselect (C x))=>//hNo;exfalso.
have [r [hr hBall]]:=@metric_open_contains_closed_ball R [the metricType R of real_line_metric R]
  (~` C) x (closed_openC hClosed) hNo.
have /andP[hax hxb]:a<=x<=b by move:hx;rewrite /= in_itv.
pose l:=Num.max a (x-r/2).
pose h:=Num.min b (x+r/2).
have hLH:l<h.
  rewrite /l /h lt_min !gt_max;apply/andP;split;apply/andP;split;lra.
have hSegment:(`[l,h]:set (real_line_metric R)) `<=` `[a,b].
  move=>y hy;move:hy;rewrite /l /h /= in_itv /= ge_max le_min=>/andP[/andP[h0 h1] /andP[h2 h3]].
  rewrite /= in_itv /=;by apply/andP.
have hMissing y:(`[l,h]:set (real_line_metric R)) y ->~C y.
  move=>hy;apply:hBall.
  move:hy;rewrite /l /h /= in_itv /= ge_max le_min=>/andP[/andP[h0 h1] /andP[h2 h3]].
  change (is_true (mdist x y<=r)).
  rewrite real_line_metric_distanceE ler_norml;apply/andP;split;lra.
have hDisjoint y:(`[l,h]:set (real_line_metric R)) y ->C y ->False
  by move=>hy;exact:hMissing y hy.
have hUnion:(`[l,h] `|` C) `<=` (`[a,b]:set (real_line_metric R))
  by move=>y [hy|hy];[exact:hSegment y hy|exact:hSub y hy].
have hBound:=measure_mono (lebesgue_scalar_is_measure R) hUnion.
rewrite (measure_disjoint_union (lebesgue_scalar_segment_measurable l h) hDisjoint)
  (lebesgue_scalar_segment (ltW hLH)) hMass (lebesgue_scalar_segment (ltW hab)) -EFinD lee_fin in hBound.
lra.
Qed.
