(** Supporting Federer (1969), 2.10.14, p. 177: the atom of the measure
    induced by arc length equals alpha_++alpha_-. Use the independent
    interval construction of 2.10.7, p. 174. Every interval covering x costs
    at least s(x+)-s(x-); arbitrarily short intervals give the reverse
    bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength CurveJumpArcLength
  CurveOneSidedJumpUP NonnegativeSum StieltjesCaratheodoryUP StieltjesCaratheodory
  StieltjesCaratheodoryConsequences StieltjesIntervalBounds MetricScaleEnvelopeUP
  CaratheodoryLimitUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [arc_length_stieltjes_singleton_lower]: supporting
    lower atom bound in 2.10.14, p. 177. Any countable
    interval cover of {x} contains an interval straddling x;
    its raw increment cost dominates the entire scalar jump. *)
Lemma arc_length_stieltjes_singleton_lower (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : curve_locally_finite_variation g ->
  ((arc_length_right g x-arc_length_left g x)%R)%:E<=
    stieltjes_caratheodory_measure (arc_length g) [set x].
Proof.
move=> hg.
pose s := arc_length g.
pose nu := stieltjes_caratheodory_scale s 1.
have hn := stieltjes_caratheodory_scale_specification s 1.
have hlow : ((arc_length_right g x-arc_length_left g x)%R)%:E<=nu [set x].
  apply: (metric_scale_envelope_greatest hn)=> G hG hdiam hcover.
  have [j hj hx] := hcover x (erefl x).
  move: hx; rewrite /stieltjes_interval_set /= in_itv /= => /andP[hax hxb].
  have hleft := @arc_length_le_left R Y g hg (val j).1 x hax.
  have hright := @arc_length_right_le R Y g hg x (val j).2 hxb.
  have hc : ((arc_length_right g x-arc_length_left g x)%R)%:E<=stieltjes_interval_cost s j.
    rewrite /stieltjes_interval_cost lee_fin /s; lra.
  exact: le_trans hc (@nonnegative_sum_term R (stieltjes_open_intervals R) G
    (stieltjes_interval_cost s) j hj).
apply: le_trans hlow _.
exact: (@caratheodory_limit_upper R [the metricType R of real_line_metric R]
  (stieltjes_open_intervals R) (@stieltjes_interval_set R) (stieltjes_interval_cost s)
  (stieltjes_caratheodory_measure s) (stieltjes_caratheodory_specification s) [set x] 1 nu lte01 hn).
Qed.

(** Source for [arc_length_stieltjes_singleton_upper]: supporting
    upper atom bound in 2.10.14, p. 177. Intervals with
    endpoints approaching x from opposite sides have raw costs
    approaching s(x+)-s(x-), by 2.5.16, p. 109. *)
Lemma arc_length_stieltjes_singleton_upper (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : curve_locally_finite_variation g ->
  stieltjes_caratheodory_measure (arc_length g) [set x]<=
    ((arc_length_right g x-arc_length_left g x)%R)%:E.
Proof.
move=> hg; apply/lee_addgt0Pr=> e he; rewrite -EFinD.
have he2 : (0<e/2)%R by rewrite divr_gt0 // ltr0n.
have [u hux hu] := arc_length_left_adherent hg x he2.
have [v hxv hv] := arc_length_right_adherent hg x he2.
have hs := @arc_length_monotone R Y g hg.
have hm := stieltjes_caratheodory_is_measure hs.
have hsub : [set x] `<=` (`]u,v[ : set (real_line_metric R)).
  by move=> t ->; rewrite /= in_itv /= hux hxv.
apply: le_trans (measure_mono hm hsub) _.
apply: le_trans (stieltjes_caratheodory_interval_bound hs (lt_trans hux hxv)) _.
rewrite lee_fin; lra.
Qed.

(** Source for [arc_length_stieltjes_singleton]: direct supporting atom
    formula s(x+)-s(x-) for 2.10.14, p. 177, consistent with the
    induced-measure atom law of 2.5.17, p. 111 *)
Theorem arc_length_stieltjes_singleton (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : curve_locally_finite_variation g ->
  stieltjes_caratheodory_measure (arc_length g) [set x]=
    ((arc_length_right g x-arc_length_left g x)%R)%:E.
Proof.
move=> hg; apply/eqP; rewrite eq_le (arc_length_stieltjes_singleton_upper x hg) /=.
exact: arc_length_stieltjes_singleton_lower x hg.
Qed.

(** Source for [curve_arc_length_atom_jump_sum]: supporting
    atomic contribution alpha_+(x)+alpha_-(x) in 2.10.14,
    p. 177. Both one-sided upper limits are finite for a
    locally BV curve, even if the target is incomplete. *)
Corollary curve_arc_length_atom_jump_sum (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : curve_locally_finite_variation g ->
  stieltjes_caratheodory_measure (arc_length g) [set x]=
    curve_right_jump_size g x+curve_left_jump_size g x.
Proof.
move=> hg; rewrite (arc_length_stieltjes_singleton x hg)
  (curve_right_jump_arc_length x hg) (curve_left_jump_arc_length x hg) -EFinD.
congr (_%:E); lra.
Qed.
