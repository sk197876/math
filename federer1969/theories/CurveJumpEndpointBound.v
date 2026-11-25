(** Federer (1969), 2.10.14, p. 177: supporting endpoint estimate with the
    actual extended-real one-sided upper limits. A finite numerical budget
    makes every eligible term finite; its real representative can then be
    used in the bridge estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveOneSidedJumpUP CurveJumpBudget
  CurveEndpointJumpEstimate HausdorffLength NonnegativeSum NonnegativeSumSupport
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_endpoint_jump_budget_bound]: supporting
    endpoint estimate in 2.10.14, p. 177, without continuity
    or bounded variation. The exact ranges are [a,b) for the
    right jumps and (a,b] for the left jumps. *)
Theorem curve_endpoint_jump_budget_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : (a<b)%R ->
  curve_interval_jump_budget g a b< +oo ->
  (mdist (g a) (g b))%:E<=@hausdorff_length R Y (g @` `[a,b])+
    curve_interval_jump_budget g a b.
Proof.
move=> hab hfin.
have hR0 := @measure_nonnegative R [the choiceType of real_line_metric R] _
  (curve_jump_measure_is_measure g true) `[a,b[.
have hL0 := @measure_nonnegative R [the choiceType of real_line_metric R] _
  (curve_jump_measure_is_measure g false) `]a,b].
have hR : curve_jump_measure g true `[a,b[< +oo.
  exact: le_lt_trans (lee_paddr hL0 (lexx _)) hfin.
have hL : curve_jump_measure g false `]a,b]< +oo.
  exact: le_lt_trans (lee_paddl hR0 (lexx _)) hfin.
have hrf x : (a<=x<b)%R -> curve_right_jump_size g x \is a fin_num.
  move=> hx; rewrite fin_numElt (lt_le_trans (ltNyr 0) (curve_one_sided_jump_nonnegative g true x)) /=.
  apply: le_lt_trans _ hR; rewrite curve_jump_measure_sum.
  exact: (@nonnegative_sum_term R [the choiceType of real_line_metric R]
    `[a,b[ (curve_one_sided_jump g true) x hx).
have hlf x : (a<x<=b)%R -> curve_left_jump_size g x \is a fin_num.
  move=> hx; rewrite fin_numElt (lt_le_trans (ltNyr 0) (curve_one_sided_jump_nonnegative g false x)) /=.
  apply: le_lt_trans _ hL; rewrite curve_jump_measure_sum.
  exact: (@nonnegative_sum_term R [the choiceType of real_line_metric R]
    `]a,b] (curve_one_sided_jump g false) x hx).
pose r x := fine (curve_right_jump_size g x).
pose l x := fine (curve_left_jump_size g x).
have hr0 x : (a<=x<b)%R -> (0<=r x)%R.
  move=> hx; have hh : 0<=curve_right_jump_size g x := curve_one_sided_jump_nonnegative g true x.
  by rewrite -(fineK (hrf x hx)) lee_fin in hh.
have hl0 x : (a<x<=b)%R -> (0<=l x)%R.
  move=> hx; have hh : 0<=curve_left_jump_size g x := curve_one_sided_jump_nonnegative g false x.
  by rewrite -(fineK (hlf x hx)) lee_fin in hh.
have hr x : (a<=x<b)%R -> curve_right_jump_size g x<=(r x)%:E.
  by move=> hx; rewrite /r (fineK (hrf x hx)).
have hl x : (a<x<=b)%R -> curve_left_jump_size g x<=(l x)%:E.
  by move=> hx; rewrite /l (fineK (hlf x hx)).
have heR : nonnegative_sum (`[a,b[ : set (real_line_metric R)) (fun x => (r x)%:E)=
    curve_jump_measure g true `[a,b[.
  rewrite curve_jump_measure_sum; apply: nonnegative_sum_ext=> x hx.
  exact: fineK (hrf x hx).
have heL : nonnegative_sum (`]a,b] : set (real_line_metric R)) (fun x => (l x)%:E)=
    curve_jump_measure g false `]a,b].
  rewrite curve_jump_measure_sum; apply: nonnegative_sum_ext=> x hx.
  exact: fineK (hlf x hx).
have hh := @curve_endpoint_real_jump_budget_bound R Y g r l a b hab hr0 hl0 hr hl
  (eq_ind_r (fun z => z< +oo) hR heR) (eq_ind_r (fun z => z< +oo) hL heL).
by rewrite heR heL -addeA in hh.
Qed.
