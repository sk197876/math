(** Supporting interval locality in Federer (1969), 2.10.14, p. 177. The
    segment retraction changes neither inward jump on [a,b] and makes all
    other jumps zero. It is a proof representative for the unrestricted
    given map, not an extra hypothesis on its values outside the segment. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveOneSidedJumpUP CurveJumpBudget
  CurveJumpLocalization StieltjesSubstitution NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_interval_jump_budget_retracted]: supporting
    invariance of the exact two jump ranges in 2.10.14, p. 177,
    including arbitrary and infinite jump sizes. *)
Lemma curve_interval_jump_budget_retracted (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : (a<=b)%R ->
  curve_interval_jump_budget (g \o @segment_retraction R a b) a b=
    curve_interval_jump_budget g a b.
Proof.
move=> hab; rewrite /curve_interval_jump_budget !curve_jump_measure_sum.
congr (_+_); apply: nonnegative_sum_ext=> x hx.
- change (curve_right_jump_size (g \o @segment_retraction R a b) x=curve_right_jump_size g x).
  have hx' : (a<=x<b)%R := hx.
  by rewrite (@curve_right_jump_retracted R Y g a b x hab) hx'.
- change (curve_left_jump_size (g \o @segment_retraction R a b) x=curve_left_jump_size g x).
  have hx' : (a<x<=b)%R := hx.
  by rewrite (@curve_left_jump_retracted R Y g a b x hab) hx'.
Qed.

(** Source for [curve_interval_jump_budget_retracted_global]:
    supporting conversion of the two sums in 2.10.14, p. 177,
    to global atomic budgets of the representative. *)
Lemma curve_interval_jump_budget_retracted_global (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : (a<=b)%R ->
  curve_jump_measure (g \o @segment_retraction R a b) true setT+
    curve_jump_measure (g \o @segment_retraction R a b) false setT=
    curve_interval_jump_budget g a b.
Proof.
move=> hab; by rewrite (@curve_right_jump_global_retraction R Y g a b hab)
  (@curve_left_jump_global_retraction R Y g a b hab).
Qed.
