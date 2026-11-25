(** Federer (1969), 2.3.8, pp. 78–79: supporting order properties of the
    gauge and its zero locus. Source context: MeasureGauge.v. These facts
    isolate the measure-level argument from the later almost-equality
    interpretation for normed maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic
  MeasureGauge MeasureGaugeAttainment ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_gauge_superlevel_comparison]: supporting
    monotonicity of the infimum in Federer 2.3.8, p. 78;
    smaller superlevel measures imply a smaller gauge. *)
Lemma measure_gauge_superlevel_comparison (R : realType) (X : choiceType)
    (Y Z : Type) (mu : set X -> \bar R) (N : Y -> R) (M : Z -> R)
    (f : partial_function X Y) (g : partial_function X Z) :
  (forall r, mu (partial_norm_superlevel N f r) <= mu (partial_norm_superlevel M g r)) ->
  measure_gauge mu N f <= measure_gauge mu M g.
Proof.
move=> h; apply: extended_real_inf_greatest=> r [hr hg].
apply: measure_gauge_bound; split=> //; exact: le_trans (h r) hg.
Qed.

(** Source for [measure_gauge_superlevel_invariance]: supporting
    equality principle for the pseudodistance of Federer 2.3.8,
    p. 78: equal superlevel measures give equal gauges. *)
Lemma measure_gauge_superlevel_invariance (R : realType) (X : choiceType)
    (Y Z : Type) (mu : set X -> \bar R) (N : Y -> R) (M : Z -> R)
    (f : partial_function X Y) (g : partial_function X Z) :
  (forall r, mu (partial_norm_superlevel N f r) = mu (partial_norm_superlevel M g r)) ->
  measure_gauge mu N f = measure_gauge mu M g.
Proof.
move=> h; apply/eqP; rewrite eq_le; apply/andP; split;
  apply: measure_gauge_superlevel_comparison=> r; by rewrite h.
Qed.

(** Source for [measure_gauge_zero_of_null_superlevel]: one half
    of the zero-distance criterion in Federer 2.3.8, p. 78;
    the positive norm locus being null makes zero feasible. *)
Lemma measure_gauge_zero_of_null_superlevel (R : realType) (X : choiceType)
    (Y : Type) (mu : set X -> \bar R) (N : Y -> R)
    (f : partial_function X Y) :
  mu (partial_norm_superlevel N f 0) = 0 -> measure_gauge mu N f = 0.
Proof.
move=> h; apply/eqP; rewrite eq_le measure_gauge_nonnegative andbT.
apply: measure_gauge_bound; split; by rewrite ?h.
Qed.

(** Source for [measure_gauge_zero_iff]: gauge form of the zero- distance
    criterion of Federer 2.3.8, p. 78 *)
Lemma measure_gauge_zero_iff (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f : partial_function X Y) :
  (forall t : R, measure_measurable mu (partial_norm_superlevel N f t%:E)) ->
  (measure_gauge mu N f = 0 <-> mu (partial_norm_superlevel N f 0) = 0).
Proof.
move=> hme; split; last exact: measure_gauge_zero_of_null_superlevel.
move=> hz; have h := (@measure_gauge_attained R X Y mu hm N f hme).2.
rewrite hz in h; apply/eqP; by rewrite eq_le h measure_nonnegative.
Qed.

(** Source for [measure_gauge_support_bound]: supporting bound
    used in Federer 2.3.8, p. 79, convex-hull paragraph:
    the gauge does not exceed the measure of the nonzero-norm
    locus. No finiteness or measurability premise is needed. *)
Lemma measure_gauge_support_bound (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f : partial_function X Y) :
  measure_gauge mu N f <= mu (partial_norm_superlevel N f 0).
Proof.
apply: measure_gauge_bound; split; first exact: measure_nonnegative.
apply: (@measure_mono R X mu hm).
apply: partial_norm_superlevel_antitone; exact: measure_nonnegative.
Qed.

(** Source for [measure_gauge_uniform_norm_bound]: supporting
    gauge estimate for uniform approximation in Federer 2.3.8,
    p. 78: a pointwise norm bound also bounds the gauge. *)
Lemma measure_gauge_uniform_norm_bound (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f : partial_function X Y) (c : R) : (0 <= c)%R ->
  (forall x y, partial_function_graph f x y -> (N y <= c)%R) ->
  measure_gauge mu N f <= c%:E.
Proof.
move=> hc hb; apply: measure_gauge_bound; split; first exact hc.
have he : partial_norm_superlevel N f c%:E = set0.
  apply/seteqP; split; last by move=> x [].
  move=> x [y [hy hh]]; have hh' : (c < N y)%R := hh.
  by move: hh'; rewrite ltNge (hb x y hy).
by rewrite he (measure_empty hm).
Qed.
