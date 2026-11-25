(** Federer (1969), 2.4.12, pp. 86–87: the essential bound used for
    phi_(infinity). No measurability of individual superlevels is necessary,
    since a countable union of null sets is null. Source context and
    threshold convention: MeasureEssentialNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureGauge MeasureGaugeAttainment MeasureEssentialNormUP MeasureEssentialNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_essential_norm_attained]: essential upper bound
    underlying Federer 2.4.12, pp. 86–87 It holds for arbitrary partial
    functions, with the bound applying on their domains. *)
Theorem measure_essential_norm_attained (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R) (f : partial_function X Y) :
  measure_essential_norm_feasible mu N f (measure_essential_norm mu N f).
Proof.
split; first exact: measure_essential_norm_nonnegative.
case he: (measure_essential_norm mu N f)=> [r| |].
- rewrite partial_norm_superlevel_approximation.
  apply: (@measure_null_countable_union R X [the choiceType of (nat : Type)] mu hm setT
    (fun n => partial_norm_superlevel N f (gauge_approximation_threshold r n)%:E) (countableP setT)).
  move=> n _; have ht : measure_essential_norm mu N f < (gauge_approximation_threshold r n)%:E.
    rewrite he lte_fin; exact: gauge_approximation_threshold_strict.
  exact: (@measure_essential_norm_strict_upper_feasible R X Y mu hm N f _ ht).2.
- have hempty : partial_norm_superlevel N f +oo=set0.
    apply/seteqP; split=> x; last by move=> [].
    by move=> [y [_ hy]].
  by rewrite hempty (measure_empty hm).
- have h := measure_essential_norm_nonnegative mu N f; by rewrite he in h.
Qed.

(** Source for [measure_essential_norm_almost_bound]: the almost-everywhere
    bound |f|<=phi_(infinity)(f) supporting Federer 2.4.12, pp. 86–87 A
    conull original domain is explicit. *)
Lemma measure_essential_norm_almost_bound (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R) (f : partial_function X Y) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu [set x | exists y,
    partial_function_graph f x y /\ (N y)%:E <= measure_essential_norm mu N f].
Proof.
move=> hd; pose B := partial_norm_superlevel N f (measure_essential_norm mu N f).
have hB : measure_almost_everywhere mu (~` B).
  rewrite /measure_almost_everywhere setCK; exact: (measure_essential_norm_attained hm N f).2.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hd hB)).
move=> x [[y hy] hx]; exists y; split=> //.
rewrite leNgt; apply/negP=> hn; apply: hx; exists y; by split.
Qed.

(** Source for [null_measure_essential_norm_zero]: boundary
    clarification of Federer 2.4.12, p. 86, defining
    display. The nonnegative-threshold convention gives zero,
    as a seminorm must, for every function under the null measure. *)
Lemma null_measure_essential_norm_zero (R : realType) (X : choiceType) (Y : Type)
    (N : Y -> R) (f : partial_function X Y) :
  measure_essential_norm (fun _ : set X => (0 : \bar R)) N f = 0.
Proof.
apply/eqP; rewrite eq_le measure_essential_norm_nonnegative andbT.
apply: measure_essential_norm_bound; by split.
Qed.
