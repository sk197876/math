(** Federer (1969), 2.4.16, p. 90: concentrating the first positive
    coefficient while retaining positive weights on the whole nonzero locus.
    Binary convex mixtures package this step using the proved Minkowski
    inequality and homogeneity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureLpNorm MeasureLpNormTotal MeasureLpMembershipUP MeasureRealLpMembership
  MeasurableTotalNormedArithmetic MeasureDualTestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dual_test_mixture]: the first-term coefficient
    1-delta and remaining positive weight delta used in Federer
    2.4.16, p. 90. *)
Definition dual_test_mixture (R : realType) (X : Type) (d : R)
    (u v : X -> real_norm_metric_space (scalar_absolute_value_norm R)) x :
    real_norm_metric_space (scalar_absolute_value_norm R) := ((1-d)*u x+d*v x)%R.

(** Source for [dual_test_mixture_unit]: supporting unit-ball
    closure for the weighted tests of Federer 2.4.16, p. 90,
    by 2.4.15 and the seminorm laws of 2.4.12. *)
Lemma dual_test_mixture_unit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (q d : R)
    (u v : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  (0 <= d)%R -> (d <= 1)%R ->
  is_finite_lp_unit_test mu q (partial_function_total u) ->
  is_finite_lp_unit_test mu q (partial_function_total v) ->
  is_finite_lp_unit_test mu q (partial_function_total (dual_test_mixture d u v)).
Proof.
move=> hd hd1 [hu hun] [hv hvn].
have h1d : (0 <= 1-d)%R by rewrite subr_ge0.
have hus := @measurable_normed_total_scale R X R^o _ (scalar_absolute_value_norm R)
  mu hm (1-d)%R u hu.2.1.
have hvs := @measurable_normed_total_scale R X R^o _ (scalar_absolute_value_norm R)
  mu hm d v hv.2.1.
have hsum := @measurable_normed_total_add R X R^o _ (scalar_absolute_value_norm R)
  mu hm _ _ hus hvs.
have hn := @total_lp_norm_triangle R X R^o _ (scalar_absolute_value_norm R)
  mu hm q hu.1 _ _ hus hvs.
rewrite (@total_lp_norm_scale R X R^o _ (scalar_absolute_value_norm R) mu hm q hu.1
  (1-d)%R u hu.2.1) (@total_lp_norm_scale R X R^o _ (scalar_absolute_value_norm R)
  mu hm q hu.1 d v hv.2.1) (ger0_norm h1d) (ger0_norm hd) in hn.
have h1de : 0 <= ((1-d)%R)%:E by rewrite lee_fin.
have hde : 0 <= (d%:E : \bar R) by rewrite lee_fin.
have hb := leeD (lee_wpmul2l h1de hun) (lee_wpmul2l hde hvn).
rewrite !mule1 -EFinD subrK in hb.
have hnorm : measure_lp_norm mu (fun y : R => `|y|%R) q
    (partial_function_total (dual_test_mixture d u v)) <= 1 := le_trans hn hb.
have hnon := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R)
  mu q _ hm hu.1 hsum.1.
have hfin : measure_lp_norm mu (fun y : R => `|y|%R) q
    (partial_function_total (dual_test_mixture d u v)) \is a fin_num.
  rewrite (ge0_fin_numE hnon); exact: le_lt_trans hnorm (ltry _).
split=> //; apply: (@measurable_real_finite_norm_lp R X mu hm q
  (fine (measure_lp_norm mu (fun y : R => `|y|%R) q
    (partial_function_total (dual_test_mixture d u v)))) _ hu.1 hsum.1).
by rewrite fineK.
Qed.
