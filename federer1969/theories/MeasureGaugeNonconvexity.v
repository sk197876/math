(** Federer (1969), 2.3.8, pp. 78–79: gauge balls need not be convex. This
    local example uses two atoms of mass one, functions with values (4,0)
    and (0,4), and their midpoint (2,2). *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic CountingMeasure
  FiniteCountingFunctionExamples MeasurableNormedFunctionUP MeasureGauge
  MeasureGaugeCharacteristic MeasureGaugeConstant MeasureGaugeBall InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [boolean_spike_function]: local two-atom witness
    for the nonconvexity assertion in Federer 2.3.8,
    pp. 78–79; value four on the chosen atom and zero on the other. *)
Definition boolean_spike_function (R : realType) (a b : bool) : R :=
  if b == a then 4%R else 0%R.

(** Source for [boolean_spike_gauge]: each of the two spikes
    has gauge one, by the characteristic formula of Federer
    2.3.8, p. 78, and counting measure in 2.1.2,
    p. 54. This is a supporting local calculation. *)
Lemma boolean_spike_gauge (R : realType) a :
  measure_gauge (@counting_measure R bool) (fun y : R => `|y|%R)
    (partial_function_total (@boolean_spike_function R a)) = 1.
Proof.
have he := @measure_gauge_two_value_norm R bool R _ (counting_measure_is_measure R bool)
  (fun y : R => `|y|%R) (@boolean_spike_function R a) [set a] 4%R.
have hon b : [set a] b -> `|boolean_spike_function R a b|%R = 4%R.
  by move=> ->; rewrite /boolean_spike_function eqxx normr_nat.
have hoff b : ~ [set a] b -> `|boolean_spike_function R a b|%R = 0%R.
  move=> hb; have hba : b != a by apply/eqP=> heq; apply: hb; exact heq.
  by rewrite /boolean_spike_function (negbTE hba) normr0.
by rewrite (he (ler0n R 4) hon hoff) counting_singleton_value min_r // lee_fin ler1n.
Qed.

(** Source for [boolean_spike_midpoint]: local calculation
    supporting Federer 2.3.8, pp. 78–79: the midpoint
    of the two spikes is the constant two. *)
Lemma boolean_spike_midpoint (R : realType) b :
  ((2%R : R)^-1 * (boolean_spike_function R true b + boolean_spike_function R false b))%R = 2%R.
Proof.
have h2 : ((2%R : R) != 0)%R by rewrite pnatr_eq0.
have he : (4%R : R) = (2*2)%R by rewrite -natrM.
by case: b; rewrite /boolean_spike_function /= ?addr0 ?add0r he mulrA mulVf // mul1r.
Qed.

(** Source for [measure_gauge_ball_not_convex]: concrete witness
    to the nonconvexity assertion of Federer 2.3.8,
    pp. 78–79. All functions have total domains, so this
    failure is independent of the partial-domain correction. *)
Theorem measure_gauge_ball_not_convex (R : realType) :
  ~ is_inner_convex (@total_measure_gauge_ball R bool R^o _
    (scalar_absolute_value_norm R) (@counting_measure R bool) 1%R).
Proof.
move=> hc.
pose M := real_norm_metric_space (scalar_absolute_value_norm R).
pose F := GRing.Lmodule.clone R (bool -> M) _.
pose f : F := @boolean_spike_function R true.
pose g : F := @boolean_spike_function R false.
have hf : @total_measure_gauge_ball R bool R^o _ (scalar_absolute_value_norm R) (@counting_measure R bool) 1%R f.
  split; first exact (@finite_source_normed_counting_function R bool R^o _ (scalar_absolute_value_norm R) f).
  by rewrite /f boolean_spike_gauge.
have hg : @total_measure_gauge_ball R bool R^o _ (scalar_absolute_value_norm R) (@counting_measure R bool) 1%R g.
  split; first exact (@finite_source_normed_counting_function R bool R^o _ (scalar_absolute_value_norm R) g).
  by rewrite /g boolean_spike_gauge.
have hh := @inner_convex_midpoint R F _ hc f g hf hg.
have he : ((2%R : R)^-1 *: (f+g))%R = (fun _ : bool => (2%R : M)).
  apply: funext=> b; exact: boolean_spike_midpoint.
rewrite he in hh; have hb := hh.2.
rewrite (@measure_gauge_total_constant R bool R _ (counting_measure_is_measure R bool))
  ?normr_ge0 // normr_nat counting_boolean_whole_value minxx lee_fin in hb.
have ht : (1 < 2 :> R)%R by rewrite ltr1n.
have := lt_le_trans ht hb; by rewrite ltxx.
Qed.
