(** Federer (1969), 2.4.19, p. 91: bounded C-valued approximants belong to
    L1 when the source measure is finite. This supporting consequence uses
    the scalar domination theorem 2.4.4(8), p. 82, and the norm definition
    2.4.12, p. 86. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialNormPower PartialAbsolutePartsGraph PartialExtendedOrderLoci RealPower ExtendedPositivePower
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableNormedFunctionUP MeasurableNormPower
  MeasureIntegralUP MeasureStepConstants MeasureStepIntegralIdentification MeasureIntegralGraphEquivalence
  MeasureAbsoluteSummability MeasureNonnegativeLowerIntegral MeasureIntegralBounds MeasureIntegralUniqueness MeasurableFunctionUP MeasureLpNorm MeasureLpMembershipUP MeasureLpCountableMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_constant_integral]: supporting integrable
    constant majorant in the bounded case of Federer 2.4.19, p. 91 *)
Lemma finite_measure_constant_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (m c : R) :
  mu setT=m%:E -> is_measure_integral mu
    (partial_function_total (fun _ : X => (c%:E : extended_real_line R))) (c * m)%R%:E.
Proof.
move=> hmass.
have hi := @measure_step_function_integral R X mu hm _ _
  (@measure_step_constant R X mu hm c) (@measure_step_constant_integral R X mu hm c).
rewrite hmass -EFinM in hi.
apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x z; split.
- by move=> [a [<- he]].
- move=> hz; exists c; by split.
Qed.

(** Source for [finite_measure_bounded_norm_lp_one]: supporting L1
    membership of bounded approximants in Federer 2.4.19, p. 91 Bounds and
    partial domains are interpreted almost everywhere. *)
Lemma finite_measure_bounded_norm_lp_one (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (m M : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  mu setT=m%:E -> is_measurable_normed_function mu f ->
  measure_almost_everywhere mu (partial_function_preimage f [set y | (N y <= M)%R]) ->
  is_measure_lp_function mu 1%R f.
Proof.
move=> hmass hf hbound.
have hsum : is_measure_summable mu (partial_function_total (fun _ : X => (M%:E : extended_real_line R))).
  exists (M * m)%R; exact: (@finite_measure_constant_integral R X mu hm m M hmass).
have hp := @measurable_norm_positive_power R X V N hN mu hm 1%R f ltr01 hf.1.
have hd : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (partial_norm_power N 1%R f))
    (partial_function_total (fun _ : X => (M%:E : extended_real_line R)))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hbound)=> x [y [hy hb]].
  exists (N y)%:E,M%:E; split.
  - exists (N y)%:E; split.
    + exists y; split=> //; by rewrite real_power_one_exponent //; exact: real_seminorm_nonnegative hN.1 _.
    + by rewrite abse_EFin (ger0_norm (real_seminorm_nonnegative hN.1 y)).
  - split=> //; by rewrite lee_fin.
have [a ha] := (@measure_dominated_summable R X mu hm _ _ hp hsum hd).1.
have ha0 : 0 <= a%:E.
  have hnon := @partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN)
    mu hm N 1%R f (measurable_function_domain hf.1).
  have hh := @measure_lower_integral_nonnegative R X mu hm _ hnon.
  have he := measure_lower_integral_unique (measure_lower_integral_specification mu _) ha.2.2.
  by rewrite he in hh.
have hnorm := @measure_lp_norm_of_integral R X V N hN mu 1%R f a%:E hm (lexx _) hf.1 ha.
rewrite invr1 extended_positive_power_one // in hnorm.
have hfinite : measure_lp_norm mu N 1%R f < +oo by rewrite hnorm ltry.
split; first exact: lexx.
split=> //; split=> //.
exact: (@finite_lp_norm_countably_measurable R X V N hN mu hm 1%R f (lexx _) hf.1 hfinite).
Qed.
