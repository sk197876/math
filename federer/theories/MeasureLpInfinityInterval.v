(** Federer (1969), 2.4.17, p. 90: interval property of the finite-norm
    exponents when the upper endpoint is infinity. The supporting bound
    |f|^p<=b^(p-s)|f|^s uses a finite positive essential bound b. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower RealPowerSuccessor
  MeasurableNormPower MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralComparison MeasureIntegralScaleLaw MeasureUpperIntegralScale
  MeasureNonnegativeIntegral MeasureLpNorm MeasureLpNormFiniteness MeasureLpPowerIntegral
  MeasureEssentialNorm MeasureEssentialNormAttainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_infinity_exponent_interval]: supporting
    infinity-endpoint interval property in Federer 2.4.17, p. 90.
    One finite Ls norm and a finite essential norm imply every
    higher finite Lp norm is finite. *)
Lemma measure_lp_infinity_exponent_interval (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (s p : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= s)%R -> (s <= p)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu N s f < +oo -> measure_essential_norm mu N f < +oo ->
  measure_lp_norm mu N p f < +oo.
Proof.
move=> hs hsp hf hsf hef; have [hps|hps] := eqVneq p s; first by rewrite hps.
have hp : (1 <= p)%R := le_trans hs hsp.
have hs0 : (0 < s)%R := lt_le_trans ltr01 hs.
have hp0 : (0 < p)%R := lt_le_trans hs0 hsp.
have hdp : (0 < p-s)%R by rewrite subr_gt0 lt_neqAle eq_sym hps hsp.
have he0 := measure_essential_norm_nonnegative mu N f.
have hefin : measure_essential_norm mu N f \is a fin_num by rewrite (ge0_fin_numE he0).
pose a := fine (measure_essential_norm mu N f).
have hea : measure_essential_norm mu N f=a%:E by rewrite /a fineK.
have ha0 : (0 <= a)%R by move: he0; rewrite hea lee_fin.
pose b := (1+a)%R.
have hb : (0 < b)%R := ltr_pwDl ltr01 ha0.
have hab : (a <= b)%R by rewrite /b lerDr ler01.
pose c := real_power b (p-s)%R.
have hc : (0 < c)%R := @real_power_strictly_positive R b (p-s)%R hb.
have hsn := @measure_lp_norm_nonnegative R X V N hN mu s f hm hs hf.
have hsfin : measure_lp_norm mu N s f \is a fin_num by rewrite (ge0_fin_numE hsn).
pose d := fine (measure_lp_norm mu N s f).
have hsd : measure_lp_norm mu N s f=d%:E by rewrite /d fineK.
have hsi := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm s d f hs hf hsd.
have hscale := @measure_integral_positive_scale R X mu hm c _ _ hc hsi.
rewrite -EFinM in hscale.
have hpm := @measurable_norm_positive_power R X V N hN mu hm p f hp0 hf.
have hpn := @partial_norm_power_almost_nonnegative R X _ mu hm N p f (measurable_function_domain hf).
have hpi := (@nonnegative_measurable_function_integral R X mu hm _ hpm hpn).1.
have hbound : measure_lower_integral mu (partial_norm_power N p f) <= (c * real_power d s)%:E.
  apply: (@measure_integral_monotone R X mu hm _ _ _ _ hpi hscale).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_essential_norm_almost_bound R X _ mu hm N f (measurable_function_domain hf))).
  move=> x [y [hy hya]].
  have hyaR : (N y <= a)%R by move: hya; rewrite hea lee_fin.
  have hyb : (N y <= b)%R := le_trans hyaR hab.
  exists (real_power (N y) p)%:E,(c * real_power (N y) s)%:E; split.
  - exists y; by split.
  split.
  - exists (real_power (N y) s)%:E; split; last exact: EFinM.
    exists y; by split.
  - rewrite lee_fin.
    have [hy0|hy0] := eqVneq (N y) 0%R.
    + by rewrite hy0 !real_power_zero_base ?gt_eqF // mulr0.
    have hyn : (0 < N y)%R by rewrite lt_neqAle eq_sym hy0 (real_seminorm_nonnegative hN.1 y).
    have he : p=((p-s)+s)%R by rewrite subrK.
    rewrite {1}he (@real_power_add_exponents_positive R (N y) (p-s)%R s hyn).
    have hpow := @real_power_monotone R (N y) b (p-s)%R (real_seminorm_nonnegative hN.1 y) hyb hdp.
    exact: (ler_wpM2r (real_power_nonnegative (N y) s) hpow).
rewrite (@measure_lp_norm_finite_iff R X V N hN mu p f hm hp hf).
exact: le_lt_trans hbound (ltry _).
Qed.
