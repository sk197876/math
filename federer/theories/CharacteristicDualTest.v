(** Federer (1969), 2.4.16, p. 90: normalized signed characteristic tests on
    A1 inside {|f|>t}. This is the individual term used before imposing the
    full-sign condition by a positive mixture with a full-support test. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialNormPower PartialScalarProduct RealPower ExtendedPositivePower MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasurableFunctionUP MeasurableNormedCharacteristic MeasurableTotalNormedArithmetic
  CharacteristicFunctionUP MeasureFiniteCharacteristicIntegral DensityCharacteristicIntegral
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralComparison MeasureNonnegativeIntegral
  MeasureLpNorm MeasureRealLpMembership MeasureDualTestUP TotalScalarArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [characteristic_dual_test]: the normalized signed
    characteristic function mu(A1)^(-1) a1 sign(f) in Federer
    2.4.16, p. 90. The positive finite measure is supplied as b. *)
Definition characteristic_dual_test (R : realType) (X : Type) (b : R)
    (s : X -> R) (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) x :
    real_norm_metric_space (scalar_absolute_value_norm R) := (b^-1*s x*Num.sg (f x))%R.

(** Source for [characteristic_dual_test_bounds]: supporting
    pointwise identities for the normalized test in Federer 2.4.16,
    p. 90. The threshold t is positive. *)
Lemma characteristic_dual_test_bounds (R : realType) (X : choiceType)
    (A : set X) (s : X -> R) (b t : R)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_characteristic_function A s -> (0 < b)%R -> (0 < t)%R ->
  (forall x, A x -> (t < `|f x|)%R) -> forall x,
  (`|characteristic_dual_test b s f x| = b^-1*s x)%R /\
  (characteristic_dual_test b s f x = `|characteristic_dual_test b s f x|*Num.sg (f x))%R /\
  (0 <= f x*characteristic_dual_test b s f x)%R /\
  (t*b^-1*s x <= f x*characteristic_dual_test b s f x)%R.
Proof.
move=> hs hb ht hf x; have hbi : (0 < b^-1)%R by rewrite invr_gt0.
have [hx|hx] := pselect (A x).
- have hfx := hf x hx.
  have hfn : f x != 0%R by rewrite -normr_gt0; exact: lt_trans ht hfx.
  have he : (f x*characteristic_dual_test b s f x = b^-1*`|f x|)%R.
    by rewrite /characteristic_dual_test (characteristic_on_set hs hx) mulr1 mulrCA
      [(f x*Num.sg (f x))%R]mulrC -normrEsg.
  have ha : (`|characteristic_dual_test b s f x| = b^-1*s x)%R.
    by rewrite /characteristic_dual_test (characteristic_on_set hs hx) mulr1 normrM
      (ger0_norm (ltW hbi)) normr_sg hfn mulr1.
  split=> //; split; first by rewrite ha.
  split; first by rewrite he mulr_ge0 ?normr_ge0 //; exact: ltW hbi.
  rewrite he (characteristic_on_set hs hx) mulr1 [(t*b^-1)%R]mulrC.
  by rewrite ler_pM2l //; exact: ltW hfx.
- rewrite /characteristic_dual_test (characteristic_off_set hs hx) !mulr0 mul0r normr0 mul0r !mulr0.
  by split=> //; split=> //; split.
Qed.

(** Source for [characteristic_dual_test_admissible]: the unit L1
    norm of the normalized first term in Federer 2.4.16, p. 90,
    and its lower integral bound by t. The resulting product integral
    is allowed to be infinite, as required when phi_infinity(f)=infinity. *)
Theorem characteristic_dual_test_admissible (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (A : set X) (s : X -> R) (b t : R)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_characteristic_function A s -> measure_measurable mu A -> mu A=b%:E ->
  (0 < b)%R -> (0 < t)%R ->
  is_measure_measurable_function mu (partial_function_total f) ->
  (forall x, A x -> (t < `|f x|)%R) ->
  is_finite_lp_unit_test mu 1%R (partial_function_total (characteristic_dual_test b s f)) /\
  exists z, is_measure_integral mu (partial_scalar_product (partial_function_total f)
    (partial_function_total (characteristic_dual_test b s f))) z /\ t%:E <= z.
Proof.
move=> hs hA hAb hb ht hf hAf.
pose u := characteristic_dual_test b s f.
have hupt := @characteristic_dual_test_bounds R X A s b t f hs hb ht hAf.
have hbi : (0 < b^-1)%R by rewrite invr_gt0.
have hbne : b != 0%R by rewrite gt_eqF.
have hsm := @measurable_normed_characteristic R X mu hm A s hs hA.
have hsc := @measurable_normed_total_scale R X R^o _ (scalar_absolute_value_norm R) mu hm b^-1 s hsm.
have hum := @measurable_total_scalar_product R X mu hm
  (fun x => ((b^-1*s x)%R : real_norm_metric_space (scalar_absolute_value_norm R)))
  (fun x => (Num.sg (f x) : real_norm_metric_space (scalar_absolute_value_norm R)))
  hsc.1 (@measurable_total_scalar_sign R X mu hm f hf).
have hci := @measure_positive_characteristic_integral R X mu hm A s b^-1 hs hA hbi.
have hct := measure_integral_graph_equivalent (real_total_embedding_graph _) hci.
rewrite hAb -EFinM mulVf // in hct.
have hpow : is_measure_integral mu (partial_norm_power (fun y : R => `|y|%R) 1%R (partial_function_total u)) 1.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hct)=> x z; split.
  - move=> hz; exists (u x); split=> //.
    by rewrite real_power_one_exponent ?normr_ge0 // (hupt x).1.
  - move=> [y [<- hy]]; move: hy.
    by rewrite real_power_one_exponent ?normr_ge0 // (hupt x).1.
have hn : measure_lp_norm mu (fun y : R => `|y|%R) 1%R (partial_function_total u)= 1.
  rewrite (@measure_lp_norm_of_integral R X R^o _ (scalar_absolute_value_norm R)
    mu 1%R (partial_function_total u) 1 hm (lexx _) hum hpow).
  by rewrite invr1 /extended_positive_power real_power_one_base.
split.
- split; last by rewrite hn.
  exact: (@measurable_real_finite_norm_lp R X mu hm 1%R 1%R _ (lexx _) hum hn).
have hpm := @measurable_scalar_product R X mu hm _ _ hf hum.
have hpa : measure_almost_everywhere mu (partial_extended_nonnegative_locus
    (partial_scalar_product (partial_function_total f) (partial_function_total u))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists (f x*u x)%:E; split; last by rewrite lee_fin; exact (hupt x).2.2.1.
  apply/partial_scalar_product_graph; exists (f x),(u x); by split=> //; split.
have [z hzi] := @nonnegative_measurable_function_integrable R X mu hm _ hpm hpa.
exists z; split=> //.
have htb : (0 < t*b^-1)%R by rewrite mulr_gt0.
have hti := @measure_positive_characteristic_integral R X mu hm A s (t*b^-1)%R hs hA htb.
have htt := measure_integral_graph_equivalent (real_total_embedding_graph _) hti.
rewrite hAb -EFinM -mulrA mulVf // mulr1 in htt.
apply: (@measure_integral_monotone R X mu hm _ _ _ _ htt hzi).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
move=> x _; exists ((t*b^-1*s x)%R)%:E,((f x*u x)%R)%:E; split=> //; split.
- apply/partial_scalar_product_graph; exists (f x),(u x); by split=> //; split.
- by rewrite lee_fin; exact (hupt x).2.2.2.
Qed.
